// Copyright Amazon.com, Inc. or its affiliates.

//! The environment APIs for macros.
//!
//! These are the *"aggregate"* types to represent things like the type environment for a macro
//! or the macro environment for E-expressions.  As such, these container types are generally
//! generic to support static typing cases (i.e., semantic analysis of the macro), but also
//! run-time use cases where the environment points to the actual instance of the macro.
//!
//! The preference *within* macro definitions are to generally replace all macro invocations
//! with direct pointers (or offset indirections) to the compiled macro.  However, with
//! E-Expressions we may have to interpret a macro invocation on the fly from its textual name
//! (i.e., text), so these generic representations help in that context.
//!
//! These data types are implemented as [*persistent data structures*][1], so we can incrementally
//! build up the environments/modules/tables and have immutable views at each step and
//! retain/close over those environments for each macro definition.
//!
//! [1]: https://en.wikipedia.org/wiki/Persistent_data_structure

use crate::macros::ident::{Addressable, MacroBind, MacroId, ModuleId, Name};
use crate::result::illegal_operation;
use crate::IonResult;
use rpds::{HashTrieMap, Vector};
use std::fmt::Debug;
use std::rc::Rc;

/// Marker trait for things that can be macro values within environments/tables/modules.
pub trait MacroVal: Debug {}

/// Represents some resolved handle to a macro definition.
///
/// This handle is either a bind into some context (a macro table/module), or an alias to
/// something that itself isn't bound (e.g., a macro alias).
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum MacroHandle {
    /// A direct binding for some addressable macro
    /// (which itself may be aliased to some definition).
    Bind(MacroBind),

    /// An alias to some addressable macro binding
    /// (which itself may be aliased to some definition).
    Alias(MacroBind, Name),
}

/// A macro value associated to some handle.
///
/// This is a reference counted data structure and can be cloned relatively cheaply.
#[derive(Debug)]
pub struct MacroHandleVal<M: MacroVal> {
    handle: Rc<MacroHandle>,
    value: Rc<M>,
}

impl<M: MacroVal> MacroHandleVal<M> {
    /// Constructs a new handle.
    pub fn new(handle: MacroHandle, value: M) -> Self {
        Self {
            handle: Rc::new(handle),
            value: Rc::new(value),
        }
    }

    /// Reference to the underlying handle for this macro value.
    pub fn handle(&self) -> &MacroHandle {
        &self.handle
    }

    /// Reference to the underlying value.
    pub fn value(&self) -> &M {
        &self.value
    }
}

impl<M: MacroVal> Clone for MacroHandleVal<M> {
    fn clone(&self) -> Self {
        MacroHandleVal {
            handle: Rc::clone(&self.handle),
            value: Rc::clone(&self.value),
        }
    }
}

/// A mapping of address to macro value.
pub trait MacroByAddress<M: MacroVal> {
    /// Retrieves a macro value by some offset.
    fn macro_by_address(&self, address: usize) -> Option<&MacroHandleVal<M>>;
}

/// A mapping of name to macro value.
pub trait MacroByName<M: MacroVal> {
    fn macro_by_name(&self, name: &Name) -> Option<&IndexEntry<M>>;
}

/// Marker trait indicating that a macro can be looked up by name or address.
pub trait MacroEnv<M: MacroVal>: MacroByAddress<M> + MacroByName<M> {}

impl<M: MacroVal, T: MacroByAddress<M> + MacroByName<M>> MacroEnv<M> for T {}

/// Represents an ordered table of macros defining addresses from a zero-based offset.
#[derive(Debug)]
pub struct MacroTable<M: MacroVal> {
    // XXX currently this is just a persistent Vector, but we could have a variant to Vec
    //     when we "freeze" the module to have O(1) lookup at O(N) one time cost
    //     if we don't do this, access is always O(log N) because we're some kind of trie or
    //     the like under the hood.
    table: Vector<MacroHandleVal<M>>,
}

impl<M: MacroVal> MacroTable<M> {
    /// Constructs the empty macro table.
    pub fn empty() -> Self {
        Self {
            table: Vector::new(),
        }
    }

    /// Creates a table the next macro added to it.
    pub fn with_additional_macro(&self, next_macro: MacroHandleVal<M>) -> Self {
        Self {
            table: self.table.push_back(next_macro),
        }
    }

    /// Returns the count of elements in the table.
    pub fn len(&self) -> usize {
        self.table.len()
    }
}

impl<M: MacroVal> MacroByAddress<M> for MacroTable<M> {
    fn macro_by_address(&self, address: usize) -> Option<&MacroHandleVal<M>> {
        self.table.get(address)
    }
}

impl<M: MacroVal> Clone for MacroTable<M> {
    fn clone(&self) -> Self {
        MacroTable {
            table: self.table.clone(),
        }
    }
}

/// The entry of the name mapping--this tracks non-unique names, the distinct case, and
/// a sentinel indicating lack of an entry.
#[derive(Debug)]
pub enum IndexEntry<M: MacroVal> {
    // TODO consider if we really want to track all the conflicts--it is nice for debugging...
    /// Indicates that a name maps to more than one distinct handle.
    Ambiguous(Vector<MacroHandleVal<M>>),

    /// Indicates a unique address in the index corresponding to the name.
    Distinct(MacroHandleVal<M>),
}

impl<M: MacroVal> Clone for IndexEntry<M> {
    fn clone(&self) -> Self {
        match self {
            IndexEntry::Ambiguous(vals) => IndexEntry::Ambiguous(vals.clone()),
            IndexEntry::Distinct(val) => IndexEntry::Distinct(val.clone()),
        }
    }
}

/// Internal address/name mapping.
#[derive(Debug)]
struct MacroIndex<M: MacroVal> {
    table: MacroTable<M>,
    name_index: HashTrieMap<Name, IndexEntry<M>>,
}

impl<M: MacroVal> MacroIndex<M> {
    /// Constructs an empty index.
    fn empty() -> Self {
        Self {
            table: MacroTable::empty(),
            name_index: HashTrieMap::new(),
        }
    }

    /// The number of entries in the underlying table.
    fn len(&self) -> usize {
        self.table.len()
    }

    /// Inserts the macro into the table and the index, returning the entry in the index and
    /// the version of the index containing the added macro.
    ///
    /// A [`MacroHandle::Bind`] will associate with the underlying table ***and*** the name map
    /// if a name is present in the underlying [`MacroBind::name`] exists. In this case,
    /// the handle ***must*** have the address of the end of the table specified or this will
    /// panic.
    ///
    /// A [`MacroHandle::Alias`] will ***only*** associate with the underlying name index.
    fn with_macro(
        &self,
        next_handle: MacroHandle,
        next_macro_val: M,
    ) -> (Option<IndexEntry<M>>, Self) {
        let next_macro = MacroHandleVal::new(next_handle, next_macro_val);

        // insert if appropriate into the macro table
        let next_table = match &next_macro.handle() {
            MacroHandle::Bind(bind) => {
                // make sure we have a valid address if applicable
                assert_eq!(self.len(), bind.address());
                self.table.with_additional_macro(next_macro.clone())
            }
            MacroHandle::Alias(_, _) => {
                // an alias never gets added to the table
                self.table.clone()
            }
        };

        let potential_name = match next_macro.handle() {
            MacroHandle::Bind(bind) => bind.name(),
            MacroHandle::Alias(_, name) => Some(name),
        };
        // insert into name index
        let mut index_entry_opt = None;
        let next_index = match potential_name {
            // no name to map--same name index.
            None => self.name_index.clone(),
            Some(name) => match self.name_index.get(name) {
                None => {
                    // nothing already is in the index for this name
                    let index_entry = IndexEntry::Distinct(next_macro.clone());
                    index_entry_opt = Some(index_entry.clone());
                    self.name_index.insert(name.clone(), index_entry)
                }
                Some(existing) => match existing {
                    IndexEntry::Ambiguous(others) => {
                        let index_entry =
                            IndexEntry::Ambiguous(others.push_back(next_macro.clone()));
                        index_entry_opt = Some(index_entry.clone());
                        self.name_index.insert(name.clone(), index_entry)
                    }
                    IndexEntry::Distinct(previous) => {
                        let index_entry = IndexEntry::Ambiguous(
                            [previous.clone(), next_macro.clone()].into_iter().collect(),
                        );
                        index_entry_opt = Some(index_entry.clone());
                        self.name_index.insert(name.clone(), index_entry)
                    }
                },
            },
        };

        (
            index_entry_opt,
            Self {
                table: next_table,
                name_index: next_index,
            },
        )
    }
}

impl<M: MacroVal> MacroByAddress<M> for MacroIndex<M> {
    fn macro_by_address(&self, address: usize) -> Option<&MacroHandleVal<M>> {
        self.table.macro_by_address(address)
    }
}

impl<M: MacroVal> MacroByName<M> for MacroIndex<M> {
    fn macro_by_name(&self, name: &Name) -> Option<&IndexEntry<M>> {
        self.name_index.get(name)
    }
}

impl<M: MacroVal> Clone for MacroIndex<M> {
    fn clone(&self) -> Self {
        MacroIndex {
            table: self.table.clone(),
            name_index: self.name_index.clone(),
        }
    }
}

/// Represents the environment for a macro module.
#[derive(Debug)]
pub struct Module<M: MacroVal> {
    id: ModuleId,
    index: MacroIndex<M>,
}

impl<M: MacroVal> Module<M> {
    /// Constructs an empty module for some [`ModuleId`].
    pub fn empty(id: ModuleId) -> Self {
        Self {
            id,
            index: MacroIndex::empty(),
        }
    }

    /// Derives a [`ModuleEnv`] for this module.
    pub fn derive_env(&self) -> ModuleEnv<M> {
        ModuleEnv::empty(self.clone())
    }

    fn with_handle(&self, next_handle: MacroHandle, next_macro_val: M) -> IonResult<Module<M>> {
        let (next_index_entry_opt, next_index) = self.index.with_macro(next_handle, next_macro_val);
        if matches!(&next_index_entry_opt, Some(IndexEntry::Ambiguous(_))) {
            return illegal_operation(format!(
                "Duplicate macro named in module: {:?}",
                next_index_entry_opt
            ));
        }
        Ok(Self {
            id: self.id.clone(),
            index: next_index,
        })
    }

    /// Defines a macro within this module with an optional name returning the new module containing
    /// it.
    ///
    /// Note that such a macro will have a [`MacroId`] that is bound to the identity of
    /// this module.
    pub fn with_defined_macro(
        &self,
        opt_name: Option<Name>,
        next_macro_val: M,
    ) -> IonResult<Module<M>> {
        let next_address = self.index.len();
        let macro_id = self.id.try_derive_macro_id(opt_name, next_address)?;
        // we alias to ourselves for defined macros
        let next_macro_handle = MacroHandle::Bind(MacroBind::Definition(macro_id));
        self.with_handle(next_macro_handle, next_macro_val)
    }

    /// Aliases a macro within this module with an optional name to the given macro identifier.
    pub fn with_aliased_macro(
        &self,
        opt_name: Option<Name>,
        source_macro_id: MacroId,
        next_macro_val: M,
    ) -> IonResult<Module<M>> {
        let next_address = self.index.len();
        let next_macro_bind =
            source_macro_id.try_derive_macro_bind_alias(opt_name, next_address)?;
        let next_macro_handle = MacroHandle::Bind(next_macro_bind);
        self.with_handle(next_macro_handle, next_macro_val)
    }

    /// Returns the underlying module identifier.
    pub fn id(&self) -> &ModuleId {
        &self.id
    }
}

impl<M: MacroVal> MacroByAddress<M> for Module<M> {
    fn macro_by_address(&self, address: usize) -> Option<&MacroHandleVal<M>> {
        self.index.macro_by_address(address)
    }
}

impl<M: MacroVal> MacroByName<M> for Module<M> {
    fn macro_by_name(&self, name: &Name) -> Option<&IndexEntry<M>> {
        self.index.macro_by_name(name)
    }
}

impl<M: MacroVal> Clone for Module<M> {
    fn clone(&self) -> Self {
        Module {
            id: self.id.clone(),
            index: self.index.clone(),
        }
    }
}

/// Represents the environment for *building* a module.
#[derive(Debug)]
pub struct ModuleEnv<M: MacroVal> {
    current_module: Module<M>,
    index: MacroIndex<M>,
}

impl<M: MacroVal> ModuleEnv<M> {
    pub(self) fn empty(current_module: Module<M>) -> Self {
        Self {
            current_module,
            index: MacroIndex::empty(),
        }
    }
}

// TODO the encoding directive environment and the e-expression environment
