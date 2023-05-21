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

// TODO better name for this concept (MacroVal seems to abstract).
// TODO add some examples in the data structures to where in MDL or the like this shows up.

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

// XXX we have to implement Clone, because derive requires M: Clone
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
    fn macro_by_name(&self, name: &Name) -> Option<&MacroEntry<M>>;
}

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

// XXX we have to implement Clone, because derive requires M: Clone
impl<M: MacroVal> Clone for MacroTable<M> {
    fn clone(&self) -> Self {
        MacroTable {
            table: self.table.clone(),
        }
    }
}

/// A mapping of name to module.
pub trait ModuleMappable<M: MacroVal>: Sized {
    /// Constructs a version of this mapping bound with a new module associated with it.
    fn try_with_module(&self, name: Name, module: Module<M>) -> IonResult<Self>;

    /// Returns the module associated with a name if it exists.
    fn module(&self, name: &Name) -> Option<&Module<M>>;
}

/// Association of name to modules.  This corresponds to the loaded modules in some context
/// that is used for qualified names to resolve
#[derive(Debug)]
pub struct ModuleMap<M: MacroVal> {
    modules: HashTrieMap<Name, Module<M>>,
}

impl<M: MacroVal> ModuleMap<M> {
    /// Creates an empty module map.
    pub fn empty() -> Self {
        Self {
            modules: HashTrieMap::new(),
        }
    }
}

impl<M: MacroVal> ModuleMappable<M> for ModuleMap<M> {
    fn try_with_module(&self, name: Name, module: Module<M>) -> IonResult<Self> {
        match self.modules.get(&name) {
            None => Ok(ModuleMap {
                modules: self.modules.insert(name, module),
            }),
            Some(module) => {
                illegal_operation(format!("Duplicate module name {} for {:?}", name, module))
            }
        }
    }

    fn module(&self, name: &Name) -> Option<&Module<M>> {
        self.modules.get(name)
    }
}

// XXX we have to implement Clone, because derive requires M: Clone
impl<M: MacroVal> Clone for ModuleMap<M> {
    fn clone(&self) -> Self {
        ModuleMap {
            modules: self.modules.clone(),
        }
    }
}

/// A macro (or list of macros) associated by some name.
///
/// This tracks non-unique names, and the distinct case.
#[derive(Debug)]
pub enum MacroEntry<M: MacroVal> {
    // TODO consider if we really want to track all the conflicts--it is nice for debugging...
    /// Indicates that a name maps to more than one distinct handle.
    Ambiguous(Vector<MacroHandleVal<M>>),

    /// Indicates a unique address in the index corresponding to the name.
    Distinct(MacroHandleVal<M>),
}

// XXX we have to implement Clone, because derive requires M: Clone
impl<M: MacroVal> Clone for MacroEntry<M> {
    fn clone(&self) -> Self {
        match self {
            MacroEntry::Ambiguous(vals) => MacroEntry::Ambiguous(vals.clone()),
            MacroEntry::Distinct(val) => MacroEntry::Distinct(val.clone()),
        }
    }
}

/// Internal address/name mapping for macros.
#[derive(Debug)]
struct MacroMap<M: MacroVal> {
    table: MacroTable<M>,
    names: HashTrieMap<Name, MacroEntry<M>>,
}

impl<M: MacroVal> MacroMap<M> {
    /// Constructs an empty index.
    fn empty() -> Self {
        Self {
            table: MacroTable::empty(),
            names: HashTrieMap::new(),
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
    ) -> (Option<MacroEntry<M>>, Self) {
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
            None => self.names.clone(),
            Some(name) => match self.names.get(name) {
                None => {
                    // nothing already is in the index for this name
                    let index_entry = MacroEntry::Distinct(next_macro.clone());
                    index_entry_opt = Some(index_entry.clone());
                    self.names.insert(name.clone(), index_entry)
                }
                Some(existing) => match existing {
                    MacroEntry::Ambiguous(others) => {
                        let index_entry =
                            MacroEntry::Ambiguous(others.push_back(next_macro.clone()));
                        index_entry_opt = Some(index_entry.clone());
                        self.names.insert(name.clone(), index_entry)
                    }
                    MacroEntry::Distinct(previous) => {
                        let index_entry = MacroEntry::Ambiguous(
                            [previous.clone(), next_macro.clone()].into_iter().collect(),
                        );
                        index_entry_opt = Some(index_entry.clone());
                        self.names.insert(name.clone(), index_entry)
                    }
                },
            },
        };

        (
            index_entry_opt,
            Self {
                table: next_table,
                names: next_index,
            },
        )
    }
}

impl<M: MacroVal> MacroByAddress<M> for MacroMap<M> {
    fn macro_by_address(&self, address: usize) -> Option<&MacroHandleVal<M>> {
        self.table.macro_by_address(address)
    }
}

impl<M: MacroVal> MacroByName<M> for MacroMap<M> {
    fn macro_by_name(&self, name: &Name) -> Option<&MacroEntry<M>> {
        self.names.get(name)
    }
}

// XXX we have to implement Clone, because derive requires M: Clone
impl<M: MacroVal> Clone for MacroMap<M> {
    fn clone(&self) -> Self {
        MacroMap {
            table: self.table.clone(),
            names: self.names.clone(),
        }
    }
}

/// Represents a context that can define or alias macro definitions.
pub trait MacroBindable<M: MacroVal>: Sized {
    /// Defines a macro within this context with an optional name returning the new module containing
    /// it.
    ///
    /// Note that such a macro will have a [`MacroId`] that is bound to the identity of
    /// this module.
    fn with_defined_macro(&self, opt_name: Option<Name>, next_macro_val: M) -> IonResult<Self>;

    /// Aliases a macro within this context with an optional name to the given macro identifier.
    fn with_aliased_macro(
        &self,
        opt_name: Option<Name>,
        source_macro_id: MacroId,
        next_macro_val: M,
    ) -> IonResult<Self>;
}

/// Represents the environment for a macro module.
#[derive(Debug)]
pub struct Module<M: MacroVal> {
    id: ModuleId,
    map: MacroMap<M>,
}

impl<M: MacroVal> Module<M> {
    /// Constructs an empty module for some [`ModuleId`].
    pub fn empty(id: ModuleId) -> Self {
        Self {
            id,
            map: MacroMap::empty(),
        }
    }

    /// Internal macro alias/definition binding.
    fn with_handle(&self, next_handle: MacroHandle, next_macro_val: M) -> IonResult<Module<M>> {
        let (next_index_entry_opt, next_index) = self.map.with_macro(next_handle, next_macro_val);
        if matches!(&next_index_entry_opt, Some(MacroEntry::Ambiguous(_))) {
            return illegal_operation(format!(
                "Duplicate macro named in module: {:?}",
                next_index_entry_opt
            ));
        }
        Ok(Self {
            id: self.id.clone(),
            map: next_index,
        })
    }

    /// Returns the underlying module identifier.
    pub fn id(&self) -> &ModuleId {
        &self.id
    }
}

impl<M: MacroVal> MacroBindable<M> for Module<M> {
    fn with_defined_macro(&self, opt_name: Option<Name>, next_macro_val: M) -> IonResult<Self> {
        let next_address = self.map.len();
        let macro_id = self.id.try_derive_macro_id(opt_name, next_address)?;
        // we alias to ourselves for defined macros
        let next_macro_handle = MacroHandle::Bind(MacroBind::Definition(macro_id));
        self.with_handle(next_macro_handle, next_macro_val)
    }

    fn with_aliased_macro(
        &self,
        opt_name: Option<Name>,
        source_macro_id: MacroId,
        next_macro_val: M,
    ) -> IonResult<Self> {
        let next_address = self.map.len();
        let next_macro_bind =
            source_macro_id.try_derive_macro_bind_alias(opt_name, next_address)?;
        let next_macro_handle = MacroHandle::Bind(next_macro_bind);
        self.with_handle(next_macro_handle, next_macro_val)
    }
}

/// Simple macro to create the delegate lookups
macro_rules! delegate_macro_lookup {
    ($t:ty, $me:ident, $exp:expr) => {
        impl<M: MacroVal> MacroByAddress<M> for $t {
            fn macro_by_address(&$me, address: usize) -> Option<&MacroHandleVal<M>> {
                $exp.macro_by_address(address)
            }
        }

        impl<M: MacroVal> MacroByName<M> for $t {
            fn macro_by_name(&$me, name: &Name) -> Option<&MacroEntry<M>> {
                $exp.macro_by_name(name)
            }
        }
    };
}

delegate_macro_lookup!(Module<M>, self, self.map);

// XXX we have to implement Clone, because derive requires M: Clone
impl<M: MacroVal> Clone for Module<M> {
    fn clone(&self) -> Self {
        Module {
            id: self.id.clone(),
            map: self.map.clone(),
        }
    }
}

/// Represents an environment for operating with macros.
///
/// This contains the loaded [`ModuleMap`], the aliases (name to macro mapping),
/// and the [`MacroTable`] of local addresses that represents the macros for environment.
///
/// When *building modules*, the environment's macro table is not used.
/// When building *encoding contexts*, the environment's table is used to assign
/// local addresses for E-expressions.
///
/// Unlike [`Module`], [`MacroBind::Definition`] is never possible as a [`MacroHandle::Bind`].
/// Environments that use a table (i.e., encoding contexts) will use [`MacroBind::Alias`]
/// to assign slots to that table (and associated names). Environments that do not
/// have a table (i.e., module environments), only use [`MacroHandle::Alias`] handles.
#[derive(Debug)]
pub struct MacroEnv<M: MacroVal> {
    modules: ModuleMap<M>,
    aliases: MacroMap<M>,
}

impl<M: MacroVal> MacroEnv<M> {
    pub fn empty() -> Self {
        Self {
            modules: ModuleMap::empty(),
            aliases: MacroMap::empty(),
        }
    }
}

delegate_macro_lookup!(MacroEnv<M>, self, self.aliases);

impl<M: MacroVal> ModuleMappable<M> for MacroEnv<M> {
    fn try_with_module(&self, name: Name, module: Module<M>) -> IonResult<Self> {
        Ok(Self {
            modules: self.modules.try_with_module(name, module)?,
            aliases: self.aliases.clone(),
        })
    }

    fn module(&self, name: &Name) -> Option<&Module<M>> {
        self.modules.module(name)
    }
}

// XXX we have to implement Clone, because derive requires M: Clone
impl<M: MacroVal> Clone for MacroEnv<M> {
    fn clone(&self) -> Self {
        MacroEnv {
            modules: self.modules.clone(),
            aliases: self.aliases.clone(),
        }
    }
}

/// Environment for *building* a module.
pub struct MacroModuleEnv<M: MacroVal> {
    env: MacroEnv<M>,
    module: Module<M>,
}

impl<M: MacroVal> MacroModuleEnv<M> {
    /// Constructs a new environment with a module binding.
    pub fn try_with_module(&self, name: Name, module: Module<M>) -> IonResult<Self> {
        Ok(Self {
            env: self.env.try_with_module(name, module)?,
            module: self.module.clone(),
        })
    }
}

delegate_macro_lookup!(MacroModuleEnv<M>, self, self.env);

impl<M: MacroVal> ModuleMappable<M> for MacroModuleEnv<M> {
    fn try_with_module(&self, name: Name, module: Module<M>) -> IonResult<Self> {
        Ok(Self {
            env: self.env.try_with_module(name, module)?,
            module: self.module.clone(),
        })
    }

    fn module(&self, name: &Name) -> Option<&Module<M>> {
        self.env.module(name)
    }
}

impl<M: MacroVal> MacroBindable<M> for MacroModuleEnv<M> {
    fn with_defined_macro(&self, opt_name: Option<Name>, next_macro_val: M) -> IonResult<Self> {
        Ok(Self {
            env: self.env.clone(),
            module: self.module.with_defined_macro(opt_name, next_macro_val)?,
        })
    }

    fn with_aliased_macro(
        &self,
        opt_name: Option<Name>,
        source_macro_id: MacroId,
        next_macro_val: M,
    ) -> IonResult<Self> {
        Ok(Self {
            env: self.env.clone(),
            module: self
                .module
                .with_aliased_macro(opt_name, source_macro_id, next_macro_val)?,
        })
    }
}

// XXX we have to implement Clone, because derive requires M: Clone
impl<M: MacroVal> Clone for MacroModuleEnv<M> {
    fn clone(&self) -> Self {
        MacroModuleEnv {
            env: self.env.clone(),
            module: self.module.clone(),
        }
    }
}
