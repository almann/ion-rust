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

use crate::macros::ident::{MacroId, MacroName, ModuleId, Name};
use crate::result::illegal_operation;
use crate::IonResult;
use delegate::delegate;
use rpds::{HashTrieMap, Vector};
use std::borrow::Borrow;
use std::fmt::Debug;

/// Marker trait for things that can be macro values within environments/tables/modules.
pub trait MacroVal: Debug {}

// TODO name is a relative concept here that we may have to change
//      a `MacroName` is a optional name/required address in a module, but aliases
//      are environmental constructs that have a required name/no address.
//      Maybe, we have a `Handle` with Macro or `MacroName`.

/// A macro value that knows its name.
#[derive(Debug)]
pub struct MacroNameVal<M: MacroVal> {
    name: MacroName,
    value: M,
}

impl<M> MacroNameVal<M>
where
    M: MacroVal,
{
    pub fn new(name: MacroName, value: M) -> Self {
        Self { name, value }
    }

    pub fn name(&self) -> &MacroName {
        &self.name
    }

    pub fn value(&self) -> &M {
        &self.value
    }
}

/// A mapping of address to macro value.
trait MacroByAddress<M: MacroVal> {
    /// Retrieves a macro value by some offset.
    fn macro_by_address(&self, address: usize) -> Option<&MacroNameVal<M>>;
}

/// A mapping of name to macro value.
trait MacroByName<M: MacroVal> {
    fn macro_by_name<N: Borrow<Name>>(&self, name: N) -> Option<&MacroNameVal<M>>;
}

/// Represents an ordered table of macros defining addresses from a zero-based offset.
#[derive(Debug)]
pub struct MacroTable<M: MacroVal> {
    // XXX currently this is just a persistent Vector, but we could have a variant to Vec
    //     when we "freeze" the module to have O(1) lookup at O(N) one time cost
    //     if we don't do this, access is always O(log N) because we're some kind of trie or
    //     the like under the hood.
    table: Vector<MacroNameVal<M>>,
}

impl<M: MacroVal> MacroTable<M> {
    /// Constructs the empty macro table.
    pub fn empty() -> Self {
        Self {
            table: Vector::new(),
        }
    }

    /// Creates a table the next macro added to it.
    pub fn with_additional_macro(&self, next_macro: MacroNameVal<M>) -> Self {
        Self {
            table: self.table.push_back(next_macro),
        }
    }

    /// Returns the count of elements in the table.
    pub fn len(&self) -> usize {
        return self.table.len();
    }
}

impl<M: MacroVal> MacroByAddress<M> for MacroTable<M> {
    fn macro_by_address(&self, address: usize) -> Option<&MacroNameVal<M>> {
        self.table.get(address)
    }
}

/// Name to address entry.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
enum IndexEntry {
    /// Indicates that a name maps to more than one distinct address.
    Ambiguous,
    /// Indicates a unique address in the index corresponding to the name.
    Address(usize),
}

/// Internal address/name mapping.
#[derive(Debug)]
struct MacroIndex<M: MacroVal> {
    table: MacroTable<M>,
    index: HashTrieMap<Name, IndexEntry>,
}

impl<M: MacroVal> MacroIndex<M> {
    /// Constructs an empty index.
    fn empty() -> Self {
        Self {
            table: MacroTable::empty(),
            index: HashTrieMap::new(),
        }
    }

    /// The number of entries in the underlying table.
    fn len(&self) -> usize {
        self.table.len()
    }

    /// Inserts the macro into the table and the index, returning the entry in the index and
    /// the version of the index containing the added macro.
    ///
    /// The name ***must*** have the address of the end of the table specified.
    fn with_macro(&self, macro_name: MacroName, next_macro_val: M) -> (IndexEntry, Self) {
        assert_eq!(self.len(), macro_name.address());
        let mut index_entry = IndexEntry::Address(macro_name.address());
        let next_index = match macro_name.name() {
            None => self.index.clone(),
            Some(name) => match self.index.get(name) {
                Some(IndexEntry::Ambiguous) => {
                    index_entry = IndexEntry::Ambiguous;
                    self.index.clone()
                }
                Some(IndexEntry::Address(_)) => {
                    index_entry = IndexEntry::Ambiguous;
                    self.index.insert(name.clone(), IndexEntry::Ambiguous)
                }
                None => self
                    .index
                    .insert(name.clone(), IndexEntry::Address(macro_name.address())),
            },
        };
        let next_macro = MacroNameVal::new(macro_name, next_macro_val);
        let next_table = self.table.with_additional_macro(next_macro);
        (
            index_entry,
            Self {
                table: next_table,
                index: next_index,
            },
        )
    }
}

impl<M: MacroVal> MacroByAddress<M> for MacroIndex<M> {
    fn macro_by_address(&self, _address: usize) -> Option<&MacroNameVal<M>> {
        todo!()
    }
}

impl<M: MacroVal> MacroByName<M> for MacroIndex<M> {
    fn macro_by_name<N: Borrow<Name>>(&self, _name: N) -> Option<&MacroNameVal<M>> {
        todo!()
    }
}

/// Represents a module of macros.
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
        let macro_id = self
            .id
            .try_derive_macro_id(opt_name.clone(), next_address)?;
        // we alias to ourselves for defined macros
        self.with_aliased_macro(opt_name, macro_id, next_macro_val)
    }

    /// Aliases a macro within this module with an optional name to the given macro identifier.
    pub fn with_aliased_macro(
        &self,
        opt_name: Option<Name>,
        source_macro_id: MacroId,
        next_macro_val: M,
    ) -> IonResult<Module<M>> {
        let next_address = self.index.len();
        let macro_name = source_macro_id.try_derive_macro_name(
            self.id.clone(),
            opt_name.clone(),
            next_address,
        )?;
        let (next_index_entry, next_index) = self.index.with_macro(macro_name, next_macro_val);
        if matches!(next_index_entry, IndexEntry::Ambiguous) {
            return illegal_operation(format!(
                "Duplicate macro named {} in module",
                opt_name.unwrap()
            ));
        }
        Ok(Self {
            id: self.id.clone(),
            index: next_index,
        })
    }

    /// Returns the underlying module identifier.
    pub fn id(&self) -> &ModuleId {
        &self.id
    }
}

impl<M: MacroVal> MacroByAddress<M> for Module<M> {
    delegate! {
        to self.index {
            fn macro_by_address(&self, _address: usize) -> Option<&MacroNameVal<M>>;
        }
    }
}

impl<M: MacroVal> MacroByName<M> for Module<M> {
    delegate! {
        to self.index {
            fn macro_by_name<N: Borrow<Name>>(&self, _name: N) -> Option<&MacroNameVal<M>>;
        }
    }
}

/// Represents a lookup environment table/index for macros.
#[derive(Debug)]
pub struct MacroEnv<M: MacroVal> {
    index: MacroIndex<M>,
}
