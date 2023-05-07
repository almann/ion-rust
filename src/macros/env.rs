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

use crate::macros::ident::{ModuleId, Name};
use rpds::{HashTrieMap, Vector};

/// Represents the ordered table of macros.
#[derive(Debug, Clone)]
pub struct MacroTable<M> {
    // XXX currently this is just a persistent Vector, but we could have a variant to Vec
    //     when we "freeze" the module to have O(1) lookup at O(N) one time cost
    //     if we don't do this, access is always O(log N) because we're some kind of trie or
    //     the like under the hood.
    table: Vector<M>,
}

impl<M> MacroTable<M> {
    /// Constructs the empty macro table.
    pub fn empty() -> Self {
        Self {
            table: Vector::new(),
        }
    }

    /// Returns the count of elements in the table.
    pub fn len(&self) -> usize {
        return self.table.len();
    }

    /// Creates a table the next macro added to it.
    pub fn add_macro(&self, next: M) -> Self {
        Self {
            table: self.table.push_back(next),
        }
    }

    /// Retrieves the macro definition at some offset in the table if within bounds.
    pub fn get_macro(&self, index: usize) -> Option<&M> {
        self.table.get(index)
    }
}

/// Represents a module of macros.
#[derive(Debug, Clone)]
pub struct Module<M> {
    id: ModuleId,
    table: MacroTable<M>,
    index: HashTrieMap<Name, M>,
}

impl<M> Module<M> {
    /// Constructs an empty module for some [`ModuleId`].
    pub fn empty(id: ModuleId) -> Self {
        Self {
            id,
            table: MacroTable::empty(),
            index: HashTrieMap::new(),
        }
    }

    /// Returns the underlying module identifier.
    pub fn id(&self) -> &ModuleId {
        &self.id
    }
}
