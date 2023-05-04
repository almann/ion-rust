// Copyright Amazon.com, Inc. or its affiliates.

//! Names and identifiers for macros.

use crate::macros::ParseStr;
use crate::IonResult;
use std::fmt::{Display, Formatter};

/// An identifier that represents a name of a parameter, module, or macro.
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub struct Name {
    text: String,
}

impl Name {
    pub fn text(&self) -> &str {
        self.text.as_str()
    }
}

impl ParseStr for Name {
    fn parse_str<S>(_as_str: S) -> IonResult<Self>
    where
        S: AsRef<str>,
    {
        // TODO implement Ion identifier parsing here...
        todo!()
    }
}

impl Display for Name {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.text)
    }
}

/// Represents the unique module identifier in a given encoding context.
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub enum ModuleId {
    /// A module defined inline in an encoding context.
    Inline(Name),
    /// A module defined in some catalog entry which has a name and a version.
    Catalog(String, usize),
}

/// Full identifier for a Macro, which is its module, the optional name, and its address within
/// the module.
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub struct MacroId {
    module: ModuleId,
    name: Option<Name>,
    address: usize,
}

impl MacroId {
    /// Returns the module identifier where this macro is defined.
    pub fn module_id(&self) -> &ModuleId {
        &self.module
    }

    /// The name of the macro if defined.
    pub fn name(&self) -> Option<&str> {
        match &self.name {
            None => None,
            Some(name) => Some(name.text()),
        }
    }

    /// The address for this macro in the module it is defined in.
    pub fn address(&self) -> usize {
        self.address
    }
}
