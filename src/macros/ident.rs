// Copyright Amazon.com, Inc. or its affiliates.

//! Names and identifiers for macros.
//!
//! These types are all immutable are persistent in that they try to share underlying structure.
//! Therefore, `clone()`-ing these types are generally inexpensive.

use crate::macros::ParseStr;
use crate::result::illegal_operation;
use crate::IonResult;
use std::borrow::Borrow;
use std::fmt::{Display, Formatter};
use std::rc::Rc;

// TODO we use shared pointers here--we might want to consider something like 'archery'
//      to abstract over this (e.g., `Arc` for sharing/`Rc` for single threaded use)

/// An identifier that represents a name of a parameter, module, or macro.
///
/// This is basically just an interned string with some constraints as to what can be
/// contained within it; i.e., Ion identifier syntax for symbols.
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub struct Name {
    text: Rc<String>,
}

impl Name {
    /// The underlying text of the string
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

impl Borrow<str> for Name {
    fn borrow(&self) -> &str {
        self.text()
    }
}

impl AsRef<str> for Name {
    fn as_ref(&self) -> &str {
        self.text()
    }
}

impl Display for Name {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.text)
    }
}

/// The identifier for a global resource (e.g., a catalog).
///
/// External identifiers have an interned string name and a version `>= 1`.
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub struct ExternalId {
    name: Rc<String>,
    version: usize,
}

impl ExternalId {
    /// Creates an external identifier from a name and version.  The version must be `>= 1`
    /// or this returns `Err`.
    pub fn try_new<S: Into<String>>(name: S, version: usize) -> IonResult<Self> {
        if version <= 0 {
            illegal_operation(format!("External version must be >= 1: {}", version))
        } else {
            Ok(Self {
                name: Rc::new(name.into()),
                version,
            })
        }
    }
}

#[inline]
fn illegal_address<T>(address: usize) -> IonResult<T> {
    illegal_operation(format!("Invalid address for macro: {}", address))
}

#[inline]
fn valid_address(address: usize) -> IonResult<()> {
    if address <= 0 {
        illegal_address(address)
    } else {
        Ok(())
    }
}

/// Represents the unique module identifier in a given encoding context.
///
/// Notable, a shared module's identifier may map to many local names, whereas an *inline module*
/// (i.e., one defined in an encoding directive), has exactly one name.
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub enum ModuleId {
    /// A module defined inline in an encoding context.
    Inline(Name),
    /// A module defined externally.
    External(ExternalId),
}

impl ModuleId {
    /// Derives a [`ModuleName`] from this module identifier.
    pub fn derive_name(&self, name: Name) -> ModuleName {
        ModuleName {
            id: self.clone(),
            name,
        }
    }

    /// Derives a [`MacroId`] from this module identifier.
    pub fn try_derive_macro_id(&self, name: Option<Name>, address: usize) -> IonResult<MacroId> {
        valid_address(address)?;
        Ok(MacroId {
            module_id: self.clone(),
            name,
            address,
        })
    }
}

/// Represents a name associated with a module.
///
/// When loading modules from a catalog, this name is not unique, but the underlying
/// [`ModuleId`] is.
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub struct ModuleName {
    id: ModuleId,
    name: Name,
}

impl ModuleName {
    /// Returns the underlying module identifier for this name.
    fn id(&self) -> &ModuleId {
        &self.id
    }

    /// Returns the name bound to this module.
    fn name(&self) -> &str {
        self.name.text()
    }
}

/// Full identifier for a Macro, which is its module, the optional name, and its address within
/// the module.
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub struct MacroId {
    module_id: ModuleId,
    name: Option<Name>,
    address: usize,
}

impl MacroId {
    /// Derives a macro name from this identifier.
    pub fn try_derive_macro_name(
        &self,
        module_name: ModuleName,
        name: Option<Name>,
        address: usize,
    ) -> IonResult<MacroName> {
        valid_address(address)?;
        Ok(MacroName {
            id: self.clone(),
            module_name,
            name,
            address,
        })
    }

    /// Returns the module identifier where this macro is defined.
    pub fn module_id(&self) -> &ModuleId {
        &self.module_id
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

/// A qualified name given to a macro.  This can be thought of as the name given to some
/// macro within a module.
///
/// Macro identifiers are unique, but more than one qualified name is allowed to map to
/// a given macro identifier through aliasing them in a module's macro table.
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct MacroName {
    id: MacroId,
    module_name: ModuleName,
    name: Option<Name>,
    address: usize,
}

impl MacroName {
    /// Returns the identity of the macro underlying this name.
    pub fn id(&self) -> &MacroId {
        &self.id
    }

    /// Returns the module name from whence this macro's name is defined.
    pub fn module_name(&self) -> &ModuleName {
        &self.module_name
    }

    /// Returns the potentially unspecified name for this macro's name definition.
    pub fn name(&self) -> Option<&str> {
        match &self.name {
            None => None,
            Some(name) => Some(name.text()),
        }
    }

    /// Returns the address of this name in the module it was defined in
    pub fn address(&self) -> usize {
        self.address
    }
}

/// An unqualified name or address of a Macro.
///
/// This on its own cannot identify a macro.  An environment is necessary to determine
/// if and what this refers to.  E.g., the *macro table* of an *encoding context* for
/// E-Expressions.
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum UnqualifiedMacroRef {
    Name(Name),
    Address(usize),
}

/// Reference to a macro, which may be [*unqualified*][u], [*partially qualified*][p],
/// or [*fully qualified*][f].
///
/// On its own, a reference does is not resolved to some unique macro.  See [`ResolvedMacroRef`]
/// for details.
///
/// [u]: Self::Unqualified
/// [p]: Self::Partial
/// [f]: Self::Full
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum MacroRef {
    /// An *unqualified* macro reference for which no module is implied.
    Unqualified(UnqualifiedMacroRef),

    /// A *partially* qualified reference, generally valid for an environment where
    /// the reference is referring to the *current* module being defined where a
    /// [`ModuleName`] may not be available to reference a macro.
    Partial(UnqualifiedMacroRef),

    /// A *fully* qualified reference by referring to some module by name and some macro
    /// within that module.
    Full(Name, UnqualifiedMacroRef),
}

/// A macro reference that has been resolved to the underlying [`MacroId`].
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct ResolvedMacroRef {
    id: MacroId,
    reference: MacroRef,
}

impl ResolvedMacroRef {
    #[inline]
    pub fn new(id: MacroId, reference: MacroRef) -> Self {
        Self { id, reference }
    }

    /// Returns the underlying macro identifier.
    #[inline]
    pub fn id(&self) -> &MacroId {
        &self.id
    }

    /// Returns the underlying macro reference.
    #[inline]
    pub fn reference(&self) -> &MacroRef {
        &self.reference
    }
}
