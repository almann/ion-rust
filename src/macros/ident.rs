// Copyright Amazon.com, Inc. or its affiliates.

//! Names and identifiers for macros.
//!
//! These types are all immutable are persistent in that they try to share underlying structure.
//! Therefore, `clone()`-ing these types are generally inexpensive.

use crate::macros::ParseStr;
use crate::result::illegal_operation;
use crate::IonResult;
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
    /// The underlying text of the name.
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

/// An address in a table.
pub type Address = usize;

/// An entity that has an optional name and a non-optional address.
pub trait Addressable {
    /// Returns the underlying name if available.
    fn name(&self) -> Option<&Name>;

    /// Returns the address of this entity.
    fn address(&self) -> Address;
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
        if version == 0 {
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
fn illegal_address<T>(address: Address) -> IonResult<T> {
    illegal_operation(format!("Invalid address for macro: {}", address))
}

// FIXME no need to check address here.
#[inline]
fn valid_address(address: Address) -> IonResult<()> {
    if address == 0 {
        illegal_address(address)
    } else {
        Ok(())
    }
}

// TODO spelling of external... shared?

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
    pub fn try_derive_macro_id(&self, name: Option<Name>, address: Address) -> IonResult<MacroId> {
        Ok(MacroId {
            module_id: self.clone(),
            name: MacroName::try_new(name, address)?,
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
    name: MacroName,
}

impl MacroId {
    /// Derives a [`MacroBind::Alias`] from this identifier with the given name/address.
    pub fn try_derive_macro_bind_alias(
        &self,
        name: Option<Name>,
        address: Address,
    ) -> IonResult<MacroBind> {
        let macro_name = MacroName::try_new(name, address)?;
        Ok(MacroBind::Alias(self.clone(), macro_name))
    }

    /// Returns the module identifier where this macro is defined.
    pub fn module_id(&self) -> &ModuleId {
        &self.module_id
    }
}

impl Addressable for MacroId {
    fn name(&self) -> Option<&Name> {
        self.name.name()
    }

    fn address(&self) -> Address {
        self.name.address()
    }
}

/// Represents a name/address of a macro for that is not bound to anything.
///
/// This is a name/address that hasn't been assigned to anything.
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub struct MacroName {
    name: Option<Name>,
    address: Address,
}

impl MacroName {
    /// Constructs a new name.
    pub(crate) fn try_new(name: Option<Name>, address: Address) -> IonResult<Self> {
        valid_address(address)?;
        Ok(Self { name, address })
    }
}

impl Addressable for MacroName {
    fn name(&self) -> Option<&Name> {
        self.name.as_ref()
    }

    fn address(&self) -> Address {
        self.address
    }
}

/// A name assigned to a macro.  This can be thought of as the name given to some
/// macro within a module, though this does not imply what module such a bind is assigned to.
///
/// Macro identifiers are unique, but more than one name is allowed to map to
/// a given macro identifier through aliasing them in a module's macro table.
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum MacroBind {
    /// A macro that has been defined where it is bound.
    Definition(MacroId),

    /// A macro name that is bound some other macro definition.
    Alias(MacroId, MacroName),
}

impl MacroBind {
    /// Returns the identity of the macro underlying this bound name.
    pub fn id(&self) -> &MacroId {
        match self {
            MacroBind::Definition(id) => id,
            MacroBind::Alias(id, _) => id,
        }
    }
}

impl Addressable for MacroBind {
    fn name(&self) -> Option<&Name> {
        match self {
            MacroBind::Definition(id) => id.name(),
            MacroBind::Alias(_, macro_name) => macro_name.name(),
        }
    }

    fn address(&self) -> Address {
        match self {
            MacroBind::Definition(id) => id.address(),
            MacroBind::Alias(_, name) => name.address(),
        }
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
    Address(Address),
}

// TODO raise the issue around E-Expressions having unqualified names as `:foo`
//      E-EXPRESSIONS:
//      (:foo ...)    // unqualified foo <-- foo anywhere, provided installed in macro table
//      (:5 ...)      // partially qualified 5 <-- 5 in the local macro table
//      MDL:
//      (foo ...)     // MDL unqualified foo <-- foo anywhere
//      (':foo' ...)  // MDL partially qualified foo <-- foo in the current module
//      (':5' ...)    // MDL partially qualified 5 <-- 5 in the current module

// TODO should we collapse Partial into something like Local(Address)

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
    /// An *unqualified* name referring to some macro for which no module is implied.
    Unqualified(Name),

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
