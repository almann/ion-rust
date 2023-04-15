// Copyright Amazon.com, Inc. or its affiliates.

//! Static type support for Ion macros.
//!
//! This goes above the runtime type system of Ion within the macro system.

use crate::macros::constants::types::*;
use crate::{IonError, IonType};
use std::fmt::{Display, Formatter};

/// Macro types that are encoded without and fixed width.
/// These types are structural constrained types over their general Ion equivalent.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum FixedType {
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    Int8,
    Int16,
    Int32,
    Int64,
    Float16,
    Float32,
    Float64,
}

impl Display for FixedType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                FixedType::UInt8 => UINT8,
                FixedType::UInt16 => UINT16,
                FixedType::UInt32 => UINT32,
                FixedType::UInt64 => UINT64,
                FixedType::Int8 => INT8,
                FixedType::Int16 => INT16,
                FixedType::Int32 => INT32,
                FixedType::Int64 => INT64,
                FixedType::Float16 => FLOAT16,
                FixedType::Float32 => FLOAT32,
                FixedType::Float64 => FLOAT64,
            }
        )
    }
}

/// Macro types that are _abstract_ over the type system.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum UnionType {
    /// The top-type, any and all Ion values are of this type.
    Any,
    /// A value that is an `int`, `float`, or `decimal`.
    Number,
    /// A value that is an `int` or `decimal`.
    Exact,
    /// A value that is a `string` or `symbol`.
    Text,
    /// A value that is a `clob` or `blob`.
    Lob,
    /// A value that is a `sexp` or `list`.
    Sequence,
}

impl Display for UnionType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                UnionType::Any => ANY,
                UnionType::Number => NUMBER,
                UnionType::Exact => EXACT,
                UnionType::Text => TEXT,
                UnionType::Lob => LOB,
                UnionType::Sequence => SEQUENCE,
            }
        )
    }
}

/// Cardinality of arguments for a macro parameter.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum Cardinality {
    ExactlyOne,
    ZeroOrOne,
    ZeroOrMore,
    OneOrMore,
    Rest,
}

impl Display for Cardinality {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Cardinality::ExactlyOne => "!",
                Cardinality::ZeroOrOne => "?",
                Cardinality::ZeroOrMore => "*",
                Cardinality::OneOrMore => "+",
                Cardinality::Rest => "...",
            }
        )
    }
}

// TODO expand support arrow `->` parameters

/// Pair of type and cardinality
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct ParamType(pub Box<StaticType>, pub Cardinality);

impl Display for ParamType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", *self.0, self.1)
    }
}

/// Type representation of a macro shape.
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct MacroType {
    result: Box<StaticType>,
    parameters: Vec<ParamType>,
}

impl Display for MacroType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

/// Static types for the Ion macro system.
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum StaticType {
    Union(UnionType),
    Tagged(IonType),
    Untagged(IonType),
    Fixed(FixedType),
    Macro(Box<MacroType>),
}

impl Display for StaticType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            StaticType::Union(t) => write!(f, "{}", t),
            StaticType::Tagged(t) => write!(f, "{}", t),
            StaticType::Untagged(t) => write!(f, "{}", t),
            StaticType::Fixed(t) => write!(f, "{}", t),
            StaticType::Macro(t) => write!(f, "{}", t),
        }
    }
}
