// Copyright Amazon.com, Inc. or its affiliates.

//! Static type support for Ion macros.
//!
//! This goes above the runtime type system of Ion within the macro system.

use crate::IonType;
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
                FixedType::UInt8 => "uint8",
                FixedType::UInt16 => "uint16",
                FixedType::UInt32 => "uint32",
                FixedType::UInt64 => "uint64",
                FixedType::Int8 => "int8",
                FixedType::Int16 => "int16",
                FixedType::Int32 => "int32",
                FixedType::Int64 => "int64",
                FixedType::Float16 => "float16",
                FixedType::Float32 => "float32",
                FixedType::Float64 => "float64",
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
                UnionType::Any => "any",
                UnionType::Number => "number",
                UnionType::Exact => "exact",
                UnionType::Text => "text",
                UnionType::Lob => "lob",
                UnionType::Sequence => "sequence",
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

/// Pair of type and cardinality
pub struct ParamType(pub Box<StaticType>, pub Cardinality);

impl Display for ParamType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", *self.0, self.1)
    }
}

/// Type representation of a macro shape.
pub struct ArrowType {
    result: Box<StaticType>,
    parameters: Vec<ParamType>,
}

impl Display for ArrowType {
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
    // TODO make this is parameterized
    Shape(Box<ArrowType>),
}

impl Display for StaticType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}
