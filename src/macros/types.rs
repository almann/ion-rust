// Copyright Amazon.com, Inc. or its affiliates.

//! Static type support for Ion macros.
//!
//! This goes above the runtime type system of Ion within the macro system.

use crate::macros::constants::syntax::*;
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
                Cardinality::ExactlyOne => EXACTLY_ONE_SIGIL,
                Cardinality::ZeroOrOne => ZERO_OR_ONE_SIGIL,
                Cardinality::ZeroOrMore => ZERO_OR_MORE_SIGIL,
                Cardinality::OneOrMore => ONE_OR_MORE_SIGIL,
                Cardinality::Rest => ZERO_OR_MORE_SIGIL,
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
    ret_type: ValueType,
    param_types: Vec<ParamType>,
}

impl MacroType {
    pub fn new<P>(ret_type: ValueType, param_types: P) -> Self
    where
        P: IntoIterator<Item = ParamType>,
    {
        Self {
            ret_type,
            param_types: param_types.into_iter().collect(),
        }
    }
}

impl<P> From<(ValueType, P)> for MacroType
where
    P: IntoIterator<Item = ParamType>,
{
    fn from(value: (ValueType, P)) -> Self {
        let (ret_type, param_types) = value;
        Self::new(ret_type, param_types)
    }
}

impl Display for MacroType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "(")?;
        for (i, param) in self.param_types.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", param)?;
        }
        write!(f, ")")?;
        write!(f, " => {}", self.ret_type)
    }
}

/// Basic value types.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum ValueType {
    Union(UnionType),
    Tagged(IonType),
    Untagged(IonType),
    Fixed(FixedType),
}

impl Display for ValueType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ValueType::Union(t) => write!(f, "{}", t),
            ValueType::Tagged(t) => write!(f, "{}", t),
            ValueType::Untagged(t) => write!(f, "{} {}", UNTAGGED, t),
            ValueType::Fixed(t) => write!(f, "{}", t),
        }
    }
}

/// Static types for the Ion macro system.
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum StaticType {
    Value(ValueType),
    Macro(Box<MacroType>),
}

impl Display for StaticType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            StaticType::Value(t) => write!(f, "{}", t),
            StaticType::Macro(t) => write!(f, "{}", t),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::macros::types::MacroType;
    use crate::{IonResult, IonType};
    use rstest::rstest;

    #[rstest]
    #[case("() => int", (ValueType::Tagged(IonType::Int), []).into())]
    fn test_macro_type_display(
        #[case] expected: &str,
        #[case] macro_type: MacroType,
    ) -> IonResult<()> {
        assert_eq!(expected, format!("{}", macro_type).as_str());
        Ok(())
    }
}
