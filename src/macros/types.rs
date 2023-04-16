// Copyright Amazon.com, Inc. or its affiliates.

//! Static type support for Ion macros.
//!
//! This goes above the runtime type system of Ion within the macro system.

use std::fmt::{Display, Formatter};

use crate::macros::constants::syntax::*;
use crate::result::illegal_operation;
use crate::{IonResult, IonType};

// XXX this trait is here to allow us to parse generically from anything referencable as a &[u8]
//     we cannot do this with TryFrom
// TODO evaluate if this should even be here...

/// Generically parse from anything that can be represented as `&str`.
pub trait ParseStr
where
    Self: Sized,
{
    /// Parse the given `&str` reference into this type.
    fn parse_str<S>(as_str: S) -> IonResult<Self>
    where
        S: AsRef<str>;
}

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

impl ParseStr for FixedType {
    fn parse_str<S>(as_str: S) -> IonResult<Self>
    where
        S: AsRef<str>,
    {
        use FixedType::*;
        let text = as_str.as_ref();
        match text {
            UINT8 => Ok(UInt8),
            UINT16 => Ok(UInt16),
            UINT32 => Ok(UInt32),
            UINT64 => Ok(UInt64),
            INT8 => Ok(Int8),
            INT16 => Ok(Int16),
            INT32 => Ok(Int32),
            INT64 => Ok(Int64),
            FLOAT16 => Ok(Float16),
            FLOAT32 => Ok(Float32),
            FLOAT64 => Ok(Float64),
            _ => illegal_operation(format!("'{}' is not a fixed type", text)),
        }
    }
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

impl ParseStr for UnionType {
    fn parse_str<S>(as_str: S) -> IonResult<Self>
    where
        S: AsRef<str>,
    {
        use UnionType::*;
        let text = as_str.as_ref();
        match text {
            ANY => Ok(Any),
            NUMBER => Ok(Number),
            EXACT => Ok(Exact),
            TEXT => Ok(Text),
            LOB => Ok(Lob),
            SEQUENCE => Ok(Sequence),
            _ => illegal_operation(format!("'{}' is not a union type", text)),
        }
    }
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

/// Cardinality of values for a macro parameter.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum Cardinality {
    ExactlyOne,
    ZeroOrOne,
    ZeroOrMore,
    OneOrMore,
}

impl ParseStr for Cardinality {
    fn parse_str<S>(as_str: S) -> IonResult<Self>
    where
        S: AsRef<str>,
    {
        use Cardinality::*;
        let text = as_str.as_ref();
        match text {
            EXACTLY_ONE_SIGIL => Ok(ExactlyOne),
            ZERO_OR_ONE_SIGIL => Ok(ZeroOrOne),
            ZERO_OR_MORE_SIGIL => Ok(ZeroOrMore),
            ONE_OR_MORE_SIGIL => Ok(OneOrMore),
            _ => illegal_operation(format!("'{}' is not a cardinality", text)),
        }
    }
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
            }
        )
    }
}

/// Cardinality of arguments for a macro parameter.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum ArgCardinality {
    Common(Cardinality),
    Rest,
}

impl ArgCardinality {
    /// Returns the common [`Cardinality`] of this argument cardinality.
    /// [`ArgCardinality::Rest`] is lowered into [`Cardinality::ZeroOrMore`]
    fn cardinality(self) -> Cardinality {
        match self {
            ArgCardinality::Common(c) => c,
            ArgCardinality::Rest => Cardinality::ZeroOrMore,
        }
    }
}

impl From<Cardinality> for ArgCardinality {
    fn from(value: Cardinality) -> Self {
        Self::Common(value)
    }
}

impl Display for ArgCardinality {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ArgCardinality::Common(c) => write!(f, "{}", c),
            ArgCardinality::Rest => write!(f, "{}", REST_SIGIL),
        }
    }
}

/// The signature of a single parameter of a macro.
///
/// Models the _argument cardinality_ and type--what types of sub-expressions are allowed in the
/// argument position for the parameter and how many are allowed at that position.  Also models
/// the _value cardinality_ and type--which are the value types of values that the argument(s)
/// must evaluate to and the number of values.
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct ParamType {
    arg_type: Box<StaticType>,
    arg_cardinality: ArgCardinality,
    val_type: Box<ValueType>,
    val_cardinality: Cardinality,
}

impl Display for ParamType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match (
            &*self.arg_type,
            self.arg_cardinality,
            &*self.val_type,
            self.val_cardinality,
        ) {
            (StaticType::Value(arg_type), ArgCardinality::Common(arg_card), val_type, val_card)
                if *arg_type == *val_type && arg_card == val_card =>
            {
                write!(f, "{}{}", arg_type, arg_card)
            }
            (arg_type, arg_card, val_type, val_card) => {
                write!(f, "{}{} -> {}{}", arg_type, arg_card, val_type, val_card)
            }
        }
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
        write!(f, " -> {}", self.ret_type)
    }
}

// TODO add tagless if/when we sort out the details

/// Basic value types.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum ValueType {
    Union(UnionType),
    Arbitrary(IonType),
    Fixed(FixedType),
}

impl Display for ValueType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ValueType::Union(t) => write!(f, "{}", t),
            ValueType::Arbitrary(t) => write!(f, "{}", t),
            ValueType::Fixed(t) => write!(f, "{}", t),
        }
    }
}

/// Static types for the Ion macro system.
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum StaticType {
    /// A regular value type.
    Value(ValueType),
    /// A macro-shaped type.
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
    use rstest::rstest;
    use std::fmt::Debug;

    use crate::{IonResult, IonType};

    use super::Cardinality::*;
    use super::FixedType::*;
    use super::UnionType::*;
    use super::*;

    #[rstest]
    #[case::uint8("uint8", UInt8)]
    #[case::uint16("uint16", UInt16)]
    #[case::uint32("uint32", UInt32)]
    #[case::uint64("uint64", UInt64)]
    #[case::int8("int8", Int8)]
    #[case::int16("int16", Int16)]
    #[case::int32("int32", Int32)]
    #[case::int64("int64", Int64)]
    #[case::float16("float16", Float16)]
    #[case::float32("float32", Float32)]
    #[case::float64("float64", Float64)]
    #[case::any("any", Any)]
    #[case::number("number", Number)]
    #[case::exact("exact", Exact)]
    #[case::text("text", Text)]
    #[case::lob("lob", Lob)]
    #[case::any("sequence", Sequence)]
    #[case::exactly_one("!", ExactlyOne)]
    #[case::zero_or_one("?", ZeroOrOne)]
    #[case::zero_or_more("*", ZeroOrMore)]
    #[case::one_or_more("+", OneOrMore)]
    fn test_type_parsing<T>(#[case] text: &str, #[case] expected_type: T) -> IonResult<()>
    where
        T: ParseStr + PartialEq + Debug + Display,
    {
        let actual_type = T::parse_str(text)?;
        assert_eq!(expected_type, actual_type);
        assert_eq!(text, format!("{}", actual_type).as_str());
        Ok(())
    }

    fn assert_invalid_parse<S, T>(bad_text: S)
    where
        S: AsRef<str>,
        T: ParseStr + PartialEq + Debug + Display,
    {
        match T::parse_str(bad_text) {
            Ok(t) => panic!("Parsed invalid string as {}", t),
            Err(_) => (),
        }
    }

    #[rstest]
    #[case::bad_case("Int8")]
    #[case::foobar("foobar")]
    #[case::any("any")]
    #[case::float8("float8")]
    fn test_fixed_type_invalid(#[case] bad_text: &str) {
        assert_invalid_parse::<_, FixedType>(bad_text)
    }

    #[rstest]
    #[case::bad_case("ANY")]
    #[case::foobar("foobar")]
    #[case::int32("int32")]
    #[case::inexact("inexact")]
    fn test_union_type_invalid(#[case] bad_text: &str) {
        assert_invalid_parse::<_, UnionType>(bad_text)
    }

    #[rstest]
    #[case::bangbang("!!")]
    #[case::at("@")]
    #[case::foobar("foobar")]
    #[case::int32("int32")]
    #[case::inexact("any")]
    fn test_cardinality_invalid(#[case] bad_text: &str) {
        assert_invalid_parse::<_, Cardinality>(bad_text)
    }

    #[rstest]
    #[case("() -> int", (ValueType::Arbitrary(IonType::Int), []).into())]
    fn test_macro_type_display(
        #[case] expected: &str,
        #[case] macro_type: MacroType,
    ) -> IonResult<()> {
        assert_eq!(expected, format!("{}", macro_type).as_str());
        Ok(())
    }
}
