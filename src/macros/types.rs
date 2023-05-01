// Copyright Amazon.com, Inc. or its affiliates.

//! Static type support for Ion macros.
//!
//! This goes above the runtime type system of Ion within the macro system.

use crate::macros::constants::syntax::*;
use crate::result::illegal_operation;
use crate::{IonResult, IonType};
use std::fmt::{Display, Formatter};

// XXX this trait is here to allow us to parse generically from anything referencable as a &str
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

/// Macro types that are encoded using a low-level Ion encoding primitive
///
/// These types are structural constrained types over their general Ion equivalent.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum PrimitiveType {
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
    VarUInt,
    VarInt,
    VarStr,
    VarSym,
}

impl ParseStr for PrimitiveType {
    fn parse_str<S>(as_str: S) -> IonResult<Self>
    where
        S: AsRef<str>,
    {
        use PrimitiveType::*;
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
            VAR_UINT => Ok(VarUInt),
            VAR_INT => Ok(VarInt),
            VAR_STR => Ok(VarStr),
            VAR_SYM => Ok(VarSym),
            _ => illegal_operation(format!("'{}' is not a tagless type", text)),
        }
    }
}

impl Display for PrimitiveType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use PrimitiveType::*;
        write!(
            f,
            "{}",
            match self {
                UInt8 => UINT8,
                UInt16 => UINT16,
                UInt32 => UINT32,
                UInt64 => UINT64,
                Int8 => INT8,
                Int16 => INT16,
                Int32 => INT32,
                Int64 => INT64,
                Float16 => FLOAT16,
                Float32 => FLOAT32,
                Float64 => FLOAT64,
                VarUInt => VAR_UINT,
                VarInt => VAR_INT,
                VarStr => VAR_STR,
                VarSym => VAR_SYM,
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
        use UnionType::*;
        write!(
            f,
            "{}",
            match self {
                Any => ANY,
                Number => NUMBER,
                Exact => EXACT,
                Text => TEXT,
                Lob => LOB,
                Sequence => SEQUENCE,
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
        use Cardinality::*;
        write!(
            f,
            "{}",
            match self {
                ExactlyOne => EXACTLY_ONE_SIGIL,
                ZeroOrOne => ZERO_OR_ONE_SIGIL,
                ZeroOrMore => ZERO_OR_MORE_SIGIL,
                OneOrMore => ONE_OR_MORE_SIGIL,
            }
        )
    }
}

/// Indicates a normal parameter or *rest* parameter.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum ParameterMode {
    Normal,
    Rest,
}

/// The signature of a single parameter of a macro.
///
/// Models the _argument cardinality_ and type--what types of sub-expressions are allowed in the
/// argument position for the parameter and how many are allowed at that position.  Also models
/// the _stream cardinality_--which is the number of values a parameter must evaluate to.
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct ParamType {
    arg_type: StaticType,
    arg_cardinality: Cardinality,
    stream_cardinality: Cardinality,
    param_mode: ParameterMode,
}

impl ParamType {
    pub fn try_new(
        arg_type: StaticType,
        arg_cardinality: Cardinality,
        stream_cardinality: Cardinality,
        param_mode: ParameterMode,
    ) -> IonResult<Self> {
        use Cardinality::*;
        use ParameterMode::*;

        // validate mode/cardinalities
        match (param_mode, arg_cardinality, stream_cardinality) {
            (Normal, a_card, s_card) if a_card == s_card => {
                // ! ? * +
            }
            (Normal, ExactlyOne, ZeroOrMore) if arg_type.is_tagged() => {
                // !*
            }
            (Normal, ExactlyOne, OneOrMore) if arg_type.is_tagged() => {
                // !+
            }
            (Normal, ZeroOrOne, ZeroOrMore) if arg_type.is_tagged() => {
                // ?*
            }
            (Rest, ZeroOrMore, ZeroOrMore) => {
                // ...
            }
            (Normal, a_card, s_card) => {
                return illegal_operation(format!(
                    "Mismatched cardinalities for param type: {}{}",
                    a_card, s_card
                ))
            }
            (Rest, a_card, s_card) => {
                return illegal_operation(format!(
                    "Rest parameter must be * cardinality: {}{}",
                    a_card, s_card
                ))
            }
        }

        Ok(Self {
            arg_type,
            arg_cardinality,
            stream_cardinality,
            param_mode,
        })
    }
}

impl Display for ParamType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Cardinality::*;
        use ParameterMode::*;

        write!(f, "{}", self.arg_type)?;
        match (
            self.param_mode,
            self.arg_cardinality,
            self.stream_cardinality,
        ) {
            (Normal, a_card, s_card) if a_card == s_card => {
                write!(f, "{}", a_card)
            }
            (Normal, a_card, s_card) if a_card != s_card => {
                write!(f, "{}{}", a_card, s_card)
            }
            (Rest, ZeroOrMore, ZeroOrMore) => {
                write!(f, "{}", REST_SIGIL)
            }
            (_, _, _) => unreachable!(),
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

/// Basic value types.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum ValueType {
    Union(UnionType),
    Tagged(IonType),
    Primitive(PrimitiveType),
}

impl Display for ValueType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use ValueType::*;
        match self {
            Union(t) => write!(f, "{}", t),
            Tagged(t) => write!(f, "{}", t),
            Primitive(t) => write!(f, "{}", t),
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

impl StaticType {
    /// Determines if a type is self-described with a type tag or not.
    fn is_tagged(&self) -> bool {
        use StaticType::*;
        use ValueType::*;
        matches!(self, Value(Union(_) | Tagged(_)))
    }
}

impl Display for StaticType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use StaticType::*;
        match self {
            Value(t) => write!(f, "{}", t),
            Macro(t) => write!(f, "{}", t),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Cardinality::*;
    use super::PrimitiveType::*;
    use super::UnionType::*;
    use super::*;
    use crate::{IonResult, IonType};
    use rstest::rstest;
    use std::fmt::Debug;

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
    #[case::varuint("var_uint", VarUInt)]
    #[case::varint("var_int", VarInt)]
    #[case::varstr("var_str", VarStr)]
    #[case::varsym("var_sym", VarSym)]
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
        if let Ok(t) = T::parse_str(bad_text) {
            panic!("Parsed invalid string as {}", t)
        }
    }

    #[rstest]
    #[case::bad_case("Int8")]
    #[case::foobar("foobar")]
    #[case::any("any")]
    #[case::float8("float8")]
    fn test_tagless_type_invalid(#[case] bad_text: &str) {
        assert_invalid_parse::<_, PrimitiveType>(bad_text)
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
    #[case::rest("...")]
    fn test_cardinality_invalid(#[case] bad_text: &str) {
        assert_invalid_parse::<_, Cardinality>(bad_text)
    }

    #[rstest]
    #[case("() -> int", (ValueType::Tagged(IonType::Int), []).into())]
    fn test_macro_type_display(
        #[case] expected: &str,
        #[case] macro_type: MacroType,
    ) -> IonResult<()> {
        assert_eq!(expected, format!("{}", macro_type).as_str());
        Ok(())
    }
}
