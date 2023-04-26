// Copyright Amazon.com, Inc. or its affiliates.

//! Provides a simple stream API bi-directionally over [`IonReader`](crate::IonReader).
//!
//! Conceptually [`TokenStream`] can be thought of as a continuation of the computation of
//! an Ion data stream.  This is useful for composing and transforming over streams of Ion data.
//!
//! It pulls in parts of the [element crate](crate::element) API to make it easier to work
//! with values without pulling in fully materializing the tree.

use crate::element::{Annotations, Bytes, Value};
use crate::result::illegal_operation;
use crate::text::text_formatter::IonValueFormatter;
use crate::thunk::{Thunk, ThunkState};
use crate::{Decimal, Int, IonError, IonResult, IonType, Str, Symbol, Timestamp};
use std::fmt::{Display, Formatter};

pub(crate) mod reader_stream;
pub(crate) mod stream_reader;

/// Generic display for anything that could be converted to `IonType`.
fn display_type<T>(value: T, f: &mut Formatter<'_>) -> std::fmt::Result
where
    T: Into<IonType>,
{
    let ion_type: IonType = value.into();
    write!(f, "{}", ion_type)
}

/// Subset of [`IonType`] that are strictly the non-null, non-container types.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum ScalarType {
    Bool,
    Int,
    Float,
    Decimal,
    Timestamp,
    String,
    Symbol,
    Blob,
    Clob,
}

impl Display for ScalarType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        display_type(*self, f)
    }
}

impl TryFrom<IonType> for ScalarType {
    type Error = IonError;

    fn try_from(value: IonType) -> Result<Self, Self::Error> {
        use ScalarType::*;
        match value {
            IonType::Bool => Ok(Bool),
            IonType::Int => Ok(Int),
            IonType::Float => Ok(Float),
            IonType::Decimal => Ok(Decimal),
            IonType::Timestamp => Ok(Timestamp),
            IonType::String => Ok(String),
            IonType::Symbol => Ok(Symbol),
            IonType::Blob => Ok(Blob),
            IonType::Clob => Ok(Clob),
            _ => illegal_operation(format!("{} type is not a scalar", value)),
        }
    }
}

impl<T> From<T> for ScalarType
where
    T: AsRef<ScalarValue>,
{
    fn from(value: T) -> Self {
        use ScalarType::*;
        match value.as_ref() {
            ScalarValue::Bool(_) => Bool,
            ScalarValue::Int(_) => Int,
            ScalarValue::Float(_) => Float,
            ScalarValue::Decimal(_) => Decimal,
            ScalarValue::Timestamp(_) => Timestamp,
            ScalarValue::String(_) => String,
            ScalarValue::Symbol(_) => Symbol,
            ScalarValue::Blob(_) => Blob,
            ScalarValue::Clob(_) => Clob,
        }
    }
}

/// Subset of [`IonType`] that are strictly the container types.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum ContainerType {
    SExp,
    List,
    Struct,
}

impl TryFrom<IonType> for ContainerType {
    type Error = IonError;

    fn try_from(value: IonType) -> Result<Self, Self::Error> {
        use ContainerType::*;
        match value {
            IonType::SExp => Ok(SExp),
            IonType::List => Ok(List),
            IonType::Struct => Ok(Struct),
            _ => illegal_operation(format!("{} type is not a container", value)),
        }
    }
}

impl Display for ContainerType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        display_type(*self, f)
    }
}

// XXX not really happy about the copy/paste/delete for this...
//     If Value was factored as scalar/collection that would've been nice

/// Subset of [`Value`] that is restricted to non-container, non-null types.
#[derive(Debug, Clone, PartialEq)]
pub enum ScalarValue {
    Bool(bool),
    Int(Int),
    Float(f64),
    Decimal(Decimal),
    Timestamp(Timestamp),
    String(Str),
    Symbol(Symbol),
    Blob(Bytes),
    Clob(Bytes),
}

impl ScalarValue {
    /// Returns the [`ScalarType`] of this value.
    pub fn scalar_type(&self) -> ScalarType {
        match self {
            ScalarValue::Bool(_) => ScalarType::Bool,
            ScalarValue::Int(_) => ScalarType::Int,
            ScalarValue::Float(_) => ScalarType::Float,
            ScalarValue::Decimal(_) => ScalarType::Decimal,
            ScalarValue::Timestamp(_) => ScalarType::Timestamp,
            ScalarValue::String(_) => ScalarType::String,
            ScalarValue::Symbol(_) => ScalarType::Symbol,
            ScalarValue::Blob(_) => ScalarType::Blob,
            ScalarValue::Clob(_) => ScalarType::Clob,
        }
    }
}

impl TryFrom<Value> for ScalarValue {
    type Error = IonError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        use ScalarValue::*;
        match value {
            Value::Null(_) => illegal_operation("Null is not a scalar value"),
            Value::Bool(bool) => Ok(Bool(bool)),
            Value::Int(int) => Ok(Int(int)),
            Value::Float(float) => Ok(Float(float)),
            Value::Decimal(decimal) => Ok(Decimal(decimal)),
            Value::Timestamp(timestamp) => Ok(Timestamp(timestamp)),
            Value::String(text) => Ok(String(text)),
            Value::Symbol(symbol) => Ok(Symbol(symbol)),
            Value::Blob(bytes) => Ok(Blob(bytes)),
            Value::Clob(bytes) => Ok(Clob(bytes)),
            Value::SExp(_) => illegal_operation("SExp is not a scalar value"),
            Value::List(_) => illegal_operation("List is not a scalar value"),
            Value::Struct(_) => illegal_operation("Struct is not a scalar value"),
        }
    }
}

impl Display for ScalarValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use ScalarValue::*;
        let mut ivf = IonValueFormatter { output: f };
        match self {
            Bool(bool) => ivf.format_bool(*bool),
            Int(int) => ivf.format_integer(int),
            Float(float) => ivf.format_float(*float),
            Decimal(decimal) => ivf.format_decimal(decimal),
            Timestamp(timestamp) => ivf.format_timestamp(timestamp),
            String(text) => ivf.format_string(text),
            Symbol(symbol) => ivf.format_symbol(symbol),
            Blob(bytes) => ivf.format_blob(bytes),
            Clob(bytes) => ivf.format_clob(bytes),
        }
        .map_err(|_| std::fmt::Error)?;
        Ok(())
    }
}

// XXX ideally we'd have our annotations return an borrowing iterator...
/// Deferred computation of annotations.
pub type AnnotationsThunk<'a> = Thunk<'a, Annotations>;

/// Deferred computation of a field name. [`Option`] is used here to denote lack of field versus
/// and error parsing the field.
pub type FieldNameThunk<'a> = Thunk<'a, Option<Symbol>>;

// XXX note that we're "stuttering" on the tag of the union here because we need the type before
//     we evaluate the data.
// XXX there is a sharp edge here that the types have to align, so we do not expose it as public
// TODO consider if it is worth modeling the thunk side value as an untagged union
/// Deferred computation of a non-null, non-container value.
#[derive(Debug)]
pub struct ScalarThunk<'a>(pub(crate) ScalarType, pub(crate) Thunk<'a, ScalarValue>);

impl<'a> ScalarThunk<'a> {
    /// Evaluates the thunk, consuming it and returning the underlying value.
    pub fn evaluate(self) -> IonResult<ScalarValue> {
        self.1.evaluate()
    }

    /// Evaluates the deferred value and returns it as a thunk.
    /// See [`Thunk::materialize`] for details.
    pub fn materialize(self) -> IonResult<ScalarThunk<'static>> {
        Ok(ScalarThunk(self.0, self.1.materialize()?))
    }

    /// In-place materialization of the thunk.
    /// See [`Thunk::memoize`] for details.
    pub fn memoize(&mut self) -> IonResult<&ScalarValue> {
        self.1.memoize()
    }

    /// Evaluates the ccurrent values and moves it out of the value without materializing.
    /// See [`Thunk::no_memoize`] for details
    pub fn no_memoize(&mut self) -> IonResult<ScalarValue> {
        self.1.no_memoize()
    }

    /// Returns the current thunk state.
    pub fn thunk_state(&self) -> ThunkState {
        self.1.thunk_state()
    }

    /// Returns the associated [`ScalarType`] for this thunk.
    pub fn scalar_type(&self) -> ScalarType {
        self.0
    }
}

// TODO consider if we should implement Clone for Content/Token (forcing materialization)

/// Represents the content of a token within the stream.
///
/// The content may be deferred if it is a scalar value (non-null, non-container),
/// and containers are represented as two content items, their start and end.
#[derive(Debug)]
pub enum Content<'a> {
    Null(IonType),
    Scalar(ScalarThunk<'a>),
    StartContainer(ContainerType),
    EndContainer(ContainerType),
    EndStream,
}

impl<'a> Content<'a> {
    /// Consumes this content to one that owns its content.
    /// See [`Thunk::materialize`] for details.
    pub fn materialize(self) -> IonResult<Content<'static>> {
        use Content::*;
        Ok(match self {
            Null(ion_type) => Null(ion_type),
            Scalar(thunk) => Scalar(thunk.materialize()?),
            StartContainer(container_type) => StartContainer(container_type),
            EndContainer(container_type) => EndContainer(container_type),
            EndStream => EndStream,
        })
    }

    /// In-place materialization of this content returning a reference to the underlying scalar
    /// value if applicable.
    /// See [`Thunk::memoize`] for details.
    pub fn memoize_scalar(&mut self) -> IonResult<Option<&ScalarValue>> {
        if let Content::Scalar(thunk) = self {
            Ok(Some(thunk.memoize()?))
        } else {
            Ok(None)
        }
    }

    /// In-place evaluation without memoization of this content returning the value of the underlying
    /// scalar if applicable.  Will clone if this is backed as a materialized value.
    /// See [`Thunk::no_memoize`] for details.
    pub fn no_memoize_scalar(&mut self) -> IonResult<Option<ScalarValue>> {
        if let Content::Scalar(thunk) = self {
            Ok(Some(thunk.no_memoize()?))
        } else {
            Ok(None)
        }
    }

    /// Indicates if this content is a null value and its corresponding type.
    pub fn null(&self) -> Option<IonType> {
        match self {
            Content::Null(ion_type) => Some(*ion_type),
            _ => None,
        }
    }

    /// Indicates if this content is a scalar value (that may be deferred) and the corresponding type.
    pub fn scalar(&self) -> Option<ScalarType> {
        match self {
            Content::Scalar(thunk) => Some(thunk.scalar_type()),
            _ => None,
        }
    }

    /// Indicates if this content is a start of a container and what type it is.
    pub fn start_container(&self) -> Option<ContainerType> {
        match self {
            Content::StartContainer(container_type) => Some(*container_type),
            Content::EndContainer(_) => None,
            _ => None,
        }
    }

    /// Indicates if this content is an end of a container and what type it is.
    pub fn end_container(&self) -> Option<ContainerType> {
        use Content::*;
        match self {
            StartContainer(_) => None,
            EndContainer(container_type) => Some(*container_type),
            _ => None,
        }
    }

    /// Indicates if this content  is the end of a stream.
    pub fn is_end_stream(&self) -> bool {
        matches!(self, Content::EndStream)
    }
}

impl From<ScalarValue> for Content<'static> {
    fn from(value: ScalarValue) -> Self {
        let scalar_type = value.scalar_type();
        let scalar_thunk = ScalarThunk(scalar_type, Thunk::wrap(value));
        Content::Scalar(scalar_thunk)
    }
}

impl<'a> From<ScalarThunk<'a>> for Content<'a> {
    fn from(scalar_thunk: ScalarThunk<'a>) -> Self {
        Content::Scalar(scalar_thunk)
    }
}

/// A token decorated with annotations and a field name (which could be empty or inapplicable).
#[derive(Debug)]
pub struct Token<'a> {
    annotations: AnnotationsThunk<'a>,
    field_name: FieldNameThunk<'a>,
    content: Content<'a>,
}

impl<'a> Token<'a> {
    pub fn new(
        annotations: AnnotationsThunk<'a>,
        field_name: FieldNameThunk<'a>,
        content: Content<'a>,
    ) -> Self {
        Self {
            annotations,
            field_name,
            content,
        }
    }

    /// Destructures this token into its constituent components.
    ///
    /// This is generally the API which one would use to "extract" the token.
    pub fn into_inner(self) -> (AnnotationsThunk<'a>, FieldNameThunk<'a>, Content<'a>) {
        (self.annotations, self.field_name, self.content)
    }

    /// Consumes and decorates this token with a field name.
    pub fn with_field_name(self, field_name: FieldNameThunk<'a>) -> Self {
        Self::new(self.annotations, field_name, self.content)
    }

    /// Consumes and decorates this token with annotations.
    pub fn with_annotations(self, annotations: AnnotationsThunk<'a>) -> Self {
        Self::new(annotations, self.field_name, self.content)
    }

    /// Returns a reference of the underlying token for this decorated one.
    ///
    /// This is generally used to observe non-destructive information about a token.
    /// Specifically things like if it is a value/container delimiters/null.
    pub fn token(&self) -> &Content<'a> {
        &self.content
    }

    /// Returns a mutable reference to the underlying token for this decorated one.
    ///
    /// This is useful for in-place evaluation/materialization of the underlying value.
    pub fn token_mut(&mut self) -> &mut Content<'a> {
        &mut self.content
    }

    /// Consume this token into one that owns its content.
    pub fn materialize(self) -> IonResult<Token<'static>> {
        Ok(Token::<'static>::new(
            self.annotations.materialize()?,
            self.field_name.materialize()?,
            self.content.materialize()?,
        ))
    }

    // TODO fix this API to be a bit less awkward with returning a content reference...

    /// Materialize in-place. Similar to [`Thunk::memoize`] for all the content.
    pub fn memoize(&mut self) -> IonResult<(&Annotations, Option<&Symbol>, &Content)> {
        self.content.memoize_scalar()?;
        Ok((
            self.annotations.memoize()?,
            self.field_name.memoize()?.as_ref(),
            &mut self.content,
        ))
    }

    /// Materializes in place the field name and make it shared.
    ///
    /// This is useful when we need the field name to be callable over and over without producing
    /// a deep copy.
    pub fn share_field_name(&mut self) -> IonResult<Option<Symbol>> {
        match self.field_name.remove() {
            Ok(Some(symbol)) => {
                let new_symbol = symbol.into_shared();
                let _ = self.field_name.replace(Some(new_symbol.clone()));
                Ok(Some(new_symbol))
            }
            Ok(None) => Ok(None),
            Err(e) => Err(e),
        }
    }
}

impl<'a> From<Content<'a>> for Token<'a> {
    fn from(value: Content<'a>) -> Self {
        Token::new(Thunk::wrap(Annotations::empty()), Thunk::wrap(None), value)
    }
}

impl From<ScalarValue> for Token<'static> {
    fn from(value: ScalarValue) -> Self {
        Token::new(
            Thunk::wrap(Annotations::empty()),
            Thunk::wrap(None),
            value.into(),
        )
    }
}

/// Instruction for the token stream to advance it to the next event.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum Instruction {
    /// Advance to the next event.
    Next,
    /// Skip to the end of the current container.
    /// If within a container, will skip to the end of the container and return that event.
    /// If not within a container, this operation is invalid.
    NextEnd,
}

/// Provides an iterator-like API over Ion data as [`Token`].
pub trait TokenStream<'a> {
    /// Advances the stream to the next token.
    ///
    /// Note that the lifetime of the resulting token is not bound to the lifetime of the borrow
    /// in the method.  This is because it may be the case that the token needs to be used
    /// outside of this context, particularly if adapting a stream to an [`IonReader`][reader] where
    /// the borrow of [`next`][next] is disassociated from a `read_XXX` method, the
    /// [`field_name`][field_name] method, or the [`annotations`][annotations] method.
    ///
    /// Returns that token or an error if there is some problem with the underlying stream.
    ///
    /// [reader]: crate::IonReader
    /// [field_name]: crate::IonReader::field_name
    /// [next]: crate::IonReader::next
    /// [annotations]: crate::IonReader::annotations
    fn next_token(&mut self, instruction: Instruction) -> IonResult<Token<'a>>;
}

#[cfg(test)]
mod tests {
    use super::ContainerType::*;
    use super::ScalarValue::*;
    use super::*;
    use crate::{IonError, IonResult, IonType};
    use rstest::rstest;
    use std::fmt::Debug;

    /// An arbitrary timestamp as a filler for testing purposes.
    fn sample_timestamp() -> crate::Timestamp {
        crate::Timestamp::with_year(2023).build().unwrap()
    }

    #[rstest]
    #[case::cont_sexp(SExp, IonType::SExp)]
    #[case::cont_list(List, IonType::List)]
    #[case::cont_struct(Struct, IonType::Struct)]
    #[case::scalar_bool(Bool(false), Value::Bool(false))]
    #[case::scalar_int(Int(3.into()), Value::Int(3.into()))]
    #[case::scalar_float(Float(1.1), Value::Float(1.1))]
    #[case::scalar_decimal(Decimal(42.into()), Value::Decimal(42.into()))]
    #[case::scalar_timestamp(Timestamp(sample_timestamp()), Value::Timestamp(sample_timestamp()))]
    #[case::scalar_symbol(Symbol("foo".into()), Value::Symbol("foo".into()))]
    #[case::scalar_string(String("bar".into()), Value::String("bar".into()))]
    #[case::scalar_clob(Clob("hello".into()), Value::Clob("hello".into()))]
    #[case::scalar_blob(Blob("world".into()), Value::Blob("world".into()))]
    fn test_valid_conversion<F, T>(#[case] expected: T, #[case] from: F) -> IonResult<()>
    where
        T: TryFrom<F, Error = IonError> + Into<F> + PartialEq + Debug + Display,
        F: PartialEq + Debug + Display + Clone,
    {
        let from_clone = from.clone();
        let actual = from_clone.try_into()?;
        assert_eq!(expected, actual);
        assert_eq!(from, actual.into());

        Ok(())
    }

    fn test_invalid_conversion<F, T>(bad_from: F)
    where
        T: TryFrom<F, Error = IonError> + Into<F> + PartialEq + Debug + Display,
        F: PartialEq + Debug + Display + Clone,
    {
        let from_clone = bad_from.clone();
        if let Ok(t) = T::try_from(bad_from) {
            panic!("Unexpected conversion from {} to {}", from_clone, t);
        }
    }

    #[rstest]
    #[case::null(IonType::Null)]
    #[case::bool(IonType::Bool)]
    #[case::int(IonType::Int)]
    #[case::float(IonType::Float)]
    #[case::decimal(IonType::Decimal)]
    #[case::timestamp(IonType::Timestamp)]
    #[case::symbol(IonType::Symbol)]
    #[case::string(IonType::String)]
    #[case::clob(IonType::Clob)]
    #[case::blob(IonType::Blob)]
    fn test_invalid_container_type_conversion(#[case] bad_type: IonType) {
        test_invalid_conversion::<_, ContainerType>(bad_type)
    }

    /// An arbitrary empty struct for testing the wrapper types.
    fn empty_struct() -> crate::element::Struct {
        crate::element::Struct::builder().build()
    }

    // XXX note that struct is spelled strct to avoid keyword clash
    #[rstest]
    #[case::null(Value::Null(IonType::Null))]
    #[case::sexp(Value::SExp(vec![].into()))]
    #[case::list(Value::List(vec![].into()))]
    #[case::strct(Value::Struct(empty_struct()))]
    fn test_invalid_scalar_conversion(#[case] bad_value: Value) {
        test_invalid_conversion::<_, ScalarValue>(bad_value)
    }
}
