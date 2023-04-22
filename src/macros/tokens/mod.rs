// Copyright Amazon.com, Inc. or its affiliates.

//! Provides a simple token-like, iterator API over [`IonReader`].
//!
//! This is useful for composing and transforming over streams and is used by the macro
//! system to operate on an Ion stream like a lexer.  It is intended to also be useful to compute
//! the Ion data stream from macro expansion.  Conceptually [`TokenSource`] can be thought of as
//! a continuation of the computation of an Ion data stream.
//!
//! It pulls in parts of the [element crate](crate::element) API to make it easier to work
//! with values without pulling in fully materializing the tree.

use crate::element::{Annotations, Bytes, Value};
use crate::macros::thunk::{Thunk, ThunkState};
use crate::result::illegal_operation;
use crate::text::text_formatter::IonValueFormatter;
use crate::{
    Decimal, Int, IonError, IonReader, IonResult, IonType, Str, StreamItem, Symbol, Timestamp,
};
use std::cell::RefCell;
use std::fmt::{Display, Formatter};
use std::marker::PhantomData;
use std::rc::Rc;

pub(crate) mod reader;

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

impl Into<IonType> for ScalarType {
    fn into(self) -> IonType {
        use ScalarType::*;
        match self {
            Bool => IonType::Bool,
            Int => IonType::Int,
            Float => IonType::Float,
            Decimal => IonType::Decimal,
            Timestamp => IonType::Timestamp,
            String => IonType::String,
            Symbol => IonType::Symbol,
            Blob => IonType::Blob,
            Clob => IonType::Clob,
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

impl Into<IonType> for ContainerType {
    fn into(self) -> IonType {
        use ContainerType::*;
        match self {
            SExp => IonType::SExp,
            List => IonType::List,
            Struct => IonType::Struct,
        }
    }
}

impl Display for ContainerType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let ion_type: IonType = (*self).into();
        write!(f, "{}", ion_type)
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
    pub fn materialize(self) -> IonResult<ScalarThunk<'static>> {
        Ok(ScalarThunk(self.0, self.1.materialize()?))
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

// TODO consider if we should implement Clone for Token/AnnotatedToken (forcing materialization)

/// Represents a token within the stream.
///
/// A token may be deferred if it is a scalar value (non-null, non-container), and containers are
/// represented as two tokens, their start and end.
#[derive(Debug)]
pub enum Token<'a> {
    Null(IonType),
    Scalar(ScalarThunk<'a>),
    StartContainer(ContainerType),
    EndContainer(ContainerType),
    EndStream,
}

impl<'a> Token<'a> {
    /// Consume this token to one that owns its content.
    pub fn materialize(self) -> IonResult<Token<'static>> {
        use Token::*;
        Ok(match self {
            Null(ion_type) => Null(ion_type),
            Scalar(thunk) => Scalar(thunk.materialize()?),
            StartContainer(container_type) => StartContainer(container_type),
            EndContainer(container_type) => EndContainer(container_type),
            EndStream => EndStream,
        })
    }

    /// Indicates if this token is a null value and its corresponding type.
    pub fn null(&self) -> Option<IonType> {
        match self {
            Token::Null(ion_type) => Some(*ion_type),
            _ => None,
        }
    }

    /// Indicates if this token is a scalar value (that may be deferred) and the corresponding type.
    pub fn scalar(&self) -> Option<ScalarType> {
        match self {
            Token::Scalar(thunk) => Some(thunk.scalar_type()),
            _ => None,
        }
    }

    /// Indicates if this token is a start of a container and what type it is.
    pub fn start_container(&self) -> Option<ContainerType> {
        match self {
            Token::StartContainer(container_type) => Some(*container_type),
            Token::EndContainer(_) => None,
            _ => None,
        }
    }

    /// Indicates if this token is an end of a container and what type it is.
    pub fn end_container(&self) -> Option<ContainerType> {
        use Token::*;
        match self {
            StartContainer(_) => None,
            EndContainer(container_type) => Some(*container_type),
            _ => None,
        }
    }

    /// Indicates if this token is the end of a stream.
    pub fn is_end_stream(&self) -> bool {
        matches!(self, Token::EndStream)
    }
}

impl From<ScalarValue> for Token<'static> {
    fn from(value: ScalarValue) -> Self {
        let scalar_type = value.scalar_type();
        let scalar_thunk = ScalarThunk(scalar_type, Thunk::wrap(value));
        Token::Scalar(scalar_thunk)
    }
}

impl<'a> From<ScalarThunk<'a>> for Token<'a> {
    fn from(scalar_thunk: ScalarThunk<'a>) -> Self {
        Token::Scalar(scalar_thunk)
    }
}

/// A token decorated with annotations and a field name (which could be empty or inapplicable).
#[derive(Debug)]
pub struct AnnotatedToken<'a> {
    annotations: AnnotationsThunk<'a>,
    field_name: FieldNameThunk<'a>,
    token: Token<'a>,
}

impl<'a> AnnotatedToken<'a> {
    pub fn new(
        annotations: AnnotationsThunk<'a>,
        field_name: FieldNameThunk<'a>,
        token: Token<'a>,
    ) -> Self {
        Self {
            annotations,
            field_name,
            token,
        }
    }

    /// Destructures this token into its constituent components.
    ///
    /// This is generally the API which one would use to "extract" the token.
    pub fn into_inner(self) -> (AnnotationsThunk<'a>, FieldNameThunk<'a>, Token<'a>) {
        (self.annotations, self.field_name, self.token)
    }

    /// Consumes and decorates this token with a field name.
    pub fn with_field_name(self, field_name: FieldNameThunk<'a>) -> Self {
        Self::new(self.annotations, field_name, self.token)
    }

    /// Consumes and decorates this token with annotations.
    pub fn with_annotations(self, annotations: AnnotationsThunk<'a>) -> Self {
        Self::new(annotations, self.field_name, self.token)
    }

    /// Returns a reference of the underlying token for this decorated one.
    ///
    /// This is generally used to observe non-destructive information about a token.
    /// Specifically things like if it is a value/container delimiters/null.
    pub fn token(&self) -> &Token<'a> {
        &self.token
    }

    /// Consume this annotated token into one that owns its content.
    pub fn materialize(self) -> IonResult<AnnotatedToken<'static>> {
        Ok(AnnotatedToken::<'static>::new(
            self.annotations.materialize()?,
            self.field_name.materialize()?,
            self.token.materialize()?,
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

impl<'a> From<Token<'a>> for AnnotatedToken<'a> {
    fn from(value: Token<'a>) -> Self {
        AnnotatedToken::new(Thunk::wrap(Annotations::empty()), Thunk::wrap(None), value)
    }
}

impl From<ScalarValue> for AnnotatedToken<'static> {
    fn from(value: ScalarValue) -> Self {
        AnnotatedToken::new(
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

/// Provides an iterator-like API over Ion data as [`AnnotatedToken`].
pub trait TokenSource {
    /// Advances the source to the next token.
    ///
    /// Returns that token or an error if there is some problem with the underlying stream.
    fn next_token(&mut self, instruction: Instruction) -> IonResult<AnnotatedToken>;
}

// TODO make this more generic with respect to other readers--the problem is Item/Symbol
// TODO this has to abstract over potentially system reader to implement macros

/// Adapter for a [`TokenSource`] over an arbitrary [`IonReader`]
struct ReaderTokenSource<'a, R>
where
    R: IonReader<Item = StreamItem, Symbol = Symbol> + 'a,
{
    // XXX this is so we can have multiple closures to lazily evaluate tokens
    reader_cell: Rc<RefCell<R>>,
    // XXX this allows us to explicitly capture a lifetime for the reader we operate on
    phantom: PhantomData<&'a R>,
}

impl<'a, R> ReaderTokenSource<'a, R>
where
    R: IonReader<Item = StreamItem, Symbol = Symbol> + 'a,
{
    #[inline]
    fn annotations_thunk(&self) -> AnnotationsThunk<'a> {
        let reader_cell = self.reader_cell.clone();
        Thunk::defer(move || reader_cell.borrow().annotations().collect())
    }

    #[inline]
    fn field_name_thunk(&self) -> FieldNameThunk<'a> {
        match self.parent_type() {
            Some(IonType::Struct) => {
                let reader_cell = self.reader_cell.clone();
                // XXX note that we expect a field name, so we do want that to surface as error
                //     and not None
                Thunk::defer(move || Ok(Some(reader_cell.borrow().field_name()?)))
            }
            _ => Thunk::wrap(None),
        }
    }

    #[inline]
    fn bool_token(&mut self) -> Token<'a> {
        let reader_cell = self.reader_cell.clone();
        ScalarThunk(
            ScalarType::Bool,
            Thunk::defer(move || {
                let mut reader = reader_cell.borrow_mut();
                Ok(ScalarValue::Bool(reader.read_bool()?))
            }),
        )
        .into()
    }

    #[inline]
    fn int_token(&mut self) -> Token<'a> {
        let reader_cell = self.reader_cell.clone();
        ScalarThunk(
            ScalarType::Int,
            Thunk::defer(move || {
                let mut reader = reader_cell.borrow_mut();
                Ok(ScalarValue::Int(reader.read_int()?))
            }),
        )
        .into()
    }

    #[inline]
    fn float_token(&mut self) -> Token<'a> {
        let reader_cell = self.reader_cell.clone();
        ScalarThunk(
            ScalarType::Float,
            Thunk::defer(move || {
                let mut reader = reader_cell.borrow_mut();
                Ok(ScalarValue::Float(reader.read_f64()?))
            }),
        )
        .into()
    }

    #[inline]
    fn decimal_token(&mut self) -> Token<'a> {
        let reader_cell = self.reader_cell.clone();
        ScalarThunk(
            ScalarType::Decimal,
            Thunk::defer(move || {
                let mut reader = reader_cell.borrow_mut();
                Ok(ScalarValue::Decimal(reader.read_decimal()?))
            }),
        )
        .into()
    }

    #[inline]
    fn timestamp_token(&mut self) -> Token<'a> {
        let reader_cell = self.reader_cell.clone();
        ScalarThunk(
            ScalarType::Timestamp,
            Thunk::defer(move || {
                let mut reader = reader_cell.borrow_mut();
                Ok(ScalarValue::Timestamp(reader.read_timestamp()?))
            }),
        )
        .into()
    }

    #[inline]
    fn string_token(&mut self) -> Token<'a> {
        let reader_cell = self.reader_cell.clone();
        ScalarThunk(
            ScalarType::String,
            Thunk::defer(move || {
                let mut reader = reader_cell.borrow_mut();
                Ok(ScalarValue::String(reader.read_string()?))
            }),
        )
        .into()
    }

    #[inline]
    fn symbol_token(&mut self) -> Token<'a> {
        let reader_cell = self.reader_cell.clone();
        ScalarThunk(
            ScalarType::Symbol,
            Thunk::defer(move || {
                let mut reader = reader_cell.borrow_mut();
                Ok(ScalarValue::Symbol(reader.read_symbol()?))
            }),
        )
        .into()
    }

    #[inline]
    fn blob_token(&mut self) -> Token<'a> {
        let reader_cell = self.reader_cell.clone();
        ScalarThunk(
            ScalarType::Blob,
            Thunk::defer(move || {
                let mut reader = reader_cell.borrow_mut();
                Ok(ScalarValue::Blob(reader.read_blob()?.into()))
            }),
        )
        .into()
    }

    #[inline]
    fn clob_token(&mut self) -> Token<'a> {
        let reader_cell = self.reader_cell.clone();
        ScalarThunk(
            ScalarType::Clob,
            Thunk::defer(move || {
                let mut reader = reader_cell.borrow_mut();
                Ok(ScalarValue::Clob(reader.read_clob()?.into()))
            }),
        )
        .into()
    }

    #[inline]
    fn next(&mut self) -> IonResult<StreamItem> {
        let mut reader = self.reader_cell.borrow_mut();
        reader.next()
    }

    #[inline]
    fn step_in(&mut self) -> IonResult<()> {
        let mut reader = self.reader_cell.borrow_mut();
        reader.step_in()
    }

    #[inline]
    fn step_out(&mut self) -> IonResult<()> {
        let mut reader = self.reader_cell.borrow_mut();
        reader.step_out()
    }

    #[inline]
    fn is_null(&self) -> bool {
        let reader = self.reader_cell.borrow();
        reader.is_null()
    }

    #[inline]
    fn ion_type(&self) -> Option<IonType> {
        let reader = self.reader_cell.borrow();
        reader.ion_type()
    }

    #[inline]
    fn parent_type(&self) -> Option<IonType> {
        let reader = self.reader_cell.borrow();
        reader.parent_type()
    }
}

impl<'a, R> TokenSource for ReaderTokenSource<'a, R>
where
    R: IonReader<Item = StreamItem, Symbol = Symbol> + 'a,
{
    fn next_token(&mut self, instruction: Instruction) -> IonResult<AnnotatedToken> {
        use Instruction::*;

        Ok(match instruction {
            Next => {
                let item = self.next()?;
                match item {
                    StreamItem::Value(ion_type) | StreamItem::Null(ion_type) => {
                        let annotations_thunk = self.annotations_thunk();
                        let field_name_thunk = self.field_name_thunk();
                        let token = if self.is_null() {
                            Token::Null(ion_type)
                        } else {
                            match self.ion_type() {
                                None => illegal_operation("No type for value from reader")?,
                                Some(IonType::Null) => {
                                    illegal_operation("Null type for value from reader")?
                                }
                                Some(IonType::Bool) => self.bool_token(),
                                Some(IonType::Int) => self.int_token(),
                                Some(IonType::Float) => self.float_token(),
                                Some(IonType::Decimal) => self.decimal_token(),
                                Some(IonType::Timestamp) => self.timestamp_token(),
                                Some(IonType::Symbol) => self.symbol_token(),
                                Some(IonType::String) => self.string_token(),
                                Some(IonType::Clob) => self.clob_token(),
                                Some(IonType::Blob) => self.blob_token(),
                                Some(IonType::List) => {
                                    self.step_in()?;
                                    Token::StartContainer(ContainerType::List)
                                }
                                Some(IonType::SExp) => {
                                    self.step_in()?;
                                    Token::StartContainer(ContainerType::SExp)
                                }
                                Some(IonType::Struct) => {
                                    self.step_in()?;
                                    Token::StartContainer(ContainerType::Struct)
                                }
                            }
                        };
                        AnnotatedToken::new(annotations_thunk, field_name_thunk, token)
                    }
                    StreamItem::Nothing => match self.parent_type() {
                        None => Token::EndStream.into(),
                        Some(IonType::SExp) => {
                            self.step_out()?;
                            Token::EndContainer(ContainerType::SExp).into()
                        }
                        Some(IonType::List) => {
                            self.step_out()?;
                            Token::EndContainer(ContainerType::List).into()
                        }
                        Some(IonType::Struct) => {
                            self.step_out()?;
                            Token::EndContainer(ContainerType::Struct).into()
                        }
                        Some(ion_type) => illegal_operation(format!(
                            "Unexpected non-container type: {}",
                            ion_type
                        ))?,
                    },
                }
            }
            NextEnd => match self.parent_type() {
                None => illegal_operation("Cannot skip to next end at top-level")?,
                Some(ion_type) => match ion_type {
                    IonType::List => {
                        self.step_out()?;
                        Token::EndContainer(ContainerType::List)
                    }
                    IonType::SExp => {
                        self.step_out()?;
                        Token::EndContainer(ContainerType::SExp)
                    }
                    IonType::Struct => {
                        self.step_out()?;
                        Token::EndContainer(ContainerType::Struct)
                    }
                    _ => illegal_operation(format!("Unexpected container type: {}", ion_type))?,
                },
            }
            .into(),
        })
    }
}

impl<'a, R> From<R> for ReaderTokenSource<'a, R>
where
    R: IonReader<Item = StreamItem, Symbol = Symbol> + 'a,
{
    fn from(value: R) -> Self {
        ReaderTokenSource {
            reader_cell: Rc::new(RefCell::new(value)),
            phantom: Default::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::ContainerType::*;
    use super::Instruction::*;
    use super::ScalarValue::*;
    use super::*;
    use crate::data_source::ToIonDataSource;
    use crate::element::{Blob as ElemBlob, Clob as ElemClob};
    use crate::result::illegal_operation_raw;
    use crate::{Decimal, IonError, IonResult, IonType, ReaderBuilder, Symbol};
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

    type Src = (Instruction, AnnotatedToken<'static>);
    type Srcs = Vec<Src>;

    fn single_src<T>(value: T) -> IonResult<Srcs>
    where
        T: Into<Value>,
    {
        let value = value.into();
        let scalar_value: ScalarValue = value.try_into()?;

        Ok(vec![(Next, scalar_value.into())])
    }

    fn container_src(container_type: ContainerType, contents: IonResult<Srcs>) -> IonResult<Srcs> {
        let mut srcs = vec![];
        srcs.push((Next, Token::StartContainer(container_type).into()));
        srcs.append(&mut contents?);
        srcs.push((Next, Token::EndContainer(container_type).into()));
        Ok(srcs)
    }

    fn container_skip_src(
        container_type: ContainerType,
        contents: IonResult<Srcs>,
    ) -> IonResult<Srcs> {
        last_next_end(container_src(container_type, contents))
    }

    fn last_next_end(contents: IonResult<Srcs>) -> IonResult<Srcs> {
        let mut srcs = contents?;
        let (_, annotated_token) = srcs
            .pop()
            .ok_or(illegal_operation_raw("No last element in source to change"))?;
        srcs.push((NextEnd, annotated_token));
        Ok(srcs)
    }

    fn field_named_srcs<C, I, S>(names: C, srcs: IonResult<Srcs>) -> IonResult<Srcs>
    where
        C: IntoIterator<Item = S, IntoIter = I>,
        I: Iterator<Item = S>,
        S: AsRef<str>,
    {
        names
            .into_iter()
            .zip(srcs?.into_iter())
            .map(|(name, (insn, a_tok))| {
                Ok((
                    insn,
                    a_tok.with_field_name(Thunk::wrap(Some(name.as_ref().into()))),
                ))
            })
            .collect()
    }

    fn annotate_first_srcs<C, I, S>(annotations: C, srcs_res: IonResult<Srcs>) -> IonResult<Srcs>
    where
        C: IntoIterator<Item = S, IntoIter = I>,
        I: Iterator<Item = S>,
        S: AsRef<str>,
    {
        let mut srcs = srcs_res?;
        if srcs.len() == 0 {
            return illegal_operation("Cannot annotated empty");
        }

        // not exactly efficient, but that's fine here
        let (instruction, mut annotated_token) = srcs.remove(0);
        let annotations: Vec<Symbol> = annotations.into_iter().map(|s| s.as_ref().into()).collect();
        annotated_token = annotated_token.with_annotations(Thunk::wrap(annotations.into()));
        srcs.insert(0, (instruction, annotated_token));

        Ok(srcs)
    }

    fn singleton_struct_src() -> IonResult<Srcs> {
        container_src(Struct, field_named_srcs(["a"], single_src(5)))
    }

    #[rstest]
    #[case::bool(single_src(false), "false")]
    #[case::int(single_src(5), "5")]
    #[case::float(single_src(5.0), "5e0")]
    #[case::decimal(single_src(Decimal::from(50)), "50.")]
    #[case::timestamp(single_src(sample_timestamp()), "2023T")]
    #[case::string(single_src("hello"), "'''hello'''")]
    #[case::symbol(single_src(Symbol::from("world")), "world")]
    #[case::blob(single_src(ElemBlob::from("foo".as_bytes())), "{{ Zm9v }}")]
    #[case::clob(single_src(ElemClob::from("bar".as_bytes())), "{{'''bar'''}}")]
    #[case::singleton_list(container_src(ContainerType::List, single_src(false)), "[false]")]
    #[case::singleton_sexp(container_src(ContainerType::SExp, single_src(1.0)), "(1e0)")]
    #[case::singleton_struct(singleton_struct_src(), "{a:5}")]
    #[case::empty_list(container_src(ContainerType::List, Ok(vec![])), "[]")]
    #[case::empty_sexp(container_src(ContainerType::SExp, Ok(vec![])), "()")]
    #[case::empty_struct(container_src(ContainerType::Struct, Ok(vec![])), "{}")]
    #[case::list_skip_start(container_skip_src(ContainerType::List, Ok(vec![])), "[1, 2, 3, 4, 5]")]
    #[case::sexp_skip_start(container_skip_src(ContainerType::SExp, Ok(vec![])), "(a b c d e f)")]
    #[case::struct_skip_start(container_skip_src(ContainerType::Struct, Ok(vec![])), "{a:1, b:2}")]
    #[case::list_skip_second(
        container_skip_src(ContainerType::List, single_src(1)),
        "[1, 2, 3, 4, 5]"
    )]
    #[case::sexp_skip_second(
        container_skip_src(ContainerType::SExp, single_src(Symbol::from("a"))),
        "(a b c d e f)"
    )]
    #[case::struct_skip_second(last_next_end(singleton_struct_src()), "{a:5, b:6, c:7}")]
    #[case::annotated(annotate_first_srcs(["a", "b", "c"], single_src(false)), "a::b::c::false")]
    fn source_test<S>(#[case] expected: IonResult<Srcs>, #[case] data: S) -> IonResult<()>
    where
        S: ToIonDataSource,
    {
        use Token::*;
        let mut expected_src = expected?;
        // add the terminator
        expected_src.push((Next, EndStream.into()));
        let expected_count = expected_src.len();

        let reader = ReaderBuilder::new().build(data)?;
        let mut tokens: ReaderTokenSource<_> = reader.into();
        let mut actual_count: usize = 0;
        for (instruction, expected_ann_token) in expected_src {
            actual_count += 1;
            let ann_token = tokens.next_token(instruction)?;

            let (exp_ann_thunk, exp_field_name_thunk, exp_token) = expected_ann_token.into_inner();
            let (ann_thunk, field_name_thunk, actual_token) = ann_token.into_inner();

            let exp_anns = exp_ann_thunk.evaluate()?;
            let actual_anns = ann_thunk.evaluate()?;
            assert_eq!(exp_anns, actual_anns);

            let exp_field_name = exp_field_name_thunk.evaluate()?;
            let actual_field_name = field_name_thunk.evaluate()?;
            assert_eq!(exp_field_name, actual_field_name);

            match (exp_token, actual_token) {
                (Null(exp_ion_type), Null(actual_ion_type)) => {
                    assert_eq!(exp_ion_type, actual_ion_type);
                }
                (Scalar(exp_scalar_thunk), Scalar(actual_scalar_thunk)) => {
                    let exp_scalar = exp_scalar_thunk.evaluate()?;
                    let actual_scalar = actual_scalar_thunk.evaluate()?;
                    assert_eq!(exp_scalar, actual_scalar);
                }
                (StartContainer(exp_c_type), StartContainer(actual_c_type)) => {
                    assert_eq!(exp_c_type, actual_c_type);
                }
                (EndContainer(exp_c_type), EndContainer(actual_c_type)) => {
                    assert_eq!(exp_c_type, actual_c_type);
                }
                (EndStream, EndStream) => {
                    // nothing to assert!
                }
                (exp_token, actual_token) => {
                    panic!(
                        "Tokens {:?} and {:?} are not the same",
                        exp_token, actual_token
                    );
                }
            }
        }
        assert_eq!(expected_count, actual_count);
        Ok(())
    }
}
