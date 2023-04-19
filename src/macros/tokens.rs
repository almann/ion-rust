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
use crate::macros::thunk::Thunk;
use crate::result::illegal_operation;
use crate::text::text_formatter::IonValueFormatter;
use crate::{
    Decimal, Int, IonError, IonReader, IonResult, IonType, Str, StreamItem, Symbol, Timestamp,
};
use std::cell::RefCell;
use std::fmt::{Display, Formatter};
use std::marker::PhantomData;
use std::rc::Rc;

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

/// Subset of [`Value`] that is restricted to non-container types.
#[derive(Debug, Clone, PartialEq)]
pub enum AtomValue {
    Null(IonType),
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

impl TryFrom<Value> for AtomValue {
    type Error = IonError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        use AtomValue::*;
        match value {
            Value::Null(ion_type) => Ok(Null(ion_type)),
            Value::Bool(bool) => Ok(Bool(bool)),
            Value::Int(int) => Ok(Int(int)),
            Value::Float(float) => Ok(Float(float)),
            Value::Decimal(decimal) => Ok(Decimal(decimal)),
            Value::Timestamp(timestamp) => Ok(Timestamp(timestamp)),
            Value::String(text) => Ok(String(text)),
            Value::Symbol(symbol) => Ok(Symbol(symbol)),
            Value::Blob(bytes) => Ok(Blob(bytes)),
            Value::Clob(bytes) => Ok(Clob(bytes)),
            Value::SExp(_) => illegal_operation("SExp is not an atom value"),
            Value::List(_) => illegal_operation("List is not an atom value"),
            Value::Struct(_) => illegal_operation("Struct is not an atom value"),
        }
    }
}

impl Display for AtomValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use AtomValue::*;
        let mut ivf = IonValueFormatter { output: f };
        match self {
            Null(ion_type) => ivf.format_null(*ion_type),
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

/// Deferred computation of an atom.
pub type AtomThunk<'a> = Thunk<'a, AtomValue>;

// XXX ideally we'd have our annotations return an borrowing iterator...

/// Deferred computation of annotations.
pub type AnnotationsThunk<'a> = Thunk<'a, Annotations>;

/// Represents a token within the stream.
pub enum Token<'a> {
    Atom(AtomThunk<'a>),
    StartContainer(ContainerType),
    EndContainer(ContainerType),
    EndStream,
}

impl<'a> Token<'a> {
    /// Consume this token to one that owns its content.
    fn materialize(self) -> IonResult<Token<'static>> {
        use Token::*;
        Ok(match self {
            Atom(thunk) => Atom(thunk.materialize()?),
            StartContainer(container_type) => StartContainer(container_type),
            EndContainer(container_type) => EndContainer(container_type),
            EndStream => EndStream,
        })
    }
}

impl From<AtomValue> for Token<'static> {
    fn from(value: AtomValue) -> Self {
        Token::Atom(Thunk::wrap(value))
    }
}

impl<'a> From<AtomThunk<'a>> for Token<'a> {
    fn from(thunk: AtomThunk<'a>) -> Self {
        Token::Atom(thunk)
    }
}

/// A token with annotations and a field name.
pub struct AnnotatedToken<'a> {
    annotations: AnnotationsThunk<'a>,
    field_name: Option<Symbol>,
    token: Token<'a>,
}

impl<'a> AnnotatedToken<'a> {
    fn new(
        annotations: AnnotationsThunk<'a>,
        field_name: Option<Symbol>,
        token: Token<'a>,
    ) -> Self {
        Self {
            annotations,
            field_name,
            token,
        }
    }

    /// Consume this annotated token into one that owns its content.
    fn materialize(self) -> IonResult<AnnotatedToken<'static>> {
        Ok(AnnotatedToken::<'static>::new(
            self.annotations.materialize()?,
            self.field_name,
            self.token.materialize()?,
        ))
    }
}

impl<'a> From<Token<'a>> for AnnotatedToken<'a> {
    fn from(value: Token<'a>) -> Self {
        AnnotatedToken::new(Thunk::wrap(Annotations::empty()), None, value)
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
trait TokenSource {
    /// Advances the source to the next token.
    ///
    /// Returns that token or an error if there is some problem with the underlying stream.
    fn next(&mut self, instruction: Instruction) -> IonResult<AnnotatedToken>;
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
    fn bool_token(&mut self) -> Token<'a> {
        let reader_cell = self.reader_cell.clone();
        Thunk::defer(move || {
            let mut reader = reader_cell.borrow_mut();
            Ok(AtomValue::Bool(reader.read_bool()?))
        })
        .into()
    }

    #[inline]
    fn int_token(&mut self) -> Token<'a> {
        let reader_cell = self.reader_cell.clone();
        Thunk::defer(move || {
            let mut reader = reader_cell.borrow_mut();
            Ok(AtomValue::Int(reader.read_int()?))
        })
        .into()
    }

    #[inline]
    fn float_token(&mut self) -> Token<'a> {
        let reader_cell = self.reader_cell.clone();
        Thunk::defer(move || {
            let mut reader = reader_cell.borrow_mut();
            Ok(AtomValue::Float(reader.read_f64()?))
        })
        .into()
    }

    #[inline]
    fn decimal_token(&mut self) -> Token<'a> {
        let reader_cell = self.reader_cell.clone();
        Thunk::defer(move || {
            let mut reader = reader_cell.borrow_mut();
            Ok(AtomValue::Decimal(reader.read_decimal()?))
        })
        .into()
    }

    #[inline]
    fn timestamp_token(&mut self) -> Token<'a> {
        let reader_cell = self.reader_cell.clone();
        Thunk::defer(move || {
            let mut reader = reader_cell.borrow_mut();
            Ok(AtomValue::Timestamp(reader.read_timestamp()?))
        })
        .into()
    }

    #[inline]
    fn string_token(&mut self) -> Token<'a> {
        let reader_cell = self.reader_cell.clone();
        Thunk::defer(move || {
            let mut reader = reader_cell.borrow_mut();
            Ok(AtomValue::String(reader.read_string()?))
        })
        .into()
    }

    #[inline]
    fn symbol_token(&mut self) -> Token<'a> {
        let reader_cell = self.reader_cell.clone();
        Thunk::defer(move || {
            let mut reader = reader_cell.borrow_mut();
            Ok(AtomValue::Symbol(reader.read_symbol()?))
        })
        .into()
    }

    #[inline]
    fn blob_token(&mut self) -> Token<'a> {
        let reader_cell = self.reader_cell.clone();
        Thunk::defer(move || {
            let mut reader = reader_cell.borrow_mut();
            Ok(AtomValue::Blob(reader.read_blob()?.into()))
        })
        .into()
    }

    #[inline]
    fn clob_token(&mut self) -> Token<'a> {
        let reader_cell = self.reader_cell.clone();
        Thunk::defer(move || {
            let mut reader = reader_cell.borrow_mut();
            Ok(AtomValue::Clob(reader.read_clob()?.into()))
        })
        .into()
    }

    // TODO probably worth just hoisting this back into an impl of IonReader

    #[inline]
    fn next(&mut self) -> IonResult<StreamItem> {
        let mut reader = self.reader_cell.borrow_mut();
        reader.next()
    }

    #[inline]
    fn field_name(&self) -> IonResult<Symbol> {
        let reader = self.reader_cell.borrow();
        reader.field_name()
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
    fn next(&mut self, instruction: Instruction) -> IonResult<AnnotatedToken> {
        use Instruction::*;

        Ok(match instruction {
            Next => {
                let item = self.next()?;
                match item {
                    StreamItem::Value(ion_type) | StreamItem::Null(ion_type) => {
                        let annotations_thunk = self.annotations_thunk();
                        let field_name = self.field_name().ok();
                        let token = if self.is_null() {
                            AtomValue::Null(ion_type).into()
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
                                Some(IonType::List) => Token::StartContainer(ContainerType::List),
                                Some(IonType::SExp) => Token::StartContainer(ContainerType::SExp),
                                Some(IonType::Struct) => {
                                    Token::StartContainer(ContainerType::Struct)
                                }
                            }
                        };
                        AnnotatedToken::new(annotations_thunk, field_name, token)
                    }
                    StreamItem::Nothing => match self.parent_type() {
                        None => Token::EndStream.into(),
                        Some(IonType::SExp) => Token::EndContainer(ContainerType::SExp).into(),
                        Some(IonType::List) => Token::EndContainer(ContainerType::List).into(),
                        Some(IonType::Struct) => Token::EndContainer(ContainerType::Struct).into(),
                        Some(ion_type) => illegal_operation(format!(
                            "Unexpected non-container type: {}",
                            ion_type
                        ))?,
                    },
                }
            }
            NextEnd => todo!(),
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
    use super::AtomValue::*;
    use super::ContainerType::*;
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
    #[case::atom_null(Null(IonType::Null), Value::Null(IonType::Null))]
    #[case::atom_bool(Bool(false), Value::Bool(false))]
    #[case::atom_int(Int(3.into()), Value::Int(3.into()))]
    #[case::atom_float(Float(1.1), Value::Float(1.1))]
    #[case::atom_decimal(Decimal(42.into()), Value::Decimal(42.into()))]
    #[case::atom_timestamp(Timestamp(sample_timestamp()), Value::Timestamp(sample_timestamp()))]
    #[case::atom_symbol(Symbol("foo".into()), Value::Symbol("foo".into()))]
    #[case::atom_string(String("bar".into()), Value::String("bar".into()))]
    #[case::atom_clob(Clob("hello".into()), Value::Clob("hello".into()))]
    #[case::atom_blob(Blob("world".into()), Value::Blob("world".into()))]
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
        match T::try_from(bad_from) {
            Ok(t) => panic!("Unexpected conversion from {} to {}", from_clone, t),
            Err(_) => (),
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

    #[rstest]
    #[case::sexp(Value::SExp(vec![].into()))]
    #[case::list(Value::List(vec![].into()))]
    #[case::strct(Value::Struct(empty_struct()))]
    fn test_invalid_atom_conversion(#[case] bad_value: Value) {
        test_invalid_conversion::<_, AtomValue>(bad_value)
    }
}
