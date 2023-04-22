// Copyright Amazon.com, Inc. or its affiliates.

use super::{
    AnnotatedToken, AnnotationsThunk, ContainerType, FieldNameThunk, Instruction, ScalarThunk,
    ScalarType, ScalarValue, Token, TokenStream,
};
use crate::result::illegal_operation;
use crate::thunk::Thunk;
use crate::{IonReader, IonResult, IonType, StreamItem, Symbol};
use std::cell::RefCell;
use std::marker::PhantomData;
use std::rc::Rc;

// TODO make this more generic with respect to other readers--the problem is Item/Symbol
// TODO this has to abstract over potentially system reader to implement macros

/// Adapter for a [`TokenStream`] over an arbitrary [`IonReader`]
pub struct ReaderTokenStream<'a, R>
where
    R: IonReader<Item = StreamItem, Symbol = Symbol> + 'a,
{
    // XXX this is so we can have multiple closures to lazily evaluate tokens
    reader_cell: Rc<RefCell<R>>,
    // XXX this allows us to explicitly capture a lifetime for the reader we operate on
    phantom: PhantomData<&'a R>,
}

impl<'a, R> ReaderTokenStream<'a, R>
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

impl<'a, R> TokenStream for ReaderTokenStream<'a, R>
where
    R: IonReader<Item = StreamItem, Symbol = Symbol> + 'a,
{
    fn next_token(&mut self, instruction: Instruction) -> IonResult<AnnotatedToken> {
        use crate::tokens::Instruction::*;

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

impl<'a, R> From<R> for ReaderTokenStream<'a, R>
where
    R: IonReader<Item = StreamItem, Symbol = Symbol> + 'a,
{
    fn from(value: R) -> Self {
        ReaderTokenStream {
            reader_cell: Rc::new(RefCell::new(value)),
            phantom: Default::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Instruction::*;
    use super::*;
    use crate::data_source::ToIonDataSource;
    use crate::element::{Blob as ElemBlob, Clob as ElemClob};
    use crate::result::{illegal_operation, illegal_operation_raw};
    use crate::tokens::{ContainerType, ScalarValue, Value};
    use crate::{Decimal, IonResult, ReaderBuilder, Symbol};
    use rstest::rstest;

    /// An arbitrary timestamp as a filler for testing purposes.
    fn sample_timestamp() -> crate::Timestamp {
        crate::Timestamp::with_year(1999).build().unwrap()
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
            .ok_or(illegal_operation_raw("No last element in stream to change"))?;
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
        container_src(
            ContainerType::Struct,
            field_named_srcs(["a"], single_src(5)),
        )
    }

    #[rstest]
    #[case::bool(single_src(false), "false")]
    #[case::int(single_src(5), "5")]
    #[case::float(single_src(5.0), "5e0")]
    #[case::decimal(single_src(Decimal::from(50)), "50.")]
    #[case::timestamp(single_src(sample_timestamp()), "1999T")]
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
    fn stream_test<S>(#[case] expected: IonResult<Srcs>, #[case] data: S) -> IonResult<()>
    where
        S: ToIonDataSource,
    {
        use Token::*;
        let mut expected_src = expected?;
        // add the terminator
        expected_src.push((Next, EndStream.into()));
        let expected_count = expected_src.len();

        let reader = ReaderBuilder::new().build(data)?;
        let mut tokens: ReaderTokenStream<_> = reader.into();
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
