// Copyright Amazon.com, Inc. or its affiliates.

use super::{AnnotatedToken, ContainerType, Content, Instruction, TokenStream};
use crate::element::{Blob, Clob};
use crate::result::{illegal_operation, illegal_operation_raw};
use crate::tokens::ScalarValue;
use crate::types::integer::IntAccess;
use crate::{Decimal, Int, IonReader, IonResult, IonType, Str, StreamItem, Symbol, Timestamp};
use std::cell::RefCell;

/// Adapts any [`TokenStream`] into an [`IonReader`].
///
/// It is important to note that adapting a stream in the middle of a container stream
/// will treat it as top-level and only surface what it can see at that level.  It will not
/// step out of the container.
pub struct TokenStreamReader<'a, T>
where
    T: TokenStream<'a>,
{
    stream: T,
    /// Models what containers we
    container_stack: Vec<ContainerType>,

    // XXX this is a RefCell<AnnotationToken> because we need interior mutability for memoization
    /// the current token
    curr_token_cell: Option<RefCell<AnnotatedToken<'a>>>,

    /// remember the current read item
    curr_item: StreamItem,

    /// memory set aside to support `read_str` since we cannot safely return a reference into the
    /// `RefCell` that holds the token without wrapping it in a `Ref`.
    str_buf: Str,
}

impl<'a, T> TokenStreamReader<'a, T>
where
    T: TokenStream<'a>,
{
    /// Advances the stream, setting the current token and item.
    fn next_token(&mut self, instruction: Instruction) -> IonResult<StreamItem> {
        let annotated_token = self.stream.next_token(instruction)?;
        let item = match &annotated_token.token {
            Content::Null(ion_type) => StreamItem::Null(*ion_type),
            Content::Scalar(thunk) => StreamItem::Value(thunk.scalar_type().into()),
            Content::StartContainer(container_type) => StreamItem::Value((*container_type).into()),
            Content::EndContainer(_) => StreamItem::Nothing,
            Content::EndStream => StreamItem::Nothing,
        };
        self.curr_item = item;
        self.curr_token_cell = Some(RefCell::new(annotated_token));
        Ok(item)
    }
}

impl<'a, T> From<T> for TokenStreamReader<'a, T>
where
    T: TokenStream<'a>,
{
    fn from(stream: T) -> Self {
        TokenStreamReader {
            stream,
            container_stack: vec![],
            curr_token_cell: None,
            curr_item: StreamItem::Nothing,
            str_buf: Str::from(""),
        }
    }
}

const STEP_IN_ERROR_TEXT: &str = "Cannot step in, not at start of container";
const STEP_OUT_ERROR_TEXT: &str = "Cannot step out, not in a container";
const NO_FIELD_NAME_ERROR_TEXT: &str = "No field name";
const NOT_POSITIONED_ON_ANYTHING_ERROR_TEXT: &str = "Not positioned on anything";
const CANNOT_READ_NON_SCALAR_ERROR_TEXT: &str = "Cannot read from non-scalar";

/// Generates the read methods against the underlying token/item state.
/// This eliminates the boilerplate around each definition avoiding a lot of copy/paste.
///
/// * `me` - the identifier for `self` to make it visible to `scalar_exp`.
/// * `method` - the name of the method.
/// * `scalar_type` - the return type for the method.
/// * `variant` - the unqualified variant of [`ScalarValue`] to match over the current token.
/// * `scalar` - the matched identifier of the contents of [`ScalarValue`].
/// * `scalar_exp` - the expression to generate the return value.
macro_rules! read_method_self {
    ($me:ident, $method:ident, $scalar_type:ty, $variant:ident, $scalar:ident, $scalar_exp:expr) => {
        fn $method(&mut $me) -> IonResult<$scalar_type> {
            match &$me.curr_token_cell {
                None => illegal_operation(NOT_POSITIONED_ON_ANYTHING_ERROR_TEXT),
                Some(token_cell) => {
                    let mut annotated_token = token_cell.borrow_mut();
                    match annotated_token.token_mut().no_memoize_scalar() {
                        Ok(Some(ScalarValue::$variant($scalar))) => Ok($scalar_exp),
                        Ok(Some(scalar_value)) => illegal_operation(format!(
                            concat!("Cannot read ", stringify!($scalar_type), " from {}"),
                            scalar_value.scalar_type()
                        )),
                        Ok(None) => illegal_operation(CANNOT_READ_NON_SCALAR_ERROR_TEXT),
                        Err(e) => Err(e),
                    }
                }
            }
        }
    };
}

/// Shorthand for `read_method_self` where we do not need to capture `self` in the expression.
macro_rules! read_method {
    ($method:ident, $scalar_type:ty, $variant:ident, $scalar:ident, $scalar_exp:expr) => {
        read_method_self!(self, $method, $scalar_type, $variant, $scalar, $scalar_exp);
    };
}

impl<'a, T> IonReader for TokenStreamReader<'a, T>
where
    T: TokenStream<'a>,
{
    type Item = StreamItem;
    type Symbol = Symbol;

    fn ion_version(&self) -> (u8, u8) {
        // XXX A `TokenStream` doesn't know its underlying Ion version, we just say 1.0
        //     because all Ion 1.x versions have the same data model.
        (1, 0)
    }

    fn next(&mut self) -> IonResult<Self::Item> {
        if let Some(token_cell) = &self.curr_token_cell {
            let annotated_token = token_cell.borrow();
            if let Content::EndContainer(_) = annotated_token.token() {
                // if we're positioned on the end of the container we return nothing until step out
                return Ok(StreamItem::Nothing);
            }
        }
        self.next_token(Instruction::Next)
    }

    fn current(&self) -> Self::Item {
        self.curr_item
    }

    fn ion_type(&self) -> Option<IonType> {
        match &self.curr_token_cell {
            None => None,
            Some(token_cell) => {
                let annotated_token = token_cell.borrow();
                match annotated_token.token() {
                    Content::Null(ion_type) => Some(*ion_type),
                    Content::Scalar(thunk) => Some(thunk.scalar_type().into()),
                    Content::StartContainer(container_type) => Some((*container_type).into()),
                    Content::EndContainer(_) => {
                        // the end of a container is considered not positioned
                        None
                    }
                    Content::EndStream => None,
                }
            }
        }
    }

    fn annotations<'b>(&'b self) -> Box<dyn Iterator<Item = IonResult<Self::Symbol>> + 'b> {
        todo!()
    }

    fn field_name(&self) -> IonResult<Self::Symbol> {
        match &self.curr_token_cell {
            None => illegal_operation(NO_FIELD_NAME_ERROR_TEXT),
            Some(token_cell) => {
                let mut annotated_token = token_cell.borrow_mut();
                match annotated_token.share_field_name() {
                    Ok(Some(symbol)) => Ok(symbol),
                    Ok(None) => illegal_operation(NO_FIELD_NAME_ERROR_TEXT),
                    Err(e) => Err(e),
                }
            }
        }
    }

    fn is_null(&self) -> bool {
        matches!(self.curr_item, StreamItem::Null(_))
    }

    fn read_null(&mut self) -> IonResult<IonType> {
        match &self.curr_item {
            StreamItem::Null(ion_type) => Ok(*ion_type),
            StreamItem::Value(ion_type) => {
                illegal_operation(format!("Cannot read null for {} value", ion_type))
            }
            StreamItem::Nothing => illegal_operation("Cannot read null on nothing"),
        }
    }

    read_method!(read_bool, bool, Bool, boolean, boolean);
    read_method!(
        read_i64,
        i64,
        Int,
        integer,
        integer
            .as_i64()
            .ok_or_else(|| illegal_operation_raw("Integer too large for i64"))?
    );
    read_method!(read_int, Int, Int, integer, integer);
    read_method!(read_f32, f32, Float, float, float as f32);
    read_method!(read_f64, f64, Float, float, float);
    read_method!(read_decimal, Decimal, Decimal, decimal, decimal);
    read_method!(read_string, Str, String, string, string);
    read_method_self!(self, read_str, &str, String, string, {
        // XXX we need to keep the computed value in our own memory
        self.str_buf = string;
        self.str_buf.text()
    });
    read_method!(read_symbol, Symbol, Symbol, symbol, symbol);
    read_method!(read_blob, Blob, Blob, blob, Blob(blob));
    read_method!(read_clob, Clob, Clob, clob, Clob(clob));
    read_method!(read_timestamp, Timestamp, Timestamp, timestamp, timestamp);

    fn step_in(&mut self) -> IonResult<()> {
        match &self.curr_token_cell {
            None => illegal_operation(STEP_IN_ERROR_TEXT),
            Some(token_cell) => {
                let annotated_token = token_cell.borrow();
                match annotated_token.token() {
                    Content::StartContainer(container_type) => {
                        // position the item over nothing
                        self.curr_item = StreamItem::Nothing;
                        // push container context
                        self.container_stack.push(*container_type);
                        Ok(())
                    }
                    _ => illegal_operation(STEP_IN_ERROR_TEXT),
                }
            }
        }
    }

    fn step_out(&mut self) -> IonResult<()> {
        // pop container context
        match self.container_stack.pop() {
            Some(_) => {
                // advance stream to the end of the container
                self.next_token(Instruction::NextEnd)?;
                Ok(())
            }
            None => illegal_operation(STEP_OUT_ERROR_TEXT),
        }
    }

    fn parent_type(&self) -> Option<IonType> {
        match self.container_stack.last() {
            Some(container_type) => Some((*container_type).into()),
            None => None,
        }
    }

    fn depth(&self) -> usize {
        self.container_stack.len()
    }
}
