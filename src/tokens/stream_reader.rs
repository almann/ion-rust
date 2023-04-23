// Copyright Amazon.com, Inc. or its affiliates.

use super::{AnnotatedToken, ContainerType, Instruction, Token, TokenStream};
use crate::element::{Blob, Clob};
use crate::result::illegal_operation;
use crate::{Decimal, Int, IonReader, IonResult, IonType, Str, StreamItem, Symbol, Timestamp};
use std::cell::RefCell;

const STEP_IN_ERROR_TEXT: &str = "Cannot step in, not at start of container";
const STEP_OUT_ERROR_TEXT: &str = "Cannot step out, not in a container";
const NO_FIELD_NAME_ERROR_TEXT: &str = "No field name";

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
}

impl<'a, T> TokenStreamReader<'a, T>
where
    T: TokenStream<'a>,
{
    /// Advances the stream, setting the current token and item.
    fn next_token(&mut self, instruction: Instruction) -> IonResult<StreamItem> {
        let annotated_token = self.stream.next_token(instruction)?;
        let item = match &annotated_token.token {
            Token::Null(ion_type) => StreamItem::Null(*ion_type),
            Token::Scalar(thunk) => StreamItem::Value(thunk.scalar_type().into()),
            Token::StartContainer(container_type) => StreamItem::Value((*container_type).into()),
            Token::EndContainer(_) => StreamItem::Nothing,
            Token::EndStream => StreamItem::Nothing,
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
        }
    }
}

impl<'a, T> IonReader for TokenStreamReader<'a, T>
where
    T: TokenStream<'a>,
{
    type Item = StreamItem;
    type Symbol = Symbol;

    fn ion_version(&self) -> (u8, u8) {
        // FIXME this is clearly wrong, but not sure about this API in general...
        // XXX we just fake 1.1 for now because that is the context we're operating in...
        (1, 1)
    }

    fn next(&mut self) -> IonResult<Self::Item> {
        if let Some(token_cell) = &self.curr_token_cell {
            let annotated_token = token_cell.borrow();
            if let Token::EndContainer(_) = annotated_token.token() {
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
                    Token::Null(ion_type) => Some(*ion_type),
                    Token::Scalar(thunk) => Some(thunk.scalar_type().into()),
                    Token::StartContainer(container_type) => Some((*container_type).into()),
                    Token::EndContainer(_) => {
                        // the end of a container is considered not positioned
                        None
                    }
                    Token::EndStream => None,
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
        todo!()
    }

    fn read_bool(&mut self) -> IonResult<bool> {
        todo!()
    }

    fn read_i64(&mut self) -> IonResult<i64> {
        todo!()
    }

    fn read_int(&mut self) -> IonResult<Int> {
        todo!()
    }

    fn read_f32(&mut self) -> IonResult<f32> {
        todo!()
    }

    fn read_f64(&mut self) -> IonResult<f64> {
        todo!()
    }

    fn read_decimal(&mut self) -> IonResult<Decimal> {
        todo!()
    }

    fn read_string(&mut self) -> IonResult<Str> {
        todo!()
    }

    fn read_str(&mut self) -> IonResult<&str> {
        todo!()
    }

    fn read_symbol(&mut self) -> IonResult<Self::Symbol> {
        todo!()
    }

    fn read_blob(&mut self) -> IonResult<Blob> {
        todo!()
    }

    fn read_clob(&mut self) -> IonResult<Clob> {
        todo!()
    }

    fn read_timestamp(&mut self) -> IonResult<Timestamp> {
        todo!()
    }

    fn step_in(&mut self) -> IonResult<()> {
        match &self.curr_token_cell {
            None => illegal_operation(STEP_IN_ERROR_TEXT),
            Some(token_cell) => {
                let annotated_token = token_cell.borrow();
                match annotated_token.token() {
                    Token::StartContainer(container_type) => {
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
