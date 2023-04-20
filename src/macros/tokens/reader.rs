// Copyright Amazon.com, Inc. or its affiliates.

use super::TokenSource;
use crate::element::{Blob, Clob};
use crate::macros::tokens::{AnnotatedToken, Instruction, Token};
use crate::result::illegal_operation;
use crate::{Decimal, Int, IonReader, IonResult, IonType, Str, StreamItem, Symbol, Timestamp};
use std::cell::RefCell;

/// Adapts any [`TokenSource`] into an [`IonReader`].
///
/// It is important to note that adapting a source in the middle of a container stream
/// will treat it as top-level and only surface what it can see at that level.  It will not
/// step out of the container.
pub struct TokenSourceReader<T>
where
    T: TokenSource,
{
    source: T,
    depth: usize,

    // FIXME this is not right
    // XXX really we have a problem between the lifetime of next() and the other APIs for the token
    // XXX not sure if materialization is the right option or re-thinking how to manage the lifetime
    //     since we're already using a Rc<RefCell<...>> under the hood
    // XXX this is a RefCell<AnnotationToken> because we need interior mutability for memoization
    /// the current token
    curr_token_cell: Option<RefCell<AnnotatedToken<'static>>>,

    /// remember the current read item
    curr_item: StreamItem,
}

impl<T> From<T> for TokenSourceReader<T>
where
    T: TokenSource,
{
    fn from(source: T) -> Self {
        TokenSourceReader {
            source,
            depth: 0,
            curr_token_cell: None,
            curr_item: StreamItem::Nothing,
        }
    }
}

impl<T> IonReader for TokenSourceReader<T>
where
    T: TokenSource,
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
        // FIXME should not require materialization!
        let annotated_token = self.source.next_token(Instruction::Next)?.materialize()?;
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

    fn annotations<'a>(&'a self) -> Box<dyn Iterator<Item = IonResult<Self::Symbol>> + 'a> {
        todo!()
    }

    fn field_name(&self) -> IonResult<Self::Symbol> {
        match &self.curr_token_cell {
            None => illegal_operation("No field name"),
            Some(token_cell) => {
                let mut annotated_token = token_cell.borrow_mut();
                annotated_token.share_field_name()
            }
        }
    }

    fn is_null(&self) -> bool {
        todo!()
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
        todo!()
    }

    fn step_out(&mut self) -> IonResult<()> {
        todo!()
    }

    fn parent_type(&self) -> Option<IonType> {
        todo!()
    }

    fn depth(&self) -> usize {
        todo!()
    }
}
