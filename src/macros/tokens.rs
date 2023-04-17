// Copyright Amazon.com, Inc. or its affiliates.

//! Provides a simple token-like, event stream API over [`IonReader`].
//!
//! This is useful for composing and transforming over streams and is used by the macro
//! system to operate on an Ion stream like a lexer.  It pulls in some of the [`crate::element`]
//! API to make it easier to work with values without pulling in fully materialized collections.

use crate::element::{Bytes, Value};
use crate::result::illegal_operation;
use crate::{Decimal, Int, IonError, IonType, Str, Symbol, Timestamp};
use std::fmt::{Display, Formatter};

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
            Value::Null(t) => Ok(Null(t)),
            Value::Bool(b) => Ok(Bool(b)),
            Value::Int(i) => Ok(Int(i)),
            Value::Float(f) => Ok(Float(f)),
            Value::Decimal(d) => Ok(Decimal(d)),
            Value::Timestamp(ts) => Ok(Timestamp(ts)),
            Value::String(text) => Ok(String(text)),
            Value::Symbol(sym) => Ok(Symbol(sym)),
            Value::Blob(bytes) => Ok(Blob(bytes)),
            Value::Clob(bytes) => Ok(Clob(bytes)),
            Value::SExp(_) => illegal_operation("SExp is not an atom value"),
            Value::List(_) => illegal_operation("List is not an atom value"),
            Value::Struct(_) => illegal_operation("Struct is not an atom value"),
        }
    }
}

// TODO implement me!

/// Represents a token within the stream.
#[derive(Debug, PartialEq, Clone)]
pub enum Token {
    Atom(AtomValue),
    StartContainer(ContainerType),
    EndContainer(ContainerType),
    /// End of the stream
    End,
}

pub struct Event {}
