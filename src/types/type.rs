use crate::result::{illegal_operation, IonError};
use ion_c_sys::ION_TYPE;
use std::convert::TryFrom;

/// Represents the Ion data type of a given value. To learn more about each data type,
/// read [the Ion Data Model](http://amzn.github.io/ion-docs/docs/spec.html#the-ion-data-model)
/// section of the spec.
#[derive(Debug, PartialEq, Eq, PartialOrd, Copy, Clone)]
pub enum IonType {
    Null,
    Boolean,
    Integer,
    Float,
    Decimal,
    Timestamp,
    Symbol,
    String,
    Clob,
    Blob,
    List,
    SExpression,
    Struct,
}

impl IonType {
    pub fn is_container(&self) -> bool {
        use IonType::*;
        match self {
            List | SExpression | Struct => true,
            _ => false,
        }
    }
}

impl TryFrom<ION_TYPE> for IonType {
    type Error = IonError;

    fn try_from(value: ION_TYPE) -> Result<Self, Self::Error> {
        use IonType::*;
        match value {
            ion_c_sys::ION_TYPE_NULL => Ok(Null),
            ion_c_sys::ION_TYPE_BOOL => Ok(Boolean),
            ion_c_sys::ION_TYPE_INT => Ok(Integer),
            ion_c_sys::ION_TYPE_FLOAT => Ok(Float),
            ion_c_sys::ION_TYPE_DECIMAL => Ok(Decimal),
            ion_c_sys::ION_TYPE_TIMESTAMP => Ok(Timestamp),
            ion_c_sys::ION_TYPE_SYMBOL => Ok(Symbol),
            ion_c_sys::ION_TYPE_STRING => Ok(String),
            ion_c_sys::ION_TYPE_CLOB => Ok(Clob),
            ion_c_sys::ION_TYPE_BLOB => Ok(Blob),
            ion_c_sys::ION_TYPE_LIST => Ok(List),
            ion_c_sys::ION_TYPE_SEXP => Ok(SExpression),
            ion_c_sys::ION_TYPE_STRUCT => Ok(Struct),
            _ => illegal_operation(format!("Could not convert Ion C ION_TYPE: ${:?}", value)),
        }
    }
}
