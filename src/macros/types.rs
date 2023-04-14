// Copyright Amazon.com, Inc. or its affiliates.

//! Static type support for Ion macros.
//!
//! This goes above the runtime type system of Ion within the macro system.

use crate::IonType;

/// Macro types that are encoded without and fixed width.
/// These types are structural constrained types over their general Ion equivalent.
pub enum FixedType {
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
}

/// Macro types that are _abstract_ over the type system.
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

/// Static types for the Ion macro system.
pub enum Type {
    Union(UnionType),
    Tagged(IonType),
    Untagged(IonType),
    Fixed(FixedType),
    // TODO this is parameterized
    Shape,
}