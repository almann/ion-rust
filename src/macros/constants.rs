// Copyright Amazon.com, Inc. or its affiliates.

//! Constants used by the macro system.
//!
//! Primarily centered around keywords and type names.

/// Constants for syntactic elements such as keywords, sigil tokens, and built-in types.
pub(crate) mod syntax {
    pub const UINT8: &str = "uint8";
    pub const UINT16: &str = "uint16";
    pub const UINT32: &str = "uint32";
    pub const UINT64: &str = "uint64";

    pub const INT8: &str = "int8";
    pub const INT16: &str = "int16";
    pub const INT32: &str = "int32";
    pub const INT64: &str = "int64";

    pub const FLOAT16: &str = "float16";
    pub const FLOAT32: &str = "float32";
    pub const FLOAT64: &str = "float64";

    pub const ANY: &str = "any";
    pub const NUMBER: &str = "number";
    pub const EXACT: &str = "exact";
    pub const TEXT: &str = "text";
    pub const LOB: &str = "lob";
    pub const SEQUENCE: &str = "sequence";

    pub const EXACTLY_ONE_SIGIL: &str = "!";
    pub const ZERO_OR_ONE_SIGIL: &str = "?";
    pub const ZERO_OR_MORE_SIGIL: &str = "*";
    pub const ONE_OR_MORE_SIGIL: &str = "+";
    pub const REST_SIGIL: &str = "...";

    pub const TAGLESS: &str = "tagless";
}
