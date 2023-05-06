// Copyright Amazon.com, Inc. or its affiliates.

//! Provides support Ion 1.1 macros (not to be confused with Rust macros).

use crate::result::decoding_error_raw;
use crate::tokens::{Instruction, TokenStream};
use crate::IonResult;

pub(crate) mod constants;

pub mod env;
pub mod ident;
pub mod types;

// XXX this trait is here to allow us to parse generically from anything referencable as a &str
//     we cannot do this with TryFrom
// TODO evaluate if this should even be here...

/// Generically parse from anything that can be represented as `&str`.
pub trait ParseStr
where
    Self: Sized,
{
    /// Parse the given `&str` reference into this type.
    fn parse_str<S>(as_str: S) -> IonResult<Self>
    where
        S: AsRef<str>;
}

/// Parse something from an Ion token stream, attempts to consume the stream to parse something
/// of this type unless it cannot be parsed or it runs out of tokens from the stream.
///
/// If something is [`ParseStr`], it can be parsed from an Ion stream as a symbol strictly with
/// no annotations.
pub trait ParseIon
where
    Self: Sized,
{
    /// Parse the given stream into an instance of this value.
    fn parse_ion<'a, S>(stream: &mut S) -> IonResult<Self>
    where
        S: TokenStream<'a>;
}

impl<T> ParseIon for T
where
    T: ParseStr,
{
    fn parse_ion<'a, S>(stream: &mut S) -> IonResult<Self>
    where
        S: TokenStream<'a>,
    {
        let mut token = stream.next_token(Instruction::Next)?;
        let text = token
            .has_no_annotations()?
            .symbol()?
            .text()
            .ok_or_else(|| decoding_error_raw("No text symbol"))?;
        T::parse_str(text)
    }
}
