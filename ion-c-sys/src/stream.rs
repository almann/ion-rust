// Copyright Amazon.com, Inc. or its affiliates.

//! Provides APIs for interfacing with Ion C's `ION_STREAM` APIs.

use std::io::BufRead;
use std::io::Write;

use crate::*;

/// Bridges the raw C interface for the `_ion_user_stream` handler to something a bit more Rust
/// friendly and can use a closure environment to handle the Rust context generically.
#[repr(C)]
pub struct IonCStreamHolder<'a, T, F: Fn(&mut T, &mut _ion_user_stream) -> IonCResult<()>> {
    source: &'a mut T,
    handler: F,
}

impl<'a, T, F> IonCStreamHolder<'a, T, F>
where
    F: Fn(&mut T, &mut _ion_user_stream) -> IonCResult<()>,
{
    /// Wraps the given closure into an FFI safe structure.
    pub fn new(source: &'a mut T, handler: F) -> Self {
        Self { source, handler }
    }
}

/// Ion C callback to bridge to our handler.
unsafe extern "C" fn ionc_stream_handler<'a, T, F>(stream: *mut _ion_user_stream) -> iERR
where
    T: 'a,
    F: Fn(&mut T, &mut _ion_user_stream) -> IonCResult<()> + 'a,
{
    let user_stream = stream.as_mut().unwrap();
    let holder_ptr = user_stream.handler_state as *mut IonCStreamHolder<'a, T, F>;
    let holder = holder_ptr.as_mut().unwrap();
    let result = (holder.handler)(holder.source, user_stream);
    match result {
        Ok(_) => ion_error_code_IERR_OK,
        Err(e) => e.code,
    }
}
