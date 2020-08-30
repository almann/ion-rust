// Copyright Amazon.com, Inc. or its affiliates.

//! Provides APIs for interfacing with Ion C's `ION_STREAM` APIs.

use std::io::BufRead;
use std::io::Write;

use crate::*;

/// Represents an input stream for Ion C.  
#[repr(C)]
struct IonCReadStream<T: BufRead> {
    input: T,
}

impl<T: BufRead> IonCReadStream<T> {
    pub fn new(input: T) -> Self {
        Self { input }
    }
}

/// Represents an output stream for Ion C.
#[repr(C)]
struct IonCWriteStream<T: Write> {
    output: T,
}

impl<T: Write> IonCWriteStream<T> {
    pub fn new(output: T) -> Self {
        Self { output }
    }
}

/// Bridges the raw C interface for the `_ion_user_stream` handler to something a bit more Rust
/// friendly and can use a closure environment to handle the Rust context generically.
#[repr(C)]
pub struct IonCStreamHandler<F: FnMut(&mut _ion_user_stream) -> IonCResult<()>> {
    handler: F,
}

impl<F: FnMut(&mut _ion_user_stream) -> IonCResult<()>> IonCStreamHandler<F> {
    pub fn new(handler: F) -> Self {
        Self { handler }
    }
}

unsafe extern "C" fn ionc_stream_handler<F>(stream: *mut _ion_user_stream) -> iERR
where
    F: FnMut(&mut _ion_user_stream) -> IonCResult<()>,
{
    let user_stream = stream.as_mut().unwrap();
    let handler_obj_ptr = user_stream.handler_state as *mut IonCStreamHandler<F>;
    let result = ((*handler_obj_ptr).handler)(user_stream);
    match result {
        Ok(_) => ion_error_code_IERR_OK,
        Err(e) => e.code,
    }
}
