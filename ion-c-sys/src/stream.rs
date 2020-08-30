// Copyright Amazon.com, Inc. or its affiliates.

//! Provides APIs for interfacing with Ion C's `ION_STREAM` APIs.

use std::io::BufRead;
use std::io::Write;

/// Represents an input stream for Ion C.  
#[repr(C)]
struct IonCReadStream<T: BufRead> {
    input: T,
}

/// Represents an output stream for Ion C.
#[repr(C)]
struct IonCWriteStream<T: Write> {
    output: T,
}

/// Represents an output s

extern "C" {}
