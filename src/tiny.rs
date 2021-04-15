// Copyright Amazon.com, Inc. or its affiliates.

use std::fmt::Debug;
use std::str::from_utf8;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum TinyError {
    #[error("{message}")]
    ParseError { message: String },
}

pub fn parse_error<T, S: Into<String>>(message: S) -> TinyResult<T> {
    Err(TinyError::ParseError {
        message: message.into(),
    })
}

pub type TinyResult<T> = Result<T, TinyError>;

#[derive(Debug)]
pub enum TinyType {
    Null,
    Integer,
}

pub trait IntegerReader {
    fn read_i64(&mut self) -> TinyResult<i64>;
}

#[derive(Debug)]
pub enum Event<I>
where
    I: IntegerReader + Debug,
{
    EndOfStream,
    Null(TinyType),
    /// GAT would make this just `I` because we could construct
    /// a value with the borrow tied to `'ctx`.
    Integer(I),
}

pub trait Cursor {
    type IReader<'val>: IntegerReader + Debug;

    fn next<'a>(&'a mut self) -> TinyResult<Event<Self::IReader<'a>>>;
}

struct ByteScanner<'data> {
    data: &'data [u8],
    pos: usize,
}

impl<'data> ByteScanner<'data> {
    #[inline]
    pub fn new(data: &'data [u8]) -> Self {
        ByteScanner { data, pos: 0 }
    }

    #[inline]
    fn rem(&self) -> usize {
        self.data.len() - self.pos
    }

    #[inline]
    fn read(&mut self) -> TinyResult<u8> {
        if self.rem() == 0 {
            parse_error("Unexpected end of stream")
        } else {
            let octet = self.data[self.pos];
            self.pos += 1;
            Ok(octet)
        }
    }
}

pub struct BCursor<'data> {
    scanner: ByteScanner<'data>,
}

impl<'data> BCursor<'data> {
    pub fn new(data: &'data [u8]) -> Self {
        Self {
            scanner: ByteScanner::new(data),
        }
    }
}

impl<'data> Cursor for BCursor<'data> {
    type IReader<'ctx> = BIntegerReader<'data, 'ctx>;

    fn next<'ctx>(&'ctx mut self) -> TinyResult<Event<Self::IReader<'ctx>>> {
        Ok(if self.scanner.rem() == 0 {
            Event::EndOfStream
        } else {
            match self.scanner.read()? {
                // null
                0x00 => Event::Null(TinyType::Null),
                // null int
                0x01 => Event::Null(TinyType::Integer),
                // integer value
                0x10 => Event::Integer(BIntegerReader { cursor: self }),
                type_code => return parse_error(format!("Invalid type: {:x}", type_code)),
            }
        })
    }
}

#[derive(Debug)]
pub struct BIntegerReader<'data, 'ctx> {
    /// We model the borrow as a raw pointer because we cannot model the lifetime into the
    /// cursor.  However, the only way this reader is returned is by a mutable borrow from the
    /// cursor itself, so even though we have to model this unsafe, it will never be used
    /// in an unsafe way.
    ///
    /// When GAT lands, we can model this with a lifetime parameter return it in the `Event`
    /// directly rather than by mutable borrow.
    cursor: &'ctx mut BCursor<'data>,
}

impl<'data, 'ctx> IntegerReader for BIntegerReader<'data, 'ctx> {
    fn read_i64(&mut self) -> TinyResult<i64> {
        // for our dumb format just widen a byte to an i64
        Ok(self.cursor.scanner.read()? as i64)
    }
}

// text implementation--forgive the copy-paste, we'd factor this better in a real implementation

pub struct TCursor<'data> {
    scanner: ByteScanner<'data>,
}

impl<'data> TCursor<'data> {
    pub fn new(data: &'data [u8]) -> Self {
        Self {
            scanner: ByteScanner::new(data),
        }
    }
}

impl<'data> Cursor for TCursor<'data> {
    type IReader<'ctx> = TIntegerReader<'data, 'ctx>;

    fn next<'ctx>(&'ctx mut self) -> TinyResult<Event<Self::IReader<'ctx>>> {
        Ok(if self.scanner.rem() == 0 {
            Event::EndOfStream
        } else {
            let octet = self.scanner.read()?;
            if let Ok(text) = from_utf8(&[octet]) {
                match text {
                    // null
                    "N" => Event::Null(TinyType::Null),
                    // null int
                    "Z" => Event::Null(TinyType::Integer),
                    // integer value
                    "I" => Event::Integer(TIntegerReader { cursor: self }),
                    type_code => return parse_error(format!("Invalid type: {}", type_code)),
                }
            } else {
                return parse_error(format!("Invalid UTF-8 character: {:x}", octet));
            }
        })
    }
}

#[derive(Debug)]
pub struct TIntegerReader<'data, 'ctx> {
    cursor: &'ctx mut TCursor<'data>,
}

impl<'data, 'ctx> IntegerReader for TIntegerReader<'data, 'ctx> {
    fn read_i64(&mut self) -> TinyResult<i64> {
        // for our dumb format, a single ascii 0-9 number character is parsed
        let octet = self.cursor.scanner.read()?;
        let value: i64 = if let Ok(text) = from_utf8(&[octet]) {
            if let Ok(val) = text.parse() {
                val
            } else {
                return parse_error(format!("Could not parse text to int: {}", text));
            }
        } else {
            return parse_error(format!("Could not parse UTF-8: {:x}", octet));
        };

        Ok(value)
    }
}

/// Encapsulates two statically possible cursor types.
pub enum PossibleCursor<B, T>
where
    B: Cursor,
    T: Cursor,
{
    Binary(B),
    Text(T),
}

/// Parses some data, the first byte of ascii `'B'` or `'T'` indicates format.
pub fn open_cursor(data: &[u8]) -> TinyResult<PossibleCursor<BCursor, TCursor>> {
    let mut scanner = ByteScanner::new(data);
    Ok(match scanner.read()? {
        // ASCII 'B'
        0x42 => PossibleCursor::Binary(BCursor::new(&data[1..])),
        // ASCII 'T'
        0x54 => PossibleCursor::Text(TCursor::new(&data[1..])),
        type_octet => return parse_error(format!("Could not parse header: {:x}", type_octet)),
    })
}

#[cfg(test)]
mod test {
    use super::*;
    use rstest::*;

    #[test]
    fn binary() -> TinyResult<()> {
        let mut cursor = BCursor::new(&[0x00, 0x01, 0x10, 0x2A]);
        match cursor.next() {
            Ok(Event::Null(TinyType::Null)) => {}
            _ => panic!("Expected null"),
        };
        match cursor.next() {
            Ok(Event::Null(TinyType::Integer)) => {}
            something => panic!("Expected null int: {:?}", something),
        };
        match cursor.next() {
            Ok(Event::Integer(ireader)) => {
                assert_eq!(42, ireader.read_i64()?);
            }
            something => panic!("Expected 9: {:?}", something),
        };

        Ok(())
    }

    #[test]
    fn text() -> TinyResult<()> {
        let mut cursor = TCursor::new("NZI9".as_bytes());
        match cursor.next() {
            Ok(Event::Null(TinyType::Null)) => {}
            something => panic!("Expected null: {:?}", something),
        };
        match cursor.next() {
            Ok(Event::Null(TinyType::Integer)) => {}
            something => panic!("Expected null int: {:?}", something),
        };
        match cursor.next() {
            Ok(Event::Integer(ireader)) => {
                assert_eq!(9, ireader.read_i64()?);
            }
            something => panic!("Expected 9: {:?}", something),
        };

        Ok(())
    }

    fn process_cursor<C: Cursor>(mut cursor: C) -> TinyResult<()> {
        match cursor.next() {
            Ok(Event::Null(TinyType::Integer)) => {}
            something => panic!("Expected null int: {:?}", something),
        };
        match cursor.next() {
            Ok(Event::Null(TinyType::Null)) => {}
            something => panic!("Expected null: {:?}", something),
        };
        match cursor.next() {
            Ok(Event::Integer(ireader)) => {
                assert_eq!(6, ireader.read_i64()?);
            }
            something => panic!("Expected 6: {:?}", something),
        };
        Ok(())
    }

    #[rstest]
    #[case::binary(&[0x42, 0x01, 0x00, 0x10, 0x6])]
    #[case::text("TZNI6".as_bytes())]
    fn both(#[case] data: &[u8]) -> TinyResult<()> {
        match open_cursor(data)? {
            PossibleCursor::Binary(bcursor) => process_cursor(bcursor),
            PossibleCursor::Text(tcursor) => process_cursor(tcursor),
        }
    }
}
