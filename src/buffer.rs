//! Provides a way to convert between storing individual bits and storing
//! whole bytes (for use in I/O operations).

use std::{fmt, error, result};

/// An enum for possible errors when reading and writing bits
#[derive(Debug)]
pub enum Error {
    /// An unexpected empty buffer
    BufferEmpty,

    /// An unexpected full buffer
    BufferFull,

    /// An unexpected closed buffer
    BufferClosed,

    /// An unexpected failed conversion
    ConversionFailed,

    /// An unexpected bit overflow
    BitOverflow {
        /// The number of bits given
        bits: u8,

        /// The number of bits expected
        expected: u8,
    },

    /// Another error containing a message
    OtherError {
        /// A message describing the error, unknown error if none is specified
        message: Option<String>,
    },
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        match *self {
            Error::BufferEmpty => write!(f, "buffer empty"),
            Error::BufferFull => write!(f, "buffer full"),
            Error::BufferClosed => write!(f, "buffer closed"),
            Error::ConversionFailed => write!(f, "conversion failed"),
            Error::BitOverflow { bits, expected } => write!(f, "bit overflow ({} > {})", bits, expected),
            Error::OtherError { ref message } => {
                if let &Some(ref message) = message {
                    write!(f, "bit error ({})", message)
                } else {
                    write!(f, "unknown error")
                }
            },
        }
    }
}

impl error::Error for Error {
    fn description(&self) -> &'static str {
        match *self {
            Error::BufferEmpty => "buffer empty",
            Error::BufferFull => "buffer full",
            Error::BufferClosed => "buffer closed",
            Error::ConversionFailed => "conversion failed",
            Error::BitOverflow { .. } => "bit overflow",
            Error::OtherError { .. } => "bit error",
        }
    }
}

/// An enum that represents how a stream is terminated
#[derive(Debug)]
pub enum Precision {
    /// Represents a stream terminated by all zeroes in order to align the
    /// end to the next byte.
    ///
    /// **Only precise to last byte.**
    ///
    /// ## Usage
    ///
    /// * 0110 => 0110(0000)
    /// * 0110001 => 0110001(0)
    /// * 01001000 => 01001000
    Byte,

    /// Represents a stream terminated by a one bit followed by all zeroes
    /// in order to align the end to the next byte.
    ///
    /// **Allows precision to last bit, but requires data created by a
    /// [`BitWriter`](struct.BitWriter.html) and often extra space.**
    ///
    /// ## Usage
    ///
    /// * 0110 => 0110(1000)
    /// * 0110001 => 0110001(1)
    /// * 01001000 => 01001000(10000000)
    Bit,
}

/// A specialized Result type for bit I/O operations
pub type Result<T> = result::Result<T, Error>;

/// A buffer that stores up to 64 bits and allows pushing and popping both bits
/// and bytes from either side
#[derive(Debug, Clone)]
pub struct BitBuffer {
    buffer: u64,
    bits: u8,
}

impl BitBuffer {
    /// Creates an empty buffer.
    pub fn new() -> BitBuffer {
        BitBuffer {
            buffer: 0,
            bits: 0,
        }
    }

    /// Pushes all current bits left and adds a byte to the right.
    pub fn push_right(&mut self, value: u8) -> Result<()> {
        if self.bits > 56 {
            return Err(Error::BufferFull);
        }
        self.buffer = self.buffer << 8 | value as u64;
        self.bits += 8;
        Ok(())
    }

    /// Pushes all current bits right and pops a byte from the right.
    pub fn pop_right(&mut self) -> Result<u8> {
        if self.bits < 8 {
            return Err(Error::BufferEmpty);
        }
        let value = (self.buffer & 0xff) as u8;
        self.buffer >>= 8;
        self.bits -= 8;
        Ok(value)
    }

    /// Adds a byte to the left.
    pub fn push_left(&mut self, value: u8) -> Result<()> {
        if self.bits > 56 {
            return Err(Error::BufferFull);
        }
        self.buffer |= (value as u64) << self.bits;
        self.bits += 8;
        Ok(())
    }

    /// Pops a byte from the left.
    pub fn pop_left(&mut self) -> Result<u8> {
        if self.bits < 8 {
            return Err(Error::BufferEmpty);
        }
        let value = (self.buffer >> self.bits-8 & 0xff) as u8;
        self.buffer &= !((0xff as u64) << self.bits-8);
        self.bits -= 8;
        Ok(value)
    }

    /// Pushes all current bits left and adds a bit to the right.
    pub fn push_bit_right(&mut self, value: bool) -> Result<()> {
        if self.bits > 63 {
            return Err(Error::BufferFull);
        }
        if value {
            self.buffer = self.buffer << 1 | 1;
        } else {
            self.buffer <<= 1;
        }
        self.bits += 1;
        Ok(())
    }

    /// Pushes all current bits right and pops a bit from the right.
    pub fn pop_bit_right(&mut self) -> Result<bool> {
        if self.bits < 1 {
            return Err(Error::BufferEmpty);
        }
        let value = self.buffer & 1 == 1;
        self.buffer >>= 1;
        self.bits -= 1;
        Ok(value)
    }

    /// Adds a bit to the left.
    pub fn push_bit_left(&mut self, value: bool) -> Result<()> {
        if self.bits > 63 {
            return Err(Error::BufferFull);
        }
        if value {
            self.buffer |= 1 << self.bits;
        }
        self.bits += 1;
        Ok(())
    }

    /// Pops a bit from the left.
    pub fn pop_bit_left(&mut self) -> Result<bool> {
        if self.bits < 1 {
            return Err(Error::BufferEmpty);
        }
        let value = self.buffer >> self.bits-1 & 1 == 1;
        self.buffer &= !(1 << self.bits-1);
        self.bits -= 1;
        Ok(value)
    }

    /// Returns the number of bits in the buffer.
    pub fn bits(&self) -> u8 {
        self.bits
    }

    /// Returns the number of whole bytes in the buffer.
    pub fn bytes(&self) -> u8 {
        self.bits/8
    }

    /// Returns `true` if the buffer is empty and `false` otherwise.
    pub fn is_empty(&self) -> bool {
        self.bits == 0
    }

    /// Returns `true` if the buffer is aligned to a byte.
    pub fn is_aligned(&self) -> bool {
        self.bits%8 == 0
    }

    /// Returns `true` if the buffer has a whole byte and `false` otherwise.
    pub fn has_byte(&self) -> bool {
        self.bits >= 8
    }

    /// Returns `true` if the buffer has a bit and `false` otherwise.
    pub fn has_bit(&self) -> bool {
        self.bits >= 1
    }

    /// Returns `true` if the buffer has room for a whole byte and `false` otherwise.
    pub fn can_take_byte(&self) -> bool {
        self.bits <= 56
    }

    /// Returns `true` if the buffer has room for a bit and `false` otherwise.
    pub fn can_take_bit(&self) -> bool {
        self.bits <= 63
    }

    /// Returns the number of whole bytes that can be added.
    pub fn byte_space(&self) -> u8 {
        (64-self.bits) / 8
    }

    /// Returns the number of whole bits that can be added.
    pub fn bit_space(&self) -> u8 {
        64-self.bits
    }
}

impl fmt::Display for BitBuffer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.bits == 0 {
            write!(f, "[]")
        } else {
            let mut buf_str = format!("{:b}", self.buffer);
            while (buf_str.len() as u8) < self.bits {
                buf_str.insert(0, '0');
            }
            write!(f, "[{}]", buf_str)
        }
    }
}