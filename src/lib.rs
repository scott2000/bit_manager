//! A crate for reading and writing bits from various streams
//!
//! # Writing
//! ```
//! extern crate bit_manager;
//! use bit_manager::BitWriter;
//!
//! # fn main() {
//! let mut writer = BitWriter::new(Vec::new());
//!
//! writer.write_bits(&[false, true, false, false, true, false, false, false]).unwrap();
//! writer.write(b'i').unwrap();
//!
//! assert_eq!(writer.into_inner().unwrap(), b"Hi");
//! # }
//! ```
//!
//! # Reading
//! ```
//! extern crate bit_manager;
//! use bit_manager::BitReader;
//!
//! # fn main() {
//! let mut reader = BitReader::new(&b"Hi"[..]);
//! let mut h = [false; 8];
//!
//! reader.read_bits(&mut h).unwrap();
//!
//! assert_eq!(h, [false, true, false, false, true, false, false, false]);
//! assert_eq!(reader.read_byte().unwrap(), b'i');
//! # }
//! ```
//!
#![deny(missing_docs)]

pub mod prelude;
pub mod conversions;

use std::error;
use std::result;
use std::fmt;
use std::io;
use std::mem;

use conversions::*;

/// An enum for possible errors when reading and writing bits
#[derive(Debug)]
pub enum Error {
    /// An unexpected empty buffer
    BufferEmpty,

    /// An unexpected full buffer
    BufferFull,

    /// An unexpected closed buffer
    BufferClosed,

    /// An unexpected closed buffer
    ConversionFailed,

    /// An unexpected bit overflow
    BitOverflow {
        /// The number of bits given
        bits: u8,

        /// The number of bits expected
        expected: u8,
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
        }
    }
}

/// A specialized Result type for bit I/O operations
pub type Result<T> = result::Result<T, Error>;

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
    /// **Allows precision to last bit, but requires data created by [BitWriter](struct.BitWriter.html) and often extra space.**
    ///
    /// ## Usage
    ///
    /// * 0110 => 0110(1000)
    /// * 0110001 => 0110001(1)
    /// * 01001000 => 01001000(10000000)
    Bit,
}

/// A buffer that stores up to 64 bits and remembers how many are being stored
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

/// A wrapper for any type implementing `io::Read` that allows the reading of individual bits
///
/// ## Example
/// ```
/// extern crate bit_manager;
/// use bit_manager::BitReader;
///
/// # fn main() {
/// let mut reader = BitReader::new(&b"Hi"[..]);
/// let mut h = [false; 8];
///
/// reader.read_bits(&mut h).unwrap();
///
/// assert_eq!(h, [false, true, false, false, true, false, false, false]);
/// assert_eq!(reader.read_byte().unwrap(), b'i');
/// # }
/// ```
pub struct BitReader<T: io::Read> {
    input: T,
    buffer: BitBuffer,
    precision: Precision,
    closed: bool,
}

impl<T: io::Read> BitReader<T> {
    /// Creates a new bit reader with the given reader. Uses `Precision::Byte` by default.
    pub fn new(reader: T) -> BitReader<T> {
        BitReader::new_with_precision(reader, Precision::Byte)
    }

    /// Creates a new bit reader with the given reader and precision.
    pub fn new_with_precision(reader: T, precision: Precision) -> BitReader<T> {
        BitReader {
            input: reader,
            buffer: BitBuffer::new(),
            precision,
            closed: false,
        }
    }

    /// Reads a value.
    pub fn read<V: BitReadable>(&mut self) -> Result<V> {
        V::read_from(self)
    }

    /// Reads a value using a converter.
    pub fn read_using<V, C>(&mut self, converter: &C) -> Result<V> where C: BitRead<V> {
        converter.read_value_from(self)
    }

    /// Loads data into a struct.
    pub fn load<V: BitLoadable>(&mut self, loader: &mut V) -> Result<()> {
        loader.load_from(self)
    }

    /// Returns `true` if the internal buffer is aligned to a byte.
    pub fn is_aligned(&self) -> bool {
        self.buffer.is_aligned()
    }

    /// Aligns the stream to the next byte.
    pub fn align(&mut self) -> Result<()> {
        while !self.is_aligned() {
            self.read_bit().map(|_| ())?;
        }
        Ok(())
    }

    /// Reads a single bit.
    pub fn read_bit(&mut self) -> Result<bool> {
        self.update();
        Ok(self.buffer.pop_bit_left()?)
    }

    /// Reads as many bits as possible into a buffer. Returns the number of bits read.
    pub fn read_bits(&mut self, buffer: &mut [bool]) -> Result<usize> {
        let mut read: usize = 0;
        for i in buffer.iter_mut() {
            self.update();
            match self.buffer.pop_bit_left() {
                Ok(bit) => {
                    *i = bit;
                    read += 1;
                },
                Err(_) if read > 0 => return Ok(read),
                Err(error) => return Err(error),
            }
        }
        Ok(read)
    }

    /// Reads a single byte.
    pub fn read_byte(&mut self) -> Result<u8> {
        self.update();
        Ok(self.buffer.pop_left()?)
    }

    /// Reads as many bytes as possible into a buffer. Returns the number of bytes read.
    pub fn read_bytes(&mut self, buffer: &mut [u8]) -> Result<usize> {
        let mut read: usize = 0;
        for i in buffer.iter_mut() {
            self.update();
            match self.buffer.pop_left() {
                Ok(byte) => {
                    *i = byte;
                    read += 1;
                },
                Err(_) if read > 0 => return Ok(read),
                Err(error) => return Err(error),
            }
        }
        Ok(read)
    }

    fn update(&mut self) {
        if !self.closed && self.buffer.can_take_byte() {
            let mut buf: Vec<u8> = Vec::new();
            for _ in 0..self.buffer.byte_space() {
                buf.push(0);
            }
            if let Ok(n) = self.input.read(&mut buf) {
                if n > 0 {
                    for i in 0..n {
                        self.buffer.push_right(buf[i]).unwrap();
                    }
                    return;
                }
            }
            self.close();
        }
    }

    fn close(&mut self) {
        self.closed = true;
        if let Precision::Bit = self.precision {
            loop {
                if self.buffer.pop_bit_right().unwrap_or(true) {
                    break;
                }
            }
            self.precision = Precision::Byte;
        }
    }
}

/// A wrapper for any type implementing `io::Write` that allows the writing of individual bits
///
/// ## Example
/// ```
/// extern crate bit_manager;
/// use bit_manager::BitWriter;
///
/// # fn main() {
/// let mut writer = BitWriter::new(Vec::new());
///
/// writer.write_bits(&[false, true, false, false, true, false, false, false]).unwrap();
/// writer.write(b'i').unwrap();
///
/// assert_eq!(writer.into_inner().unwrap(), b"Hi");
/// # }
/// ```
///
/// ## Closing
///
/// When the writer is dropped, the contents of its buffer will be written out.
/// However, any errors that happen in the process of closing the buffer when the
/// writer is dropped will be ignored. Code that wishes to handle such errors must
/// manually call close before the writer is dropped. The internal buffer will be returned on success.
///
/// A failed flush operation will result in `Error::BufferClosed`. Any further operations
/// will also fail because the internal buffer may have been corrupted.
pub struct BitWriter<T: io::Write> {
    output: Option<T>,
    buffer: BitBuffer,
    precision: Precision,
}

impl<T: io::Write> BitWriter<T> {
    /// Creates a new bit writer with the given writer. Uses `Precision::Byte` by default.
    pub fn new(writer: T) -> BitWriter<T> {
        BitWriter::new_with_precision(writer, Precision::Byte)
    }

    /// Creates a new bit writer with the given writer and precision.
    pub fn new_with_precision(writer: T, precision: Precision) -> BitWriter<T> {
        BitWriter {
            output: Some(writer),
            buffer: BitBuffer::new(),
            precision,
        }
    }

    /// Writes a value.
    pub fn write<V: BitWritable>(&mut self, value: V) -> Result<()> {
        value.write_to(self)
    }

    /// Writes a value using a converter.
    pub fn write_using<V, C>(&mut self, value: V, converter: &C) -> Result<()> where C: BitWrite<V> {
        converter.write_value_to(value, self)
    }

    /// Returns `true` if the internal buffer is aligned to a byte.
    pub fn is_aligned(&self) -> bool {
        self.buffer.is_aligned()
    }

    /// Aligns the stream to the next byte.
    pub fn align(&mut self) -> Result<()> {
        while !self.is_aligned() {
            self.write_bit(false)?;
        }
        Ok(())
    }

    /// Writes a single bit.
    pub fn write_bit(&mut self, bit: bool) -> Result<()> {
        self.buffer.push_bit_right(bit)?;
        self.flush().and(Ok(()))
    }

    /// Writes as many bits as possible into a buffer. Returns the number of bits written.
    pub fn write_bits(&mut self, bits: &[bool]) -> Result<usize> {
        let mut written = 0;
        for bit in bits.iter() {
            match self.write_bit(*bit) {
                Ok(_) => {
                    written += 1;
                },
                Err(_) if written > 0 => return Ok(written),
                Err(error) => return Err(error),
            }
        }
        Ok(written)
    }

    /// Writes a single byte.
    pub fn write_byte(&mut self, byte: u8) -> Result<()> {
        self.buffer.push_right(byte)?;
        self.flush().and(Ok(()))
    }

    /// Writes as many bytes as possible into a buffer. Returns the number of bytes written.
    pub fn write_bytes(&mut self, bytes: &[u8]) -> Result<usize> {
        let mut written = 0;
        for byte in bytes.iter() {
            match self.write_byte(*byte) {
                Ok(_) => {
                    written += 1;
                },
                Err(_) if written > 0 => return Ok(written),
                Err(error) => return Err(error),
            }
        }
        Ok(written)
    }

    /// Flushes the internal buffer. Returns the number of bits left in the buffer.
    pub fn flush(&mut self) -> Result<usize> {
        if self.output.is_some() {
            let mut buf: Vec<u8> = Vec::new();
            while let Ok(byte) = self.buffer.pop_left() {
                buf.push(byte);
            }
            match self.output.as_mut().unwrap().write(&buf) {
                Ok(n) if n == buf.len() => Ok(self.buffer.bits as usize),
                _ => {
                    self.output = None;
                    Err(Error::BufferClosed)
                },
            }
        } else {
            Err(Error::BufferClosed)
        }
    }

    fn close_mut(&mut self) -> Result<()> {
        if self.output.is_some() {
            if let Precision::Bit = self.precision {
                self.buffer.push_bit_right(true)?;
                self.precision = Precision::Byte;
            }
            while self.buffer.bits() & 7 != 0 {
                self.buffer.push_bit_right(false)?;
            }
            self.flush().and(Ok(()))
        } else {
            Err(Error::BufferClosed)
        }
    }

    /// Returns the inner writer after closing and flushing the internal buffer.
    pub fn into_inner(mut self) -> Result<T> {
        if let Err(e) = self.close_mut() {
            return Err(e);
        }
        match mem::replace(&mut self.output, None) {
            Some(v) => Ok(v),
            None => Err(Error::BufferClosed),
        }
    }

    /// Flushes the remaining internal buffer and aligns bits to the next byte using the precision of this writer.
    pub fn close(mut self) -> Result<()> {
        self.close_mut()?;
        self.output = None;
        Ok(())
    }
}

impl<T: io::Write> Drop for BitWriter<T> {
    #[allow(unused_must_use)]
    fn drop(&mut self) {
        self.close_mut();
    }
}

/// A trait for loading data to a struct
///
/// **Used for structs that cannot be returned meaningfully or are using the reader to update their internal state.**
pub trait BitLoadable: Sized {
    /// Loads data for this struct.
    fn load_from<R: io::Read>(&mut self, reader: &mut BitReader<R>) -> Result<()>;
}

/// A trait for reading a value
pub trait BitReadable: Sized {
    /// Reads a value from the given reader.
    fn read_from<R: io::Read>(reader: &mut BitReader<R>) -> Result<Self>;
}

impl BitReadable for bool {
    fn read_from<R: io::Read>(reader: &mut BitReader<R>) -> Result<Self> {
        reader.read_bit()
    }
}

impl BitReadable for u8 {
    fn read_from<R: io::Read>(reader: &mut BitReader<R>) -> Result<Self> {
        reader.read_byte()
    }
}

/// A trait for writing a value
pub trait BitWritable: Sized {
    /// Writes this value to the given writer.
    fn write_to<W: io::Write>(self, writer: &mut BitWriter<W>) -> Result<()>;
}

impl BitWritable for bool {
    fn write_to<W: io::Write>(self, writer: &mut BitWriter<W>) -> Result<()> {
        writer.write_bit(self)
    }
}

impl BitWritable for u8 {
    fn write_to<W: io::Write>(self, writer: &mut BitWriter<W>) -> Result<()> {
        writer.write_byte(self)
    }
}

macro_rules! impl_bit_convert {
    ($( $u: ident $i: ident $b: expr ),+) => { $(
        impl BitReadable for $u {
            fn read_from<R: io::Read>(reader: &mut BitReader<R>) -> Result<Self> {
                reader.read_using(&BitMask::bits($b))
            }
        }
        impl BitReadable for $i {
            fn read_from<R: io::Read>(reader: &mut BitReader<R>) -> Result<Self> {
                reader.read_using(&BitMask::bits($b))
            }
        }
        impl BitWritable for $u {
            fn write_to<W: io::Write>(self, writer: &mut BitWriter<W>) -> Result<()> {
                writer.write_using(self, &BitMask::bits($b))
            }
        }
        impl BitWritable for $i {
            fn write_to<W: io::Write>(self, writer: &mut BitWriter<W>) -> Result<()> {
                writer.write_using(self, &BitMask::bits($b))
            }
        }
    )+ }
}

impl_bit_convert!(u64 i64 64, u32 i32 32, u16 i16 16);

impl BitReadable for String {
    fn read_from<R: io::Read>(reader: &mut BitReader<R>) -> Result<Self> {
        reader.read_using(&StringConverter::default())
    }
}

impl BitWritable for String {
    fn write_to<W: io::Write>(self, writer: &mut BitWriter<W>) -> Result<()> {
        writer.write_using(self, &StringConverter::default())
    }
}

impl<'a> BitWritable for &'a str {
    fn write_to<W: io::Write>(self, writer: &mut BitWriter<W>) -> Result<()> {
        writer.write_using(self, &StringConverter::default())
    }
}