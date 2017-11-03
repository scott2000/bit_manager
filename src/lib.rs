//! A crate for reading and writing bits from various streams
//!
//! # Writing
//! ```
//! # extern crate bit_manager;
//! use bit_manager::{BitWriter, BitWrite};
//!
//! # fn main() {
//! let mut writer = BitWriter::new(Vec::new());
//!
//! writer.write(&[false, true, false, false, true, false, false, false]).unwrap();
//! writer.write(&b'i').unwrap();
//!
//! assert_eq!(writer.into_inner().unwrap(), b"Hi");
//! # }
//! ```
//!
//! # Reading
//! ```
//! # extern crate bit_manager;
//! use bit_manager::{BitReader, BitRead};
//!
//! # fn main() {
//! let mut reader = BitReader::new(&b"Hi"[..]);
//!
//! assert_eq!(reader.read::<[bool; 8]>().unwrap(), [false, true, false, false, true, false, false, false]);
//! assert_eq!(reader.read::<u8>().unwrap(), b'i');
//! # }
//! ```
#![deny(missing_docs)]

/// A macro for creating BitStore implementations
///
/// ## Usage
///
/// ```
/// # /*
/// bit_store! {
///     for Type {
///         (reader) => { ... },
///         (self, writer) => { ... },
///     };
///     impl<T: Trait> for Type<T> {
///         (reader) => { ... }
///         (self, writer) => { ... }
///     };
/// }
/// # */
/// ```
///
/// Expands into:
///
/// ```
/// # /*
/// impl BitStore for Type {
///     fn read_from<R: BitRead>(reader: &mut R) -> Result<Type> { ... }
///     fn write_to<W: BitWrite>(&self, writer: &mut W) -> Result<()> { ... }
/// }
///
/// impl<T: Trait> BitStore for Type<T> {
///     fn read_from<R: BitRead>(reader: &mut R) -> Result<Type> { ... }
///     fn write_to<W: BitWrite>(&self, writer: &mut W) -> Result<()> { ... }
/// }
/// # */
/// ```
///
/// ## Example
///
/// ```
/// # #[macro_use]
/// # extern crate bit_manager;
/// struct ByteWrapper(u8);
///
/// bit_store! {
///     for ByteWrapper {
///         (reader) => { Ok(ByteWrapper(reader.read_byte()?)) },
///         (self, writer) => { writer.write_byte(self.0) },
///     };
/// }
///
/// # fn main() {}
/// ```
#[macro_export]
macro_rules! bit_store {
    { $( $(impl<$($t: ident $(: $b: ident $(+ $x: ident)*)*),+>)* for $ty: ty {
        ( $r: ident ) => $read: block,
        ( $self: ident, $w: ident ) => $write: block,
    }; )+ } => { $(
        impl$(<$($t $(: $b $(+ $x)*)*, )+>)* $crate::BitStore for $ty {
            fn read_from<R: $crate::BitRead>($r: &mut R) -> $crate::Result<Self> $read
            fn write_to<W: $crate::BitWrite>(&$self, $w: &mut W) -> $crate::Result<()> $write
        }
    )+ };
}

macro_rules! const_bit_store {
    { $(impl<$($t: ident $(: $b: ident $(+ $x: ident)*)*),+>)* const $ty: ty {
        $read: expr,
        $write: expr,
    }; } => {
        impl$(<$($t $(: $b $(+ $x)*)*, )+>)* $crate::BitStore for $ty {
            fn read_from<R: $crate::BitRead>(_: &mut R) -> $crate::Result<Self> { $read }
            fn write_to<W: $crate::BitWrite>(&self, _: &mut W) -> $crate::Result<()> { $write }
        }
    };
}

/// A macro for creating BitConvert implementations
///
/// ## Usage
///
/// ```
/// # /*
/// bit_convert! {
///     for Convert: Type {
///         (self, reader) => { ... },
///         (self, value, writer) => { ... },
///     };
///     impl<T: Trait> for Convert: T {
///         (self, reader) => { ... },
///         (self, value, writer) => { ... },
///     };
///     impl<T: Trait, F: Trait> for Convert<F>: T {
///         (self, reader) => { ... },
///         (self, value, writer) => { ... },
///     };
/// }
/// # */
/// ```
///
/// Expands into:
///
/// ```
/// # /*
/// impl BitConvert<Type> for Convert {
///     fn read_value_from<R: BitRead>(&self, reader: &mut R) -> Result<Type> { ... }
///     fn write_value_to<W: BitWrite>(&self, value: &Type, writer: &mut W) -> Result<()> { ... }
/// }
///
/// impl<T: Trait> BitConvert<T> for Convert {
///     fn read_value_from<R: BitRead>(&self, reader: &mut R) -> Result<T> { ... }
///     fn write_value_to<W: BitWrite>(&self, value: &T, writer: &mut W) -> Result<()> { ... }
/// }
///
/// impl<T: Trait, F: Trait> BitConvert<T> for Convert<F> {
///     fn read_value_from<R: BitRead>(&self, reader: &mut R) -> Result<T> { ... }
///     fn write_value_to<W: BitWrite>(&self, value: &T, writer: &mut W) -> Result<()> { ... }
/// }
/// # */
/// ```
///
/// ## Example
///
/// ```
/// # #![allow(dead_code)]
/// # #[macro_use]
/// # extern crate bit_manager;
/// struct ByteConverter;
///
/// bit_convert! {
///     for ByteConverter: u8 {
///         (self, reader) => { reader.read_byte() },
///         (self, value, writer) => { writer.write_byte(*value) },
///     };
/// }
///
/// # fn main() {}
/// ```
#[macro_export]
macro_rules! bit_convert {
    { $( $(impl<$($t: ident $(: $b: ident $(+ $x: ident)*)*),+>)* for $ty: ty: $return: ty {
        ( $self_r: ident, $r: ident ) => $read: block,
        ( $self_w: ident, $v: ident, $w: ident ) => $write: block,
    }; )+ } => { $(
        impl$(<$($t $(: $b $(+ $x)*)*, )+>)* $crate::BitConvert<$return> for $ty {
            fn read_value_from<R: $crate::BitRead>(&$self_r, $r: &mut R) -> $crate::Result<$return> $read
            fn write_value_to<W: $crate::BitWrite>(&$self_w, $v: &$return, $w: &mut W) -> $crate::Result<()> $write
        }
    )+ };
}

pub mod prelude;
pub mod conversions;
#[cfg(test)]
mod test;

use std::error;
use std::result;
use std::fmt;
use std::mem;

use conversions::*;
use std::io::{Read, Write};

/// A trait for types that can read bits
pub trait BitRead: Sized {
    /// Reads a single bit.
    fn read_bit(&mut self) -> Result<bool>;

    /// Reads a single byte.
    ///
    /// *Default implementation is unoptimized and should be overridden*
    fn read_byte(&mut self) -> Result<u8> {
        let mut byte = 0;
        for bit in (0..8).rev() {
            if self.read_bit()? {
                byte |= 1 << bit;
            }
        }
        Ok(byte)
    }

    /// Reads a value that implements [`BitStore`](trait.BitStore.html) using the `read_from` function.
    fn read<T: BitStore>(&mut self) -> Result<T> {
        T::read_from(self)
    }

    /// Reads a value using a converter that implements [`BitConvert`](trait.BitConvert.html) with the `read_value_from` function.
    fn read_using<T, C>(&mut self, converter: &C) -> Result<T> where C: BitConvert<T> {
        converter.read_value_from(self)
    }
}

/// A trait for types that can write bits
pub trait BitWrite: Sized {
    /// Writes a single bit.
    fn write_bit(&mut self, bit: bool) -> Result<()>;

    /// Writes a single byte.
    ///
    /// *Default implementation is unoptimized and should be overridden*
    fn write_byte(&mut self, byte: u8) -> Result<()> {
        for bit in (0..8).rev() {
            self.write_bit((byte >> bit) & 1 == 1)?;
        }
        Ok(())
    }

    /// Writes a value that implements [`BitStore`](trait.BitStore.html) using the `write_to` function.
    fn write<T: BitStore>(&mut self, value: &T) -> Result<()> {
        value.write_to(self)
    }

    /// Writes a value using a converter that implements [`BitConvert`](trait.BitConvert.html) with the `write_value_to` function.
    fn write_using<T, C>(&mut self, value: &T, converter: &C) -> Result<()> where C: BitConvert<T> {
        converter.write_value_to(value, self)
    }
}

/// A trait for storing a value
pub trait BitStore: Sized {
    /// Reads a value from the given reader.
    fn read_from<R: BitRead>(reader: &mut R) -> Result<Self>;

    /// Writes this value to the given writer.
    fn write_to<W: BitWrite>(&self, writer: &mut W) -> Result<()>;
}

/// A trait for a converter that allows storing of types that don't implement [BitStore](trait.BitStore.html)
pub trait BitConvert<T>: Sized {
    /// Reads a value from the given reader.
    fn read_value_from<R: BitRead>(&self, reader: &mut R) -> Result<T>;

    /// Writes this value to the given writer.
    fn write_value_to<W: BitWrite>(&self, value: &T, writer: &mut W) -> Result<()>;
}

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
    /// **Allows precision to last bit, but requires data created by [BitWriter](struct.BitWriter.html) and often extra space.**
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
/// # extern crate bit_manager;
/// use bit_manager::{BitReader, BitRead};
///
/// # fn main() {
/// let mut reader = BitReader::new(&b"Hi"[..]);
///
/// assert_eq!(reader.read::<[bool; 8]>().unwrap(), [false, true, false, false, true, false, false, false]);
/// assert_eq!(reader.read::<u8>().unwrap(), b'i');
/// # }
/// ```
pub struct BitReader<T: Read> {
    input: T,
    buffer: BitBuffer,
    precision: Precision,
    closed: bool,
}

impl<T: Read> BitReader<T> {
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

    /// Returns `true` if the internal buffer is aligned to a byte.
    pub fn is_aligned(&self) -> bool {
        self.buffer.is_aligned()
    }

    /// Aligns the stream to the next byte.
    pub fn align(&mut self) -> Result<()> {
        while !self.is_aligned() {
            self.read_bit()?;
        }
        Ok(())
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

impl<T: Read> BitRead for BitReader<T> {
    fn read_bit(&mut self) -> Result<bool> {
        self.update();
        self.buffer.pop_bit_left()
    }

    fn read_byte(&mut self) -> Result<u8> {
        self.update();
        self.buffer.pop_left()
    }
}

/// A wrapper for any type implementing `io::Write` that allows the writing of individual bits
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
///
/// ## Example
/// ```
/// # extern crate bit_manager;
/// use bit_manager::{BitWriter, BitWrite};
///
/// # fn main() {
/// let mut writer = BitWriter::new(Vec::new());
///
/// writer.write(&[false, true, false, false, true, false, false, false]).unwrap();
/// writer.write(&b'i').unwrap();
///
/// assert_eq!(writer.into_inner().unwrap(), b"Hi");
/// # }
/// ```
pub struct BitWriter<T: Write> {
    output: Option<T>,
    buffer: BitBuffer,
    precision: Precision,
}

impl<T: Write> BitWriter<T> {
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
}

impl<T: Write> BitWrite for BitWriter<T> {
    fn write_bit(&mut self, bit: bool) -> Result<()> {
        self.buffer.push_bit_right(bit)?;
        self.flush()?;
        Ok(())
    }

    fn write_byte(&mut self, byte: u8) -> Result<()> {
        self.buffer.push_right(byte)?;
        self.flush()?;
        Ok(())
    }
}

impl<T: Write> Drop for BitWriter<T> {
    #[allow(unused_must_use)]
    fn drop(&mut self) {
        self.close_mut();
    }
}

bit_store! {
    for bool {
        (reader) => { reader.read_bit() },
        (self, writer) => { writer.write_bit(*self) },
    };
    for u8 {
        (reader) => { reader.read_byte() },
        (self, writer) => { writer.write_byte(*self) },
    };
    for i8 {
        (reader) => { reader.read_byte().map(|b| b as i8) },
        (self, writer) => { writer.write_byte(*self as u8) },
    };
}

macro_rules! impl_bit_convert {
    ($( $s: expr => $( $v: ident ),+  );+) => { $( $( bit_store! { for $v {
        (reader) => { Ok(Self::from_be( unsafe { mem::transmute::<[u8; $s], Self>(reader.read()?) } )) },
        (self, writer) => { writer.write( & unsafe { mem::transmute::<Self, [u8; $s]>((*self).to_be()) } ) },
    }; } )+ )+ }
}

impl_bit_convert!(2 => u16, i16; 4 => u32, i32; 8 => u64, i64);

macro_rules! impl_bit_convert_float {
    ($( $s: expr => $u: ident => $v: ident  );+) => { $( bit_store! { for $v {
        (reader) => { Ok( unsafe { mem::transmute($u::from_be(mem::transmute::<[u8; $s], $u>(reader.read()?))) } ) },
        (self, writer) => { writer.write( & unsafe { mem::transmute::<$u, [u8; $s]>(mem::transmute::<Self, $u>(*self).to_be()) } ) },
    }; } )+ }
}

impl_bit_convert_float!(4 => u32 => f32; 8 => u64 => f64);

bit_store! {
    for String {
        (reader) => { reader.read_using(&StringConverter::default()) },
        (self, writer) => { writer.write_using(self, &StringConverter::default()) },
    };
    impl<T: BitStore> for Option<T> {
        (reader) => {
            if reader.read_bit()? {
                Ok(Some(reader.read()?))
            } else {
                Ok(None)
            }
        },
        (self, writer) => {
            if let &Some(ref value) = self {
                writer.write_bit(true)?;
                writer.write(value)
            } else {
                writer.write_bit(false)
            }
        },
    };
    impl<T: BitStore, F: BitStore> for result::Result<T, F> {
        (reader) => {
            if reader.read_bit()? {
                Ok(Ok(reader.read()?))
            } else {
                Ok(Err(reader.read()?))
            }
        },
        (self, writer) => {
            match self {
                &Ok(ref value) => {
                    writer.write_bit(true)?;
                    writer.write(value)
                },
                &Err(ref value) => {
                    writer.write_bit(false)?;
                    writer.write(value)
                }
            }
        },
    };
}

macro_rules! impl_array {
    ($x: expr; $a: ident $( $b: ident )*) => {
        impl_array! { $x - 1; $( $b )* }
        bit_store! {
            impl<T: BitStore> for [T; $x] {
                (reader) => { Ok([reader.$a()? $(, reader.$b()?)*]) },
                (self, writer) => {
                    for item in self.iter() {
                        writer.write(item)?;
                    }
                    Ok(())
                },
            };
        }
    };
    ($x: expr; ) => {
        const_bit_store! {
            impl<T> const [T; $x] {
                Ok([]),
                Ok(()),
            };
        }
    };
}

impl_array! { 32; read read read read read read read read read read read read read read read read read read read read read read read read read read read read read read read read }

const_bit_store! {
    const () {
        Ok(()),
        Ok(()),
    };
}