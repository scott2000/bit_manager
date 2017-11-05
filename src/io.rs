//! Allows the reading and writing of information from streams.

use data::*;
use buffer::*;

use std::io::{Read, Write};
use std::mem;

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

    /// Reads a value that implements [`BitStore`] using the `read_from` function.
    ///
    /// [`BitStore`]: http://docs.rs/bit_manager/0.5.3/bit_manager/data/trait.BitStore.html
    fn read<T: BitStore>(&mut self) -> Result<T> {
        T::read_from(self)
    }

    /// Reads a value using a converter that implements [`BitConvert`] with the `read_value_from` function.
    ///
    /// [`BitConvert`]: http://docs.rs/bit_manager/0.5.3/bit_manager/data/trait.BitConvert.html
    fn read_using<T, C>(&mut self, converter: &C) -> Result<T> where C: BitConvert<T> {
        converter.read_value_from(self)
    }

    /// Reads values that implement [`BitStore`] to a buffer. Returns the number of values read.
    ///
    /// [`BitStore`]: http://docs.rs/bit_manager/0.5.3/bit_manager/data/trait.BitStore.html
    fn read_to_buffer<T, B>(&mut self, mut buffer: B) -> usize where T: BitStore, B: AsMut<[T]> {
        let mut read = 0;
        'read: for item in buffer.as_mut().iter_mut() {
            match self.read() {
                Ok(value) => *item = value,
                Err(_) => break 'read,
            }
            read += 1;
        }
        read
    }


    /// Reads values using a converter that implements [`BitConvert`] to a buffer. Returns the number of values read.
    ///
    /// [`BitConvert`]: http://docs.rs/bit_manager/0.5.3/bit_manager/data/trait.BitConvert.html
    fn read_to_buffer_using<T, B, C>(&mut self, mut buffer: B, converter: &C) -> usize where B: AsMut<[T]>, C: BitConvert<T> {
        let mut read = 0;
        'read: for item in buffer.as_mut().iter_mut() {
            match self.read_using(converter) {
                Ok(value) => *item = value,
                Err(_) => break 'read,
            }
            read += 1;
        }
        read
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

    /// Writes a value that implements [`BitStore`] using the `write_to` function.
    ///
    /// [`BitStore`]: http://docs.rs/bit_manager/0.5.3/bit_manager/data/trait.BitStore.html
    fn write<T: BitStore>(&mut self, value: &T) -> Result<()> {
        value.write_to(self)
    }

    /// Writes a value using a converter that implements [`BitConvert`] with the `write_value_to` function.
    ///
    /// [`BitConvert`]: http://docs.rs/bit_manager/0.5.3/bit_manager/data/trait.BitConvert.html
    fn write_using<T, C>(&mut self, value: &T, converter: &C) -> Result<()> where C: BitConvert<T> {
        converter.write_value_to(value, self)
    }

    /// Writes values that implement [`BitStore`] from a buffer. Returns the number of values written.
    ///
    /// [`BitStore`]: http://docs.rs/bit_manager/0.5.3/bit_manager/data/trait.BitStore.html
    fn write_buffer<T, B>(&mut self, buffer: B) -> usize where T: BitStore, B: AsRef<[T]> {
        let mut written = 0;
        'write: for item in buffer.as_ref().iter() {
            match self.write(item) {
                Ok(()) => written += 1,
                Err(_) => break 'write,
            }
        }
        written
    }

    /// Writes values using a converter that implements [`BitConvert`] from a buffer. Returns the number of values written.
    ///
    /// [`BitConvert`]: http://docs.rs/bit_manager/0.5.3/bit_manager/data/trait.BitConvert.html
    fn write_buffer_using<T, B, C>(&mut self, buffer: B, converter: &C) -> usize where B: AsRef<[T]>, C: BitConvert<T> {
        let mut written = 0;
        'write: for item in buffer.as_ref().iter() {
            match self.write_using(item, converter) {
                Ok(()) => written += 1,
                Err(_) => break 'write,
            }
        }
        written
    }
}

/// A wrapper for any type implementing `io::Read` that allows the reading of individual bits
///
/// ## Example
/// ```
/// # extern crate bit_manager; fn main() { test().unwrap(); } fn test() -> bit_manager::Result<()> {
/// use bit_manager::{BitReader, BitRead};
///
/// let mut reader = BitReader::new([0b01101110u8, 0b10100000u8].as_ref());
///
/// assert_eq!(reader.read_bit()?, false);
/// assert_eq!(reader.read_bit()?, true);
/// assert_eq!(reader.read_bit()?, true);
/// assert_eq!(reader.read_byte()?, 0b01110101);
/// # Ok(()) }
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
/// # extern crate bit_manager; fn main() { test().unwrap(); } fn test() -> bit_manager::Result<()> {
/// use bit_manager::{BitWriter, BitWrite};
///
/// let mut writer = BitWriter::new(Vec::new());
///
/// writer.write_bit(false)?;
/// writer.write_bit(true)?;
/// writer.write_bit(true)?;
/// writer.write_byte(0b01110101)?;
///
/// assert_eq!(writer.into_inner()?, [0b01101110u8, 0b10100000u8]);
/// # Ok(()) }
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

    /// Creates a new bit writer with the given writer and [`Precision`]
    ///
    /// [`Precision`]: http://docs.rs/bit_manager/0.5.3/bit_manager/buffer/enum.Precision.html
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
                Ok(n) if n == buf.len() => Ok(self.buffer.bits() as usize),
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