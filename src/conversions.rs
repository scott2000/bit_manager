//! Provides converters for reading and writing values using stucts

use super::*;
use std::io;

/// A trait for reading values using a converter
pub trait BitRead<T>: Sized {
    /// Reads a value from the given reader.
    fn read_value_from<R: io::Read>(&self, reader: &mut BitReader<R>) -> Result<T>;
}

/// A trait for writing values using a converter
pub trait BitWrite<T>: Sized {
    /// Writes a value to the given writer.
    fn write_value_to<W: io::Write>(&self, value: T, writer: &mut BitWriter<W>) -> Result<()>;
}

/// An enum that allows the writing and reading of strings using various methods
#[derive(Debug)]
pub enum StringConverter {
    /// Prefixes the string with length.
    ///
    /// This is the default option. The recommended number of bits for the prefix is 32.
    LengthPrefixed {
        /// The number of bits in the prefix
        prefix_bits: u8,
    },

    /// Terminates the string with a null character (`\0`). The string must not contain a null character.
    ///
    /// This option is recommended if it is possible to guarantee that the string will never contain a null character.
    NullTerminated,

    /// Writes a string with a specified fixed length. If the string is shorter, it will have
    /// null characters (`\0`) appended until it is the right length.
    ///
    /// This option is only recommended if it is known in advance how long the string will be.
    FixedLength {
        /// The length of the string
        length: u32,
    },
}

impl Default for StringConverter {
    fn default() -> Self {
        StringConverter::LengthPrefixed {
            prefix_bits: 32,
        }
    }
}

impl BitReadable for StringConverter {
    fn read_from<R: io::Read>(reader: &mut BitReader<R>) -> Result<Self> {
        Ok(
            if !reader.read_bit()? {
                StringConverter::LengthPrefixed {
                    prefix_bits: reader.read_byte()?,
                }
            } else if !reader.read_bit()? {
                StringConverter::NullTerminated
            } else {
                StringConverter::FixedLength {
                    length: reader.read::<u32>()?,
                }
            }
        )
    }
}

impl BitWritable for StringConverter {
    fn write_to<W: io::Write>(self, writer: &mut BitWriter<W>) -> Result<()> {
        match self {
            StringConverter::LengthPrefixed { prefix_bits } => {
                writer.write_bit(false)?;
                writer.write_byte(prefix_bits)
            },
            StringConverter::NullTerminated => {
                writer.write_bit(true)?;
                writer.write_bit(false)
            },
            StringConverter::FixedLength { length } => {
                writer.write_bit(true)?;
                writer.write_bit(true)?;
                writer.write(length)
            }
        }
    }
}

impl<'a> BitWritable for &'a StringConverter {
    fn write_to<W: io::Write>(self, writer: &mut BitWriter<W>) -> Result<()> {
        match self {
            &StringConverter::LengthPrefixed { prefix_bits } => {
                writer.write_bit(false)?;
                writer.write_byte(prefix_bits)
            },
            &StringConverter::NullTerminated => {
                writer.write_bit(true)?;
                writer.write_bit(false)
            },
            &StringConverter::FixedLength { length } => {
                writer.write_bit(true)?;
                writer.write_bit(true)?;
                writer.write(length)
            }
        }
    }
}

impl BitRead<String> for StringConverter {
    fn read_value_from<R: io::Read>(&self, reader: &mut BitReader<R>) -> Result<String> {
        let mut string = Vec::new();
        match *self {
            StringConverter::LengthPrefixed { prefix_bits } => {
                let mask = BitMask::bits(prefix_bits);
                let bytes: u32 = reader.read_using(&mask)?;
                for _ in 0..bytes {
                    string.push(reader.read_byte()?);
                }
            },
            StringConverter::NullTerminated => {
                loop {
                    let byte = reader.read_byte()?;
                    if byte == 0 {
                        break;
                    } else {
                        string.push(byte);
                    }
                }
            },
            StringConverter::FixedLength { length } => {
                for _ in 0..length {
                    string.push(reader.read_byte()?);
                }
            },
        }
        String::from_utf8(string).map_err(|_| Error::ConversionFailed)
    }
}

impl<T> BitWrite<T> for StringConverter where T: AsRef<str> {
    fn write_value_to<W: io::Write>(&self, value: T, writer: &mut BitWriter<W>) -> Result<()> {
        let value = value.as_ref();
        if value.len() > u32::max_value() as usize {
            return Err(Error::ConversionFailed);
        }
        match *self {
            StringConverter::LengthPrefixed { prefix_bits } => {
                let mask = BitMask::bits(prefix_bits);
                writer.write_using(value.len() as u32, &mask)?;
                writer.write_bytes(value.as_bytes()).map(|_| ())
            },
            StringConverter::NullTerminated => {
                for byte in value.as_bytes() {
                    if *byte == 0 {
                        return Err(Error::ConversionFailed);
                    }
                    writer.write_byte(*byte)?;
                }
                writer.write_byte(0)
            },
            StringConverter::FixedLength { length } => {
                let bytes = length as usize;
                if value.len() > bytes {
                    return Err(Error::ConversionFailed);
                }
                let extra = bytes-value.len();
                writer.write_bytes(value.as_bytes())?;
                for _ in 0..extra {
                    writer.write_byte(0)?;
                }
                Ok(())
            },
        }
    }
}

/// A struct that allows writing non-bit-length numbers
#[derive(Debug)]
pub struct BitMask {
    bits: u8,
}

impl BitMask {
    /// Creates a mask with the given number of bits.
    pub fn bits(bits: u8) -> BitMask {
        BitMask {
            bits,
        }
    }

    /// Creates a mask with the given number of bytes.
    pub fn bytes(bytes: u8) -> BitMask {
        BitMask {
            bits: bytes*8,
        }
    }
}

impl BitReadable for BitMask {
    fn read_from<R: io::Read>(reader: &mut BitReader<R>) -> Result<Self> {
        match reader.read_byte() {
            Ok(bits) => Ok(BitMask { bits }),
            Err(e) => Err(e),
        }
    }
}

impl BitWritable for BitMask {
    fn write_to<W: io::Write>(self, writer: &mut BitWriter<W>) -> Result<()> {
        writer.write_byte(self.bits)
    }
}

impl<'a> BitWritable for &'a BitMask {
    fn write_to<W: io::Write>(self, writer: &mut BitWriter<W>) -> Result<()> {
        writer.write_byte(self.bits)
    }
}

macro_rules! impl_bit_mask {
    ($( $u: ident $i: ident $b: expr ),+) => { $(
        impl BitRead<$u> for BitMask {
            fn read_value_from<R: io::Read>(&self, reader: &mut BitReader<R>) -> Result<$u> {
                if self.bits > $b {
                    return Err(Error::BitOverflow { bits: self.bits, expected: $b } );
                } else if self.bits == 0 {
                    return Ok(0);
                }
                let mut int = 0;
                let bytes = self.bits/8;
                for index in 0..bytes {
                    let read = reader.read_byte()?;
                    if read != 0 {
                        int |= (read as $u) << (self.bits - index*8 - 8);
                    }
                }
                let bits = self.bits%8;
                for index in 0..bits {
                    let read = reader.read_bit()?;
                    if read {
                        int |= 1 << (bits - index - 1);
                    }
                }
                Ok($u::from_le(int))
            }
        }

        impl BitRead<$i> for BitMask {
            fn read_value_from<R: io::Read>(&self, reader: &mut BitReader<R>) -> Result<$i> {
                Ok(BitRead::<$u>::read_value_from(self, reader)? as $i)
            }
        }

        impl BitWrite<$u> for BitMask {
            fn write_value_to<W: io::Write>(&self, value: $u, writer: &mut BitWriter<W>) -> Result<()> {
                if self.bits != 0 {
                    let int = u64::to_le(value as u64);
                    if self.bits > $b {
                        return Err(Error::BitOverflow { bits: self.bits, expected: $b } );
                    }
                    if int >> self.bits != 0 {
                        return Err(Error::ConversionFailed);
                    }
                    let bytes = self.bits/8;
                    for index in 0..bytes {
                        writer.write_byte((int >> (self.bits - 8*index - 8)) as u8)?;
                    }
                    let bits = self.bits%8;
                    for index in 0..bits {
                        writer.write_bit((int >> (bits - index - 1)) & 1 == 1)?;
                    }
                }
                Ok(())
            }
        }

        impl BitWrite<$i> for BitMask {
            fn write_value_to<W: io::Write>(&self, value: $i, writer: &mut BitWriter<W>) -> Result<()> {
                self.write_value_to(value as $u, writer)
            }
        }
    )+ }
}

impl_bit_mask!(u64 i64 64, u32 i32 32, u16 i16 16, u8 i8 8);