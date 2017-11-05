//! Provides methods for reading and writing data both directly
//! (using [`BitStore`]) and indirectly
//! (using [`BitConvert`]).
//!
//! [`BitStore`]: http://docs.rs/bit_manager/0.5.3/bit_manager/data/trait.BitStore.html
//! [`BitConvert`]: http://docs.rs/bit_manager/0.5.3/bit_manager/data/trait.BitConvert.html

use io::*;
use buffer::*;

/// A trait for storing a value directly
///
/// ## Derive
///
/// `BitStore` can be derived using the [bit manager derive] crate.
///
/// ## Storage Primitives
/// * `bool`, `u8` (directly implemented)
/// * `u16`, `u32`, `u64`
/// * `i8`, `i16`, `i32`, `i64`
/// * `f32`, `f64`
/// * `String` (through [`StringConverter`])
/// * `Option<T>` where `T` can be stored
/// * `Result<T, F>` where `T` and `F` can be stored
/// * `[T; 0]` through `[T; 32]` where `T` can be stored
/// * `()` (the unit type) and all tuples with 2 through 26 storable values
///
/// [`StringConverter`]: http://docs.rs/bit_manager/0.5.3/bit_manager/data/enum.StringConverter.html
/// [bit manager derive]: http://docs.rs/bit_manager_derive
pub trait BitStore: Sized {
    /// Reads a value from the given reader.
    fn read_from<R: BitRead>(reader: &mut R) -> Result<Self>;

    /// Writes this value to the given writer.
    fn write_to<W: BitWrite>(&self, writer: &mut W) -> Result<()>;
}

/// A trait for a converter that allows the reading and writing of types though a converter
pub trait BitConvert<T>: Sized {
    /// Reads a value from the given reader.
    fn read_value_from<R: BitRead>(&self, reader: &mut R) -> Result<T>;

    /// Writes this value to the given writer.
    fn write_value_to<W: BitWrite>(&self, value: &T, writer: &mut W) -> Result<()>;
}

/// An enum that allows the reading and writing of strings using various methods
#[derive(Debug)]
pub enum StringConverter {
    /// Prefixes the string with length.
    ///
    /// This is the default option. The recommended number of bits for the prefix is 32.
    ///
    /// *Requires 2 bits to store converter for recommended number of bits, otherwise 7 bits to store*
    LengthPrefixed {
        /// The number of bits in the prefix
        prefix_bits: u8,
    },

    /// Terminates the string with a null character (`\0`). The string must not contain a null character.
    ///
    /// This option is recommended if it is possible to guarantee that the string will never contain a null character.
    ///
    /// *Requires 2 bits to store converter*
    NullTerminated,

    /// Writes a string with a specified fixed length. If the string is shorter, it will have
    /// null characters (`\0`) appended until it is the right length.
    ///
    /// This option is only recommended if it is known in advance how long the string will be.
    ///
    /// *Requires 34 bits to store converter*
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

bit_store! {
    for StringConverter {
        (reader) => {
            Ok(
                if !reader.read_bit()? {
                    if !reader.read_bit()? {
                        StringConverter::LengthPrefixed {
                            prefix_bits: 32,
                        }
                    } else {
                        StringConverter::LengthPrefixed {
                            prefix_bits: reader.read_using(&BitMask::bits(5))?,
                        }
                    }
                } else if !reader.read_bit()? {
                    StringConverter::NullTerminated
                } else {
                    StringConverter::FixedLength {
                        length: reader.read::<u32>()?,
                    }
                }
            )
        },
        (self, writer) => {
            match self {
                &StringConverter::LengthPrefixed { prefix_bits: 32 } => {
                    writer.write_bit(false)?;
                    writer.write_bit(false)
                }
                &StringConverter::LengthPrefixed { prefix_bits } => {
                    writer.write_bit(false)?;
                    writer.write_bit(true)?;
                    writer.write_using(&prefix_bits, &BitMask::bits(5))
                },
                &StringConverter::NullTerminated => {
                    writer.write_bit(true)?;
                    writer.write_bit(false)
                },
                &StringConverter::FixedLength { length } => {
                    writer.write_bit(true)?;
                    writer.write_bit(true)?;
                    writer.write(&length)
                }
            }
        },
    };
}

bit_convert! {
    for StringConverter: String {
        (self, reader) => {
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
        },
        (self, value, writer) => {
            if value.len() > u32::max_value() as usize {
                return Err(Error::ConversionFailed);
            }
            match *self {
                StringConverter::LengthPrefixed { prefix_bits } => {
                    let mask = BitMask::bits(prefix_bits);
                    writer.write_using(&(value.len() as u32), &mask)?;
                    for byte in value.as_bytes() {
                        writer.write_byte(*byte)?;
                    }
                    Ok(())
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
                    for byte in value.as_bytes() {
                        writer.write_byte(*byte)?;
                    }
                    for _ in 0..extra {
                        writer.write_byte(0)?;
                    }
                    Ok(())
                },
            }
        },
    };
}

/// A struct that allows the reading and writing of non-bit-length numbers
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

bit_store! {
    for BitMask {
        (reader) => {
            match reader.read_byte() {
                Ok(bits) => Ok(BitMask { bits }),
                Err(e) => Err(e),
            }
        },
        (self, writer) => {
            writer.write_byte(self.bits)
        },
    };
}

macro_rules! impl_bit_mask {
    ($( $u: ident $b: expr ),+) => { $(
        bit_convert! {
            for BitMask: $u {
                (self, reader) => {
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
                    Ok(int)
                },
                (self, value, writer) => {
                    if self.bits != 0 {
                        let int = *value as u64;
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
                },
            };
        }
    )+ }
}

impl_bit_mask!(u64 64, u32 32, u16 16, u8 8);

/// Redirects to [`BitStore`]
///
/// [`BitStore`]: http://docs.rs/bit_manager/0.5.3/bit_manager/data/trait.BitStore.html
pub struct DefaultConverter;

bit_const! {
    const DefaultConverter {
        Ok(DefaultConverter),
        Ok(()),
    };
}

bit_convert! {
    impl<T: BitStore> for DefaultConverter: T {
        (self, reader) => { T::read_from(reader) },
        (self, value, writer) => { value.write_to(writer) },
    };
}