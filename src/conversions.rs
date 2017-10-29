//! Provides converters for reading and writing values using stucts

use super::*;
use std::io;
use std::mem;

/// A trait for reading values using a converter
pub trait BitRead<T>: Sized {
    /// Read a value from the given reader
    fn read_value_from<R: io::Read>(&self, reader: &mut BitReader<R>) -> Result<T>;
}

/// A trait for writing values using a converter
pub trait BitWrite<T>: Sized {
    /// Write a value to the given writer
    fn write_value_to<W: io::Write>(&self, value: T, writer: &mut BitWriter<W>) -> Result<()>;
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
    fn read_from<R: io::Read>(reader: &mut BitReader<R>) -> Result<BitMask> {
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
                    return Err(Error::ConversionFailed);
                } else if self.bits == 0 {
                    return Ok(0);
                }
                let mut int = 0;
                for index in 0..self.bits {
                    let read = reader.read_bit()?;
                    if read {
                        int |= 1 << (self.bits-index-1);
                    }
                }
                Ok($u::from_le(int))
            }
        }

        impl BitRead<$i> for BitMask {
            fn read_value_from<R: io::Read>(&self, reader: &mut BitReader<R>) -> Result<$i> {
                unsafe { Ok(mem::transmute::<$u, $i>(self.read_value_from(reader)?)) }
            }
        }

        impl BitWrite<$u> for BitMask {
            fn write_value_to<W: io::Write>(&self, value: $u, writer: &mut BitWriter<W>) -> Result<()> {
                if self.bits != 0 {
                    let int = u64::to_le(value as u64);
                    if self.bits < 64 && int >> self.bits != 0 {
                        return Err(Error::ConversionFailed);
                    }
                    for index in 0..self.bits {
                        writer.write_bit((int >> (self.bits - index - 1)) & 1 == 1)?;
                    }
                }
                Ok(())
            }
        }

        impl BitWrite<$i> for BitMask {
            fn write_value_to<W: io::Write>(&self, value: $i, writer: &mut BitWriter<W>) -> Result<()> {
                unsafe { self.write_value_to(mem::transmute::<$i, $u>(value), writer) }
            }
        }
    )+ }
}

impl_bit_mask!(u64 i64 64, u32 i32 32, u16 i16 16, u8 i8 8);

///// A trait for a struct that can be converted to a `Vec` of bits
//pub trait ToBits: Sized {
//    /// Returns this as a series of bits.
//    fn to_bits(&self) -> Vec<bool>;
//}
//
///// A trait for a struct that can be converted to a `Vec` of bytes
//pub trait ToBytes: Sized {
//    fn to_bytes(&self) -> Vec<u8>;
//}
//
//impl<T: ToBytes> ToBits for T {
//    fn to_bits(&self) -> Vec<bool> {
//        let bytes = self.to_bytes();
//        let mut bits = Vec::with_capacity(bytes.len()*8);
//        for byte in bytes {
//            for index in 0..8 {
//                bits.push((byte >> 7-index) & 1 == 1);
//            }
//        }
//        bits
//    }
//}