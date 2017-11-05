//! A crate for reading and writing bits from various streams
//!
//! *This crate is unstable. Features may be added or removed without warning. Expect breaking changes.*
//!
//! # Reading
//! ```
//! # extern crate bit_manager; fn main() { test().unwrap(); } fn test() -> bit_manager::Result<()> {
//! use bit_manager::{BitReader, BitRead};
//!
//! let mut reader = BitReader::new([0b01101110u8, 0b10100000u8].as_ref());
//!
//! assert_eq!(reader.read_bit()?, false);
//! assert_eq!(reader.read_bit()?, true);
//! assert_eq!(reader.read_bit()?, true);
//! assert_eq!(reader.read_byte()?, 0b01110101);
//! # Ok(()) }
//! ```
//!
//! # Writing
//! ```
//! # extern crate bit_manager; fn main() { test().unwrap(); } fn test() -> bit_manager::Result<()> {
//! use bit_manager::{BitWriter, BitWrite};
//!
//! let mut writer = BitWriter::new(Vec::new());
//!
//! writer.write_bit(false)?;
//! writer.write_bit(true)?;
//! writer.write_bit(true)?;
//! writer.write_byte(0b01110101)?;
//!
//! assert_eq!(writer.into_inner()?, [0b01101110u8, 0b10100000u8]);
//! # Ok(()) }
//! ```
#![deny(missing_docs)]

#[doc(inline)]
pub use io::*;
#[doc(inline)]
pub use buffer::{Result, Error, Precision};

use data::*;
use std::{mem, result};

macro_rules! bit_store {
    { $( $(impl<$($t: ident $(: $b: ident $(+ $x: ident)*)*),+>)* for $ty: ty {
        ( $r: ident ) => $read: block,
        ( $self: ident, $w: ident ) => $write: block,
    }; )+ } => { $(
        impl$(<$($t $(: $b $(+ $x)*)*, )+>)* $crate::data::BitStore for $ty {
            fn read_from<R: $crate::io::BitRead>($r: &mut R) -> $crate::buffer::Result<Self> $read
            fn write_to<W: $crate::io::BitWrite>(&$self, $w: &mut W) -> $crate::buffer::Result<()> $write
        }
    )+ };
}

macro_rules! bit_const {
    { $(impl<$($t: ident $(: $b: ident $(+ $x: ident)*)*),+>)* const $ty: ty {
        $read: expr,
        $write: expr,
    }; } => {
        impl$(<$($t $(: $b $(+ $x)*)*, )+>)* $crate::data::BitStore for $ty {
            fn read_from<R: $crate::io::BitRead>(_: &mut R) -> $crate::buffer::Result<Self> { $read }
            fn write_to<W: $crate::io::BitWrite>(&self, _: &mut W) -> $crate::buffer::Result<()> { $write }
        }
    };
}

macro_rules! bit_convert {
    { $( $(impl<$($t: ident $(: $b: ident $(+ $x: ident)*)*),+>)* for $ty: ty: $return: ty {
        ( $self_r: ident, $r: ident ) => $read: block,
        ( $self_w: ident, $v: ident, $w: ident ) => $write: block,
    }; )+ } => { $(
        impl$(<$($t $(: $b $(+ $x)*)*, )+>)* $crate::data::BitConvert<$return> for $ty {
            fn read_value_from<R: $crate::io::BitRead>(&$self_r, $r: &mut R) -> $crate::buffer::Result<$return> $read
            fn write_value_to<W: $crate::io::BitWrite>(&$self_w, $v: &$return, $w: &mut W) -> $crate::buffer::Result<()> $write
        }
    )+ };
}

pub mod prelude;
pub mod buffer;
pub mod data;
pub mod io;

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

macro_rules! int_impl {
    ($( $s: expr => $( $v: ident ),+  );+) => { $( $( bit_store! { for $v {
        (reader) => { Ok(Self::from_be( unsafe { mem::transmute::<[u8; $s], Self>(reader.read()?) } )) },
        (self, writer) => { writer.write( & unsafe { mem::transmute::<Self, [u8; $s]>((*self).to_be()) } ) },
    }; } )+ )+ }
}

int_impl!(2 => u16, i16; 4 => u32, i32; 8 => u64, i64);

macro_rules! float_impl {
    ($( $s: expr => $u: ident => $v: ident  );+) => { $( bit_store! { for $v {
        (reader) => { Ok( unsafe { mem::transmute($u::from_be(mem::transmute::<[u8; $s], $u>(reader.read()?))) } ) },
        (self, writer) => { writer.write( & unsafe { mem::transmute::<$u, [u8; $s]>(mem::transmute::<Self, $u>(*self).to_be()) } ) },
    }; } )+ }
}

float_impl!(4 => u32 => f32; 8 => u64 => f64);

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

macro_rules! array_impl {
    ($x: expr; $a: ident $( $b: ident )*) => {
        array_impl! { $x - 1; $( $b )* }
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
        bit_const! {
            impl<T> const [T; $x] {
                Ok([]),
                Ok(()),
            };
        }
    };
}

array_impl! { 32; read read read read read read read read read read read read read read read read read read read read read read read read read read read read read read read read }

macro_rules! tuple_impl {
    ($a: ident $( $b: ident )+) => {
        #[allow(non_snake_case)]
        impl<$a $(, $b )*> BitStore for ( $a $(, $b )* ) where $a: BitStore $(, $b: BitStore )* {
            fn read_from<READ: BitRead>(reader: &mut READ) -> buffer::Result<Self> { Ok((reader.read()? $(, reader.read::<$b>()?)*)) }
            fn write_to<WRITE: BitWrite>(&self, writer: &mut WRITE) -> buffer::Result<()> {
                let &( ref $a, $(ref $b, )* ) = self;
                writer.write($a)
                $(
                    ?; writer.write($b)
                )*
            }
        }
    };
}

bit_const! {
    const () {
        Ok(()),
        Ok(()),
    };
}

// Unit     { }
// Expr     { A }
tuple_impl! { A B }
tuple_impl! { A B C }
tuple_impl! { A B C D }
tuple_impl! { A B C D E }
tuple_impl! { A B C D E F }
tuple_impl! { A B C D E F G }
tuple_impl! { A B C D E F G H }
tuple_impl! { A B C D E F G H I }
tuple_impl! { A B C D E F G H I J }
tuple_impl! { A B C D E F G H I J K }
tuple_impl! { A B C D E F G H I J K L }
tuple_impl! { A B C D E F G H I J K L M }
tuple_impl! { A B C D E F G H I J K L M N }
tuple_impl! { A B C D E F G H I J K L M N O }
tuple_impl! { A B C D E F G H I J K L M N O P }
tuple_impl! { A B C D E F G H I J K L M N O P Q }
tuple_impl! { A B C D E F G H I J K L M N O P Q R }
tuple_impl! { A B C D E F G H I J K L M N O P Q R S }
tuple_impl! { A B C D E F G H I J K L M N O P Q R S T }
tuple_impl! { A B C D E F G H I J K L M N O P Q R S T U }
tuple_impl! { A B C D E F G H I J K L M N O P Q R S T U V }
tuple_impl! { A B C D E F G H I J K L M N O P Q R S T U V W }
tuple_impl! { A B C D E F G H I J K L M N O P Q R S T U V W X }
tuple_impl! { A B C D E F G H I J K L M N O P Q R S T U V W X Y }
tuple_impl! { A B C D E F G H I J K L M N O P Q R S T U V W X Y Z }



















