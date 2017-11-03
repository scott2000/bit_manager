//! The bit manager prelude
//!
//! ```
//! # #[allow(unused_imports)]
//! use bit_manager::prelude::*;
//! ```

pub use std::io::{Read, Write};
pub use {BitRead, BitWrite, BitReader, BitWriter};
pub use conversions::BitMask;