//! Contains aliases for the most commonly used types.
//!
//! ```
//! # #[allow(unused_imports)]
//! use bit_manager::prelude::*;
//! ```

#[doc(inline)]
pub use io::*;
#[doc(inline)]
pub use data::{BitMask, StringConverter};
#[doc(inline)]
pub use buffer::Precision;

#[doc(no_inline)]
pub use std::io::{Read, Write};