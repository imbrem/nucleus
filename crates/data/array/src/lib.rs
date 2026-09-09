//! Opaque word array tables and flat O256 hash sequences.
//!
//! [`table`] supplies reusable length-delimited arrays with a generic header
//! codec, copy-on-write, and intrusive free rings. [`HashSeq`] is the separate
//! Iroh-compatible wire sequence described below.
//!
//! Elements are concatenated without a header. Order and duplicates matter.
//! This crate defines representation, not addressing.
//!
//! ```
//! use covalence_data_array::HashSeq;
//! use covalence_lib_hash::O256;
//!
//! let array: HashSeq = [3, 1, 3, 2]
//!     .map(|byte| O256::from_array([byte; 32]))
//!     .into_iter()
//!     .collect();
//!
//! let hashes = HashSeq::<&[O256]>::from_bytes(array.as_bytes())?;
//! assert_eq!(hashes.len(), 4);
//! assert_eq!(hashes.get(1), Some(O256::from_array([1; 32])));
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

#![deny(unsafe_code)]

mod seq;
pub mod table;

pub use seq::{HashSeq, HashSeqRef, WIDTH, WidthError};
