//! Flat hash arrays in content-addressed normal form.
//!
//! A hash array is a sequence of fixed-width objects serialized as the
//! concatenation of their representations, and nothing else: no header, no
//! length prefix, no element count. A blob is a hash array exactly when its
//! length is a multiple of the element width, which makes it the smallest
//! useful thing a content-addressed store can hold, and the foundation the
//! other Merkle structures are built on.
//!
//! # Normal form, not efficiency
//!
//! These structures are deliberately not optimized. Their purpose is to give
//! every value exactly one canonical byte serialization. A store which
//! understands arrays may hold an indexed representation internally and serve
//! the same bytes on request. Such an optimization never has to be trusted:
//! serializing it back to normal form, hashing, and comparing is cheap.
//!
//! # Addressing
//!
//! This crate defines normal form only; it computes no hashes and depends on
//! no hash algorithm. An array's address is the store's hash of
//! [`Hashes::as_bytes`], taken by whichever layer owns that decision.
//!
//! ```
//! use covalence_data_array::{HashArray, Hashes};
//! use covalence_lib_hash::O256;
//!
//! // Build an array. Order and duplicates are preserved.
//! let array: HashArray = [3, 1, 3, 2]
//!     .map(|byte| O256::from_array([byte; 32]))
//!     .into_iter()
//!     .collect();
//!
//! // Read the same bytes back without a decoding allocation.
//! let hashes = Hashes::from_bytes(array.as_bytes())?;
//! assert_eq!(hashes.len(), 4);
//! assert_eq!(hashes.get(1), Some(O256::from_array([1; 32])));
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

#![deny(unsafe_code)]

mod seq;

pub use seq::{HashArray, HashArrayRef, Hashes, OwnedHashArray, WIDTH, WidthError};
