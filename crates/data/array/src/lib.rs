//! Flat hash arrays, and the sets and maps read directly out of them.
//!
//! A hash array is a sequence of fixed-width objects serialized as the
//! concatenation of their representations, and nothing else: no header, no
//! length prefix, no element count. A blob is a hash array exactly when its
//! length is a multiple of the element width, which makes it the smallest
//! useful thing a content-addressed store can hold, and the foundation the
//! other Merkle structures are built on.
//!
//! [`FlatSet`] and [`FlatIndexMap`] add invariants to that same normal form —
//! strictly ascending elements, and an even element count read as
//! `(key, value)` entries — rather than a representation of their own. One
//! blob is therefore readable as all three without re-encoding, and each
//! reading is checkable in a linear scan.
//!
//! # Normal form, not efficiency
//!
//! These structures are deliberately not optimized. Their purpose is to give
//! every value exactly one canonical byte serialization, so that a store which
//! understands arrays, sets, and maps is free to hold a denser representation
//! internally and to serve it on request. Such a representation never has to
//! be trusted: serializing it back to normal form, hashing, and comparing is
//! cheap. Truncating objects to `u64` or `u32` where a structure permits it is
//! the obvious such optimization, and zero-padding reverses it.
//!
//! Object ordering is bytewise, so sortedness of the elements and
//! lexicographic ordering of the normal form are the same property. Sorting,
//! merging, and comparison can be performed on either side of the
//! serialization boundary and agree.
//!
//! # Addressing
//!
//! [`Canonical`] gives a value one normal form, and with it one address. It is
//! generic over the hasher, so this crate names no algorithm: `address::<A>()`
//! works in whichever namespace the caller asks for. Because a normal form is
//! a bare concatenation, the elements are absorbed as they are written and the
//! array itself is never built.
//!
//! That is what makes an untrusted store usable. Ask it for an array by
//! address; let it answer in whatever representation it keeps, however dense;
//! parse that into a value; then check the value re-derives the address that
//! was asked for. See the `untrusted` integration test for the round trip.
//!
//! ```
//! use std::collections::BTreeSet;
//!
//! use covalence_data_array::{Canonical, HashArray, Hashes};
//! use covalence_lib_hash::{Cov, O256};
//!
//! // Build an array, then put it in canonical set form.
//! let mut array: HashArray = [3, 1, 3, 2]
//!     .map(|byte| O256::from_array([byte; 32]))
//!     .into_iter()
//!     .collect();
//! array.sort_dedup();
//!
//! // Read the same bytes back as an array, and as a set.
//! let hashes = Hashes::<_>::new(array.as_bytes())?;
//! assert_eq!(hashes.len(), 3);
//!
//! let set = hashes.flat_set()?;
//! assert!(set.contains(&O256::from_array([2; 32])));
//! assert!(!set.contains(&O256::from_array([9; 32])));
//!
//! // Any representation of those elements addresses identically.
//! let elsewhere: BTreeSet<O256> = [1, 2, 3].map(|b| O256::from_array([b; 32])).into();
//! assert_eq!(elsewhere.address::<Cov>(), array.address::<Cov>());
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

#![deny(unsafe_code)]

mod canonical;
mod map;
mod seq;
mod set;

pub use canonical::{Canonical, HashSink, Sink};
pub use map::{Entries, FlatIndexMap, ParityError};
pub use seq::{HashArray, Hashes, Iter, WidthError, width};
pub use set::{FlatSet, OrderError};
