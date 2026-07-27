//! Uninterpreted relational machinery over `SQLite`.
//!
//! [`Connection`] augments a [`covalence_lib_sqlite::Connection`] with
//! connection-local metadata. It deliberately remains permeable: callers can
//! access the underlying `SQLite` connection and are responsible for any
//! semantic invariants they require. Nucleus provides the policy-enforcing
//! layer above this crate.

#![deny(unsafe_code)]

mod addition;
mod cas;
mod connection;
mod image;
mod trust;

pub use addition::{AdditionError, AdditionFact, AdditionLayout, AdditionTable};
pub use bytes::Bytes;
pub use cas::{Cas, CasError, CasId};
pub use connection::{
    ATTACHED_DATABASES, ATTACHED_DATABASES_INTERPRETATION, CONNECTION_CATALOG,
    CONNECTION_CATALOG_INTERPRETATION, Connection, ConnectionError, DEFAULT_CAS,
    DEFAULT_CAS_INTERPRETATION, SIGNING_KEYS, SIGNING_KEYS_INTERPRETATION, TRUSTED_KEYS,
    TRUSTED_KEYS_INTERPRETATION, TRUSTED_SNAPSHOTS, TRUSTED_SNAPSHOTS_INTERPRETATION,
};
pub use covalence_lib_hash::O256;
pub use image::ImageError;
pub use trust::TrustMetadataError;
