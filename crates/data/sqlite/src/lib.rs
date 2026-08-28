//! Untrusted relational data helpers over `SQLite`.
//!
//! [`Connection`] augments a [`covalence_lib_sqlite::Connection`] with
//! connection-local metadata. It deliberately remains permeable: callers can
//! access the underlying `SQLite` connection and are responsible for any
//! semantic invariants they require. This is userspace infrastructure: it has
//! no theorem, signing, or Nucleus state authority.

#![deny(unsafe_code)]

mod cas_vfs;
mod connection;
mod image;
mod resource_vfs;
pub mod sql;

pub use bytes::Bytes;
pub use cas_vfs::{CAS_VFS_NAME, CasFile, CasVfs, register_cas};
pub use connection::{
    ATTACHED_DATABASES, ATTACHED_DATABASES_INTERPRETATION, CONNECTION_CATALOG,
    CONNECTION_CATALOG_INTERPRETATION, Connection, ConnectionError,
};
pub use covalence_lib_sqlite::vfs::ReadOnlyVfs;
pub use image::ImageError;
pub use resource_vfs::ResourceVfs;
