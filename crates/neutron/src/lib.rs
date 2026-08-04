//! Thin mechanical wrappers over `SQLite`.
//!
//! Neutron deliberately remains permeable and assigns no interpretation to a
//! database. Nucleus provides protocol-enforcing enclosures above this crate.

#![deny(unsafe_code)]

mod connection;
mod image;
mod vfs;

pub use bytes::Bytes;
pub use connection::{Connection, ConnectionError};
pub use image::ImageError;
pub use vfs::DatabaseVfsError;
