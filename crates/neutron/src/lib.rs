//! Uninterpreted relational machinery over `SQLite`.
//!
//! [`Connection`] is a deliberately permeable mechanical wrapper around
//! [`covalence_lib_sqlite::Connection`]. Nucleus provides conventions and
//! policy above it.

#![deny(unsafe_code)]

mod connection;
mod image;

pub use bytes::Bytes;
pub use connection::{Connection, ConnectionError};
pub use image::ImageError;
