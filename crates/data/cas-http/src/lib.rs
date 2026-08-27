//! Bounded, read-only CAS access over HTTP.

mod client;
mod server;

pub use client::{HttpCas, HttpCasError};
pub use server::{Serving, serve};

/// Path prefix under which objects are served.
pub const OBJECT_PREFIX: &str = "/cas/";

/// Largest response this server will produce, whole or ranged.
pub const MAX_RESPONSE_BYTES: u64 = 8 << 20;
