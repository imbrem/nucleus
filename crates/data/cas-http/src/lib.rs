//! Bounded HTTP transport for a composable CAS service.

mod client;
mod server;

pub use client::{HttpCas, HttpCasError};
pub use server::{Serving, serve};

/// Compatibility path prefix for BLAKE3-addressed objects.
pub const OBJECT_PREFIX: &str = "/cas/";

/// Canonical path prefix for BLAKE3-addressed objects.
pub const BLAKE3_PREFIX: &str = "/cas/blake3/";

/// Path accepting bodies whose BLAKE3 address is computed by the service.
pub const UPLOAD_PATH: &str = "/cas/upload";

/// Largest response this server will produce, whole or ranged.
pub const MAX_RESPONSE_BYTES: u64 = 8 << 20;

/// Largest request body this transport accepts for admission.
pub const MAX_UPLOAD_BYTES: usize = 64 << 20;

/// Shortest hexadecimal address prefix accepted for lookup.
pub const MIN_HASH_PREFIX_HEX: usize = 8;
