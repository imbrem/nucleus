//! Bounded, read-only CAS access over ranged HTTP.

mod server;

pub use server::{Serving, serve};

/// Path prefix under which objects are served.
pub const OBJECT_PREFIX: &str = "/cas/";

/// Largest response this server will produce, whole or ranged.
pub const MAX_RESPONSE_BYTES: u64 = 8 << 20;
