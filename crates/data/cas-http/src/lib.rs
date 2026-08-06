//! The CAS over HTTP.
//!
//! A ranged `GET` is the CAS read operation, so serving the store this way
//! costs almost nothing and buys a client every ranged-read tool that already
//! exists: `fetch`, S3, CDNs, caches, `curl`. It is also what lets a browser
//! reach a kernel without a bespoke bridge.
//!
//! The HTTP protocol itself is `tiny_http`'s and range parsing is
//! `http-range-header`'s — the crate `tower-http` uses. Hand-rolling either is
//! a good way to ship a subtly wrong server, and neither is where this project
//! has anything to contribute. What is written here is the routing, the
//! content-address lookup, and the bounds.
//!
//! # This is a read capability, and an unauthenticated one
//!
//! Anything that can reach the port can read every object the store holds.
//! There is no admission here — `MemoryCas::insert` stays local — but
//! "read-only" is not "harmless". Bind to loopback unless you have decided
//! otherwise, and treat an object's address as the secret it is.
//!
//! # What the client must check
//!
//! Nothing here is trusted, and a client that believes this server without
//! checking has learned nothing from content addressing: the bytes for an
//! address must hash to that address. [`covalence_data_cas::Verified`] is the
//! shape that turns an untrusted source into a `Cas`; issue #442 covers range
//! proofs, which are what make *partial* reads verifiable without fetching the
//! whole object.
//!
//! Until those exist, a paranoid client fetches whole objects and hashes them.
//! That is correct, and it is what the browser demo does.

mod server;

pub use server::{Serving, serve};

/// Path prefix under which objects are served.
pub const OBJECT_PREFIX: &str = "/cas/";

/// Largest response this server will produce, whole or ranged.
pub const MAX_RESPONSE_BYTES: u64 = 8 << 20;
