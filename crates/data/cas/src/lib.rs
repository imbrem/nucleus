//! Synchronous content-addressed byte sources.
//!
//! [`Cas`] is the trusted interface. Its primitive is *opening* an address,
//! not reading one: [`Cas::open`] resolves an address once and returns a
//! [`CasObject`] which serves ranges thereafter.
//!
//! [`MemoryCas`] is the only implementation here: whole objects, resident in
//! memory, admitted by hashing complete bytes. Reading an *untrusted* source
//! — an HTTP server, a bucket — means verifying every response against the
//! address it was asked for, which is a layer over this one rather than a
//! change to it.
//!
//! # Why opening is the primitive
//!
//! An address-keyed `read` cannot promise anything about an object it is not
//! holding. If the object is dropped from the store between two reads, the
//! second fails — so a database opened over a content-addressed file would
//! start failing mid-query. Handing out an object instead makes the guarantee
//! structural: *while you hold it, it reads*. Removal affects only future
//! opens.
//!
//! This also gives composition somewhere to attach. A copy-on-write layer, an
//! overlay, or a cache is naturally an object built from other objects, and it
//! can hold its bases open for exactly as long as it needs them. That is not
//! expressible when the only operation is "read this address, now".
//!
//! # Why the contract is only open, len, and read
//!
//! Because that is what a directory of files can do. Name each file by its own
//! address and a plain file server implements this interface exactly:
//! `GET /cas/<address>` with ranges, and 404 for an address it does not hold.
//! So does an S3 bucket, and so does static hosting. Nothing about a store
//! that small should need writing.
//!
//! Nothing else belongs in the contract for the same reason. Listing is the
//! obvious candidate and the clearest mistake: a bucket cannot cheaply
//! enumerate, an overlay has no single list to give, and putting it here would
//! mean every implementation either lies or refuses. `MemoryCas::addresses`
//! exists because that store happens to keep a map, and callers must treat it
//! as a property of that store rather than of stores.
//!
//! The direction this points is worth being explicit about: **a more capable
//! store is a front end over a simpler one, not a bigger interface.** A store
//! wanting an index, a manifest, or a packing scheme for ten thousand small
//! objects should keep that state *in* a simple store -- an `SQLite` database
//! is itself one object, at one address -- and serve this same interface over
//! the result. That way the sophisticated thing composes onto the dumb thing,
//! and the dumb thing stays something you can host anywhere.

mod memory;

/// Re-exported because [`CasObject::read`] hands one back: an implementor
/// needs the type and should not have to guess which version of `bytes` we
/// mean.
pub use bytes::Bytes;

pub use memory::{
    AdmissionError, CasStats, InvalidRange, MAX_OBJECT_BYTES, MemoryCas, ResidentObject,
};

use std::ops::Range;

use covalence_lib_hash::O256;

/// A trusted, immutable content-addressed byte source.
///
/// Deliberately no `Send + Sync` bound. Sharing a store across threads is a
/// requirement of the *caller* that needs it -- serving one to a subprocess
/// from another thread, say -- and a store which cannot is still a store.
/// Requiring it here would exclude implementations backed by things that are
/// not themselves thread-safe, `SQLite` connections on wasm among them.
pub trait Cas {
    /// Implementation-specific failure.
    type Error;

    /// An object opened from this source.
    type Object: CasObject<Error = Self::Error>;

    /// Opens `address`, or returns `None` when it does not resolve.
    ///
    /// The returned object stays readable for as long as it is held, whatever
    /// happens to the store afterwards. Resolving an address is therefore a
    /// one-time act, and implementations may do their length lookup,
    /// authentication, or handle acquisition here rather than per read.
    ///
    /// `None` is an unauthenticated, fail-closed absence signal. It means this
    /// source did not produce the object, not that no such object exists.
    ///
    /// # Errors
    ///
    /// Returns an error when the source fails to answer at all, as distinct
    /// from answering that the address does not resolve.
    fn open(&self, address: O256) -> Result<Option<Self::Object>, Self::Error>;

    /// Returns the length of `address`, or `None` when it does not resolve.
    ///
    /// # Errors
    ///
    /// Returns an error when the source cannot determine the length.
    fn len(&self, address: O256) -> Result<Option<u64>, Self::Error> {
        Ok(self.open(address)?.map(|object| object.len()))
    }

    /// Returns exactly `range` from `address`, or `None` when it does not
    /// resolve.
    ///
    /// This is a convenience for a single read. A caller making several reads
    /// of one address should [`open`](Self::open) it instead, both to resolve
    /// once and to hold the object still.
    ///
    /// # Errors
    ///
    /// Returns an error when the range cannot be served or authenticated.
    fn read(&self, address: O256, range: Range<u64>) -> Result<Option<Bytes>, Self::Error> {
        self.open(address)?
            .map(|object| object.read(range))
            .transpose()
    }
}

/// An object opened from a [`Cas`].
///
/// Holding one keeps its bytes readable. An implementation must not depend on
/// the address still resolving in the store it came from.
pub trait CasObject {
    /// Implementation-specific failure.
    type Error;

    /// Returns the object's total length in bytes.
    ///
    /// This is fixed for the object's lifetime: content-addressed objects are
    /// immutable, so length cannot change under a holder.
    fn len(&self) -> u64;

    /// Returns whether the object is empty.
    ///
    /// An empty object is a legitimate object, distinct from an address which
    /// does not resolve.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns exactly `range`.
    ///
    /// Implementations must reject a reversed range or one extending past
    /// [`len`](Self::len) rather than truncating it. A short read is an error,
    /// not a silent partial answer.
    ///
    /// # Errors
    ///
    /// Returns an error when the range is invalid, cannot be served, or cannot
    /// be authenticated.
    fn read(&self, range: Range<u64>) -> Result<Bytes, Self::Error>;
}
