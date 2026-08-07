//! Incremental hashing.
//!
//! [`HashNamespace`](crate::HashNamespace) hashes bytes a caller already holds.
//! A [`Hasher`] instead absorbs them in order, which lets an object be derived
//! from a structure that is never materialized — the serialized form of a
//! large collection, say, or a stream too big to keep.
//!
//! The two agree: absorbing a byte sequence in any number of steps produces
//! the object that hashing it whole would.

use crate::{Namespace, Obj};

/// An incremental hasher producing objects in one namespace.
pub trait Hasher {
    /// The namespace of the produced object.
    type Namespace: Namespace;

    /// Absorbs `bytes`.
    fn update(&mut self, bytes: &[u8]);

    /// Produces the object of everything absorbed so far.
    ///
    /// This does not end the stream; absorbing may continue afterwards.
    fn finish(&self) -> Obj<Self::Namespace>;
}

/// A namespace whose objects can be produced incrementally.
pub trait HasherNamespace: Namespace + Sized {
    /// This namespace's incremental hasher.
    type Hasher: Hasher<Namespace = Self>;

    /// Creates a hasher that has absorbed nothing.
    fn hasher() -> Self::Hasher;
}

impl<H: Hasher + ?Sized> Hasher for &mut H {
    type Namespace = H::Namespace;

    fn update(&mut self, bytes: &[u8]) {
        (**self).update(bytes);
    }

    fn finish(&self) -> Obj<Self::Namespace> {
        (**self).finish()
    }
}
