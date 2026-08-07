//! Canonical normal forms, and addressing them through any hasher.
//!
//! [`Canonical`] says that a value has one canonical hash array normal form.
//! Writing that form goes through a [`Sink`], so the same implementation both
//! materializes a [`HashArray`] and, via [`HashSink`], derives an address
//! without ever building one.
//!
//! What "canonical" means is the implementing type's decision, and it is the
//! whole content of the trait:
//!
//! - a sequence writes its elements in order;
//! - a set writes them ascending and distinct, so that independent set
//!   representations of the same elements share an address;
//! - a map writes its entries ascending by key;
//! - an ordered dictionary writes its entries in order, unsorted, because the
//!   order is part of the value.
//!
//! # Verifying an untrusted store
//!
//! This is what the trait is for. A store may serve any representation it
//! likes — a denser one it keeps internally, selected by content type — as
//! long as we can parse it. Parsing yields a value; [`Canonical::matches`]
//! then re-derives the normal form and checks it against the address that was
//! asked for. Nothing about the store's encoding has to be trusted, and the
//! normal form is never materialized to check.

use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    hash::BuildHasher,
};

use covalence_lib_hash::{Cov, Hasher, HasherNamespace, Namespace, Obj};

use crate::{FlatIndexMap, FlatSet, HashArray, Hashes};

/// A destination for the elements of a normal form.
pub trait Sink<N: Namespace = Cov> {
    /// Appends one element.
    fn push(&mut self, value: Obj<N>);

    /// Appends one `(key, value)` entry, as two elements.
    fn push_entry(&mut self, key: Obj<N>, value: Obj<N>) {
        self.push(key);
        self.push(value);
    }
}

impl<N: Namespace> Sink<N> for HashArray<N> {
    fn push(&mut self, value: Obj<N>) {
        HashArray::push(self, value);
    }
}

impl<N: Namespace, S: Sink<N> + ?Sized> Sink<N> for &mut S {
    fn push(&mut self, value: Obj<N>) {
        (**self).push(value);
    }
}

/// A sink that hashes elements instead of storing them.
///
/// Because a normal form is the bare concatenation of its elements, absorbing
/// them one by one produces exactly the address of the serialized array.
pub struct HashSink<H> {
    hasher: H,
}

impl<H: Hasher> HashSink<H> {
    /// Wraps `hasher`.
    pub const fn new(hasher: H) -> Self {
        Self { hasher }
    }

    /// Returns the address of everything absorbed so far.
    pub fn finish(&self) -> Obj<H::Namespace> {
        self.hasher.finish()
    }

    /// Returns the wrapped hasher.
    pub fn into_hasher(self) -> H {
        self.hasher
    }
}

impl<N: Namespace, H: Hasher> Sink<N> for HashSink<H> {
    fn push(&mut self, value: Obj<N>) {
        self.hasher.update(value.as_ref());
    }
}

/// A value with a canonical hash array normal form.
///
/// Implementations must be deterministic: equal values write equal elements,
/// whatever order they are held in internally.
pub trait Canonical<N: Namespace = Cov> {
    /// Writes the normal form's elements, in canonical order.
    fn write_canonical<S: Sink<N> + ?Sized>(&self, sink: &mut S);

    /// Returns the normal form.
    #[must_use]
    fn to_hash_array(&self) -> HashArray<N> {
        let mut array = HashArray::default();
        self.write_canonical(&mut array);
        array
    }

    /// Returns the address of the normal form, in namespace `A`.
    ///
    /// The normal form is not materialized; its elements are absorbed as they
    /// are written.
    #[must_use]
    fn address<A: HasherNamespace>(&self) -> Obj<A> {
        let mut sink = HashSink::new(A::hasher());
        self.write_canonical(&mut sink);
        sink.finish()
    }

    /// Returns whether `address` addresses this value's normal form.
    #[must_use]
    fn matches<A: HasherNamespace>(&self, address: &Obj<A>) -> bool {
        &self.address::<A>() == address
    }

    /// Returns whether `hashes` is this value's normal form.
    #[must_use]
    fn canonical_eq(&self, hashes: Hashes<'_, N>) -> bool {
        self.to_hash_array().as_hashes() == hashes
    }
}

impl<N: Namespace, T: Canonical<N> + ?Sized> Canonical<N> for &T {
    fn write_canonical<S: Sink<N> + ?Sized>(&self, sink: &mut S) {
        (**self).write_canonical(sink);
    }
}

// Sequences: the elements in the order they are held.

impl<N: Namespace> Canonical<N> for Hashes<'_, N> {
    fn write_canonical<S: Sink<N> + ?Sized>(&self, sink: &mut S) {
        for value in self {
            sink.push(value);
        }
    }
}

impl<N: Namespace> Canonical<N> for HashArray<N> {
    fn write_canonical<S: Sink<N> + ?Sized>(&self, sink: &mut S) {
        self.as_hashes().write_canonical(sink);
    }
}

impl<N: Namespace> Canonical<N> for [Obj<N>] {
    fn write_canonical<S: Sink<N> + ?Sized>(&self, sink: &mut S) {
        for value in self {
            sink.push(*value);
        }
    }
}

impl<N: Namespace> Canonical<N> for Vec<Obj<N>> {
    fn write_canonical<S: Sink<N> + ?Sized>(&self, sink: &mut S) {
        self.as_slice().write_canonical(sink);
    }
}

impl<N: Namespace, const K: usize> Canonical<N> for [Obj<N>; K] {
    fn write_canonical<S: Sink<N> + ?Sized>(&self, sink: &mut S) {
        self.as_slice().write_canonical(sink);
    }
}

// Ordered dictionaries: the entries in the order they are held.

impl<N: Namespace> Canonical<N> for FlatIndexMap<'_, N> {
    fn write_canonical<S: Sink<N> + ?Sized>(&self, sink: &mut S) {
        for (key, value) in self {
            sink.push_entry(key, value);
        }
    }
}

impl<N: Namespace> Canonical<N> for [(Obj<N>, Obj<N>)] {
    fn write_canonical<S: Sink<N> + ?Sized>(&self, sink: &mut S) {
        for (key, value) in self {
            sink.push_entry(*key, *value);
        }
    }
}

impl<N: Namespace> Canonical<N> for Vec<(Obj<N>, Obj<N>)> {
    fn write_canonical<S: Sink<N> + ?Sized>(&self, sink: &mut S) {
        self.as_slice().write_canonical(sink);
    }
}

// Sets: ascending and distinct.

impl<N: Namespace> Canonical<N> for FlatSet<'_, N> {
    fn write_canonical<S: Sink<N> + ?Sized>(&self, sink: &mut S) {
        for value in self {
            sink.push(value);
        }
    }
}

impl<N: Namespace> Canonical<N> for BTreeSet<Obj<N>> {
    fn write_canonical<S: Sink<N> + ?Sized>(&self, sink: &mut S) {
        // A `BTreeSet` iterates ascending under the same ordering.
        for value in self {
            sink.push(*value);
        }
    }
}

impl<N: Namespace, B: BuildHasher> Canonical<N> for HashSet<Obj<N>, B> {
    fn write_canonical<S: Sink<N> + ?Sized>(&self, sink: &mut S) {
        let mut values: Vec<_> = self.iter().copied().collect();
        values.sort_unstable();
        values.as_slice().write_canonical(sink);
    }
}

// Maps: ascending by key.

impl<N: Namespace> Canonical<N> for BTreeMap<Obj<N>, Obj<N>> {
    fn write_canonical<S: Sink<N> + ?Sized>(&self, sink: &mut S) {
        // A `BTreeMap` iterates by ascending key under the same ordering.
        for (key, value) in self {
            sink.push_entry(*key, *value);
        }
    }
}

impl<N: Namespace, B: BuildHasher> Canonical<N> for HashMap<Obj<N>, Obj<N>, B> {
    fn write_canonical<S: Sink<N> + ?Sized>(&self, sink: &mut S) {
        let mut entries: Vec<_> = self.iter().map(|(key, value)| (*key, *value)).collect();
        entries.sort_unstable_by_key(|(key, _)| *key);
        entries.as_slice().write_canonical(sink);
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

    use covalence_lib_hash::{Cov, O256};

    use super::Canonical;
    use crate::HashArray;

    fn obj(byte: u8) -> O256 {
        O256::from_array([byte; 32])
    }

    fn array(bytes: &[u8]) -> HashArray {
        bytes.iter().copied().map(obj).collect()
    }

    #[test]
    fn streaming_an_address_agrees_with_hashing_the_normal_form() {
        let values = array(&[1, 2, 3]);
        assert_eq!(
            values.address::<Cov>(),
            O256::from_bytes(values.as_bytes()),
            "the address must be the hash of the serialized normal form"
        );
        assert!(values.matches(&O256::from_bytes(values.as_bytes())));
        assert!(!values.matches(&O256::from_bytes(array(&[1, 2]).as_bytes())));

        let empty = array(&[]);
        assert_eq!(empty.address::<Cov>(), O256::from_bytes([]));
    }

    #[test]
    fn sequences_keep_their_order() {
        let values = vec![obj(3), obj(1), obj(2)];
        assert_eq!(values.to_hash_array(), array(&[3, 1, 2]));
        assert_eq!([obj(3), obj(1)].to_hash_array(), array(&[3, 1]));
        assert_eq!(values.as_slice().address::<Cov>(), values.address::<Cov>());
    }

    #[test]
    fn independent_set_representations_share_an_address() {
        let elements = [obj(5), obj(1), obj(3)];
        let ordered: BTreeSet<O256> = elements.into_iter().collect();
        let unordered: HashSet<O256> = elements.into_iter().collect();
        let canonical = array(&[1, 3, 5]);
        let flat = canonical.as_hashes().flat_set().unwrap();

        let expected = canonical.address::<Cov>();
        assert_eq!(ordered.address::<Cov>(), expected);
        assert_eq!(unordered.address::<Cov>(), expected);
        assert_eq!(flat.address::<Cov>(), expected);
        assert_eq!(ordered.to_hash_array(), canonical);
        assert_eq!(unordered.to_hash_array(), canonical);

        // The unsorted sequence of the same elements is a different value.
        assert_ne!(elements.address::<Cov>(), expected);
    }

    #[test]
    fn independent_map_representations_share_an_address() {
        let entries = [(obj(5), obj(50)), (obj(1), obj(10))];
        let ordered: BTreeMap<O256, O256> = entries.into_iter().collect();
        let unordered: HashMap<O256, O256> = entries.into_iter().collect();
        let canonical = array(&[1, 10, 5, 50]);

        assert_eq!(ordered.to_hash_array(), canonical);
        assert_eq!(unordered.address::<Cov>(), ordered.address::<Cov>());
        assert!(
            canonical
                .as_hashes()
                .flat_index_map()
                .unwrap()
                .is_strictly_sorted_by_key()
        );
    }

    #[test]
    fn ordered_dictionaries_keep_their_order_while_maps_sort() {
        let entries = vec![(obj(5), obj(50)), (obj(1), obj(10))];
        let map: BTreeMap<O256, O256> = entries.iter().copied().collect();

        assert_eq!(entries.to_hash_array(), array(&[5, 50, 1, 10]));
        assert_eq!(map.to_hash_array(), array(&[1, 10, 5, 50]));
        assert_ne!(entries.address::<Cov>(), map.address::<Cov>());

        // The entry sequence reads back as a flat index map, unsorted.
        let dictionary = entries.to_hash_array();
        let dictionary = dictionary.as_hashes().flat_index_map().unwrap();
        assert!(!dictionary.is_sorted_by_key());
        assert_eq!(dictionary.address::<Cov>(), entries.address::<Cov>());
    }

    #[test]
    fn canonical_equality_compares_against_a_borrowed_array() {
        let values = array(&[1, 2]);
        let set: BTreeSet<O256> = [obj(1), obj(2)].into_iter().collect();
        assert!(set.canonical_eq(values.as_hashes()));
        assert!(!set.canonical_eq(array(&[2, 1]).as_hashes()));
    }

    #[test]
    fn references_forward_to_their_referent() {
        let values = array(&[1, 2]);
        let reference = &values;
        assert_eq!(reference.address::<Cov>(), values.address::<Cov>());
    }
}
