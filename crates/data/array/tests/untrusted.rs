//! The untrusted-representation round trip.
//!
//! A store is asked for an array by address, and answers in whichever
//! representation was negotiated — here a dense run-length encoding it keeps
//! internally, rather than the normal form. The answer is parsed into a value,
//! and the value re-derives the normal form's address through [`Canonical`].
//! Nothing the store said has to be trusted, and the array it stands for is
//! never materialized to check it.

use covalence_data_array::{Canonical, HashArray, Sink};
use covalence_lib_hash::{Blake3, Cov, Namespace, O256, Obj};

/// A run of one repeated object.
type Run = (O256, u64);

/// A dense encoding of an array as runs of repeated objects.
///
/// This is the kind of representation a store is free to keep internally: for
/// the constant and repeating ranges that motivate O256-keyed maps, it is
/// arbitrarily smaller than the normal form.
struct Runs(Vec<Run>);

/// The width of one encoded run: an object and a little-endian count.
const RUN: usize = Cov::BYTES + 8;

impl Runs {
    /// Encodes the runs, as an untrusted store would serve them.
    fn encode(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(self.0.len() * RUN);
        for (value, count) in &self.0 {
            bytes.extend_from_slice(value.as_ref());
            bytes.extend_from_slice(&count.to_le_bytes());
        }
        bytes
    }

    /// Parses a served encoding, rejecting anything malformed.
    fn parse(bytes: &[u8]) -> Option<Self> {
        if !bytes.len().is_multiple_of(RUN) {
            return None;
        }
        let mut runs = Vec::new();
        for chunk in bytes.chunks_exact(RUN) {
            let (value, count) = chunk.split_at(Cov::BYTES);
            runs.push((
                O256::from_array(value.try_into().ok()?),
                u64::from_le_bytes(count.try_into().ok()?),
            ));
        }
        Some(Self(runs))
    }
}

impl Canonical for Runs {
    fn write_canonical<S: Sink + ?Sized>(&self, sink: &mut S) {
        for (value, count) in &self.0 {
            for _ in 0..*count {
                sink.push(*value);
            }
        }
    }
}

fn obj(byte: u8) -> O256 {
    O256::from_array([byte; 32])
}

/// The array the store is asked for: 1000 elements in two runs.
fn subject() -> HashArray {
    let mut array = HashArray::with_capacity(1000);
    array.extend(std::iter::repeat_n(obj(1), 600));
    array.extend(std::iter::repeat_n(obj(2), 400));
    array
}

#[test]
fn a_dense_representation_is_verified_against_the_address_it_was_asked_for() {
    let array = subject();
    let address = array.address::<Cov>();

    // The store answers with runs rather than the normal form.
    let served = Runs(vec![(obj(1), 600), (obj(2), 400)]).encode();
    assert_eq!(served.len(), 2 * RUN);
    assert_eq!(array.as_bytes().len(), 32_000);

    // We parse what we were given, and check it ourselves.
    let parsed = Runs::parse(&served).expect("well-formed encoding");
    assert!(
        parsed.matches(&address),
        "the parsed representation must re-derive the address it was asked for"
    );

    // It does stand for exactly the array, though checking never built one.
    assert_eq!(parsed.to_hash_array(), array);
    assert!(parsed.canonical_eq(array.as_hashes()));
}

#[test]
fn a_tampered_representation_fails_to_match() {
    let address = subject().address::<Cov>();

    for tampered in [
        // A changed value.
        Runs(vec![(obj(1), 600), (obj(3), 400)]),
        // A changed count, keeping the total.
        Runs(vec![(obj(1), 599), (obj(2), 401)]),
        // A truncated array.
        Runs(vec![(obj(1), 600), (obj(2), 399)]),
        // The right elements in the wrong order.
        Runs(vec![(obj(2), 400), (obj(1), 600)]),
        // Nothing at all.
        Runs(Vec::new()),
    ] {
        assert!(
            !tampered.matches(&address),
            "a representation that is not the array must not match its address"
        );
    }
}

#[test]
fn a_malformed_encoding_is_rejected_before_it_is_trusted() {
    assert!(Runs::parse(&[0; RUN - 1]).is_none());
    assert!(Runs::parse(&[0; RUN + 1]).is_none());
    assert!(Runs::parse(&[]).is_some());
}

#[test]
fn the_address_does_not_depend_on_the_representation_that_produced_it() {
    let array = subject();

    // Runs, the owned array, and a borrowed view all address identically.
    let runs = Runs(vec![(obj(1), 600), (obj(2), 400)]);
    assert_eq!(runs.address::<Cov>(), array.address::<Cov>());
    assert_eq!(array.as_hashes().address::<Cov>(), array.address::<Cov>());

    // And that address is the hash of the serialized normal form.
    assert_eq!(array.address::<Cov>(), O256::from_bytes(array.as_bytes()));
}

#[test]
fn addressing_is_polymorphic_over_the_hasher() {
    let array = subject();

    // The same value addresses in whichever namespace is asked for.
    let covalence: O256 = array.address::<Cov>();
    let blake3: Obj<Blake3> = array.address::<Blake3>();
    assert_eq!(blake3.into_o256(), covalence);
}

/// The addressing namespace is genuinely a parameter, not BLAKE3 in disguise.
#[cfg(feature = "sha256")]
#[test]
fn addressing_works_under_an_unrelated_algorithm() {
    use covalence_lib_hash::{HashNamespace, Sha256};

    let array = subject();
    let sha256: Obj<Sha256> = array.address::<Sha256>();

    assert_eq!(sha256, Sha256::hash(array.as_bytes()));
    assert_ne!(sha256.as_ref(), array.address::<Cov>().as_ref());
}
