//! Retryable CAS-backed arena-link resolution.

use std::{collections::BTreeMap, sync::Arc, sync::RwLock};

use covalence_data_cas::{Cas, CasObject};
use covalence_lib_hash::O256;

use crate::{Arena, Link, Resolver, TrustedResolver, resolve::trusted_resolver, wire};

/// A CAS or arena-decoding failure.
#[derive(Debug)]
pub enum Error<E> {
    Cas(E),
    WrongAddress { expected: O256, actual: O256 },
    Decode(wire::DecodeError),
}

impl<E: std::fmt::Display> std::fmt::Display for Error<E> {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Cas(error) => write!(output, "CAS lookup failed: {error}"),
            Self::WrongAddress { expected, actual } => write!(
                output,
                "CAS returned content with address {actual:?} for {expected:?}"
            ),
            Self::Decode(error) => write!(output, "linked arena failed to decode: {error}"),
        }
    }
}

impl<E: std::error::Error + 'static> std::error::Error for Error<E> {}

/// A resolver over immutable content-addressed bytes.
///
/// Only successful decodes are cached. Absence and decoding errors remain
/// retryable, and cache contents do not participate in link serialization.
pub struct CasResolver<C> {
    cas: C,
    cache: RwLock<BTreeMap<O256, Arc<Arena>>>,
}

impl<C> CasResolver<C> {
    #[must_use]
    pub const fn new(cas: C) -> Self {
        Self {
            cas,
            cache: RwLock::new(BTreeMap::new()),
        }
    }

    #[must_use]
    pub const fn cas(&self) -> &C {
        &self.cas
    }

    #[must_use]
    pub fn cached(&self, address: O256) -> Option<Arc<Arena>> {
        self.cache
            .read()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .get(&address)
            .cloned()
    }
}

impl<C: Cas> Resolver for CasResolver<C> {
    type Error = Error<C::Error>;

    fn resolve(&self, link: &Link) -> Result<Option<Arc<Arena>>, Self::Error> {
        let address = link.blake3;
        if let Some(arena) = self.cached(address) {
            return Ok(Some(arena));
        }
        let Some(object) = self.cas.open(address).map_err(Error::Cas)? else {
            return Ok(None);
        };
        let bytes = object.read(0..object.len()).map_err(Error::Cas)?;
        let actual = O256::from_bytes(bytes.as_ref());
        if actual != address {
            return Err(Error::WrongAddress {
                expected: address,
                actual,
            });
        }
        let arena = Arc::new(wire::deserialize(bytes.as_ref()).map_err(Error::Decode)?);
        let mut cache = self
            .cache
            .write()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        Ok(Some(Arc::clone(cache.entry(address).or_insert(arena))))
    }
}

impl<C: Cas> trusted_resolver::Sealed for CasResolver<C> {}
impl<C: Cas> TrustedResolver for CasResolver<C> {}

#[cfg(test)]
mod tests {
    use std::{convert::Infallible, ops::Range};

    use covalence_data_cas::MemoryCas;
    use covalence_data_cas::{Bytes, CasObject};

    use super::*;
    use crate::{LinkFormat, Resolver};

    struct LyingObject(Bytes);

    impl CasObject for LyingObject {
        type Error = Infallible;

        fn len(&self) -> u64 {
            self.0.len() as u64
        }

        fn read(&self, range: Range<u64>) -> Result<Bytes, Self::Error> {
            let start = usize::try_from(range.start).unwrap();
            let end = usize::try_from(range.end).unwrap();
            Ok(self.0.slice(start..end))
        }
    }

    struct LyingCas(Bytes);

    impl Cas for LyingCas {
        type Error = Infallible;
        type Object = LyingObject;

        fn open(&self, _: O256) -> Result<Option<Self::Object>, Self::Error> {
            Ok(Some(LyingObject(self.0.clone())))
        }
    }

    #[test]
    fn absence_is_retryable_and_success_is_cached() {
        let cas = MemoryCas::new();
        let mut bytes = Vec::new();
        wire::serialize(&Arena::empty(), &mut bytes).unwrap();
        let address = O256::from_bytes(&bytes);
        let link = Link {
            format: LinkFormat::Cbor,
            blake3: address,
        };
        let resolver = CasResolver::new(cas);

        assert!(resolver.resolve(&link).unwrap().is_none());
        assert_eq!(resolver.cas().insert(bytes).unwrap(), address);
        let arena = resolver.resolve(&link).unwrap().unwrap();
        assert!(arena.is_empty());
        assert!(Arc::ptr_eq(
            &arena,
            &resolver.resolve(&link).unwrap().unwrap()
        ));
    }

    #[test]
    fn malformed_content_is_not_cached() {
        let cas = MemoryCas::new();
        let address = cas.insert(&b"not an arena"[..]).unwrap();
        let link = Link {
            format: LinkFormat::Cbor,
            blake3: address,
        };
        let resolver = CasResolver::new(cas);

        assert!(matches!(resolver.resolve(&link), Err(Error::Decode(_))));
        assert!(resolver.cached(address).is_none());
    }

    #[test]
    fn content_is_authenticated_even_for_a_lying_cas() {
        let mut encoded = Vec::new();
        wire::serialize(&Arena::empty(), &mut encoded).unwrap();
        let bytes = Bytes::from(encoded);
        let actual = O256::from_bytes(bytes.as_ref());
        let expected = O256::from_bytes(b"a different object");
        assert_ne!(actual, expected);

        let resolver = CasResolver::new(LyingCas(bytes));
        let link = Link {
            format: LinkFormat::Cbor,
            blake3: expected,
        };
        assert!(matches!(
            resolver.resolve(&link),
            Err(Error::WrongAddress {
                expected: found_expected,
                actual: found_actual,
            }) if found_expected == expected && found_actual == actual
        ));
        assert!(resolver.cached(expected).is_none());
    }
}
