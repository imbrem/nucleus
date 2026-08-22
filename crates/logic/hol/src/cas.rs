//! Retryable CAS-backed arena-link resolution.

use std::{collections::BTreeMap, sync::Arc, sync::RwLock};

use covalence_lib_hash::O256;
use covalence_logic_cas::{Cas, CasExt, CasLookupError};

use crate::{Arena, Link, Resolver, wire};

/// A CAS or arena-decoding failure.
#[derive(Debug)]
pub enum Error<E: std::error::Error + 'static> {
    Cas(CasLookupError<E>),
    Decode(wire::DecodeError),
}

impl<E: std::error::Error + 'static> std::fmt::Display for Error<E> {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Cas(error) => write!(output, "CAS lookup failed: {error}"),
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
        let Some(fact) = self.cas.get_checked(address).map_err(Error::Cas)? else {
            return Ok(None);
        };
        let arena = Arc::new(wire::deserialize(fact.as_ref()).map_err(Error::Decode)?);
        let mut cache = self
            .cache
            .write()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        Ok(Some(Arc::clone(cache.entry(address).or_insert(arena))))
    }
}

#[cfg(test)]
mod tests {
    use std::{io, ops::Range};

    use covalence_data_cas::SharedIndexCas;
    use covalence_logic_cas::Bytes;

    use super::*;
    use crate::{LinkFormat, Resolver};

    struct LyingCas(Bytes);

    impl Cas for LyingCas {
        type Error = io::Error;

        fn get_bytes(&self, _: O256) -> Result<Option<Bytes>, Self::Error> {
            Ok(Some(self.0.clone()))
        }

        fn get_range(&self, _: O256, range: Range<u64>) -> Result<Option<Bytes>, Self::Error> {
            let start = usize::try_from(range.start)
                .map_err(|_| io::Error::from(io::ErrorKind::InvalidInput))?;
            let end = usize::try_from(range.end)
                .map_err(|_| io::Error::from(io::ErrorKind::InvalidInput))?;
            let Some(bytes) = self.0.get(start..end) else {
                return Err(io::Error::from(io::ErrorKind::InvalidInput));
            };
            Ok(Some(Bytes::copy_from_slice(bytes)))
        }
    }

    #[test]
    fn absence_is_retryable_and_success_is_cached() {
        let cas = SharedIndexCas::new();
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
        let cas = SharedIndexCas::new();
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
            Err(Error::Cas(CasLookupError::Check {
                requested,
                source: _,
            })) if requested == expected
        ));
        assert!(resolver.cached(expected).is_none());
    }
}
