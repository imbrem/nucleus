//! Transport-neutral, composable CAS service operations.

use std::error::Error;
use std::future::Future;
use std::ops::Range;
use std::pin::Pin;

use covalence_lib_error::snafu::Snafu;
use covalence_lib_hash::O256;

use crate::{Bytes, SharedIndexCas};

const PREFIX_HINT_LIMIT: usize = 32;

/// A boxed service operation which may suspend on storage or computation.
pub type CasServiceFuture<'a, T> =
    Pin<Box<dyn Future<Output = Result<T, CasServiceError>> + Send + 'a>>;

/// Metadata returned after bytes have been admitted to a CAS.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StoredObject {
    /// The BLAKE3 address of the complete bytes.
    pub address: O256,
    /// The byte length of the object.
    pub len: u64,
    /// A provider-local stable index, when the provider exposes one.
    pub index: Option<u64>,
}

/// A byte range resolved against an immutable object's length.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ByteRange {
    /// A half-open bounded range.
    Bounded(Range<u64>),
    /// Bytes from this offset through the end of the object.
    From(u64),
    /// At most this many bytes from the end of the object.
    Suffix(u64),
}

/// One resolved range and its bytes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RangePart {
    /// Half-open range resolved against the complete object length.
    pub range: Range<u64>,
    /// Bytes in `range`.
    pub bytes: Bytes,
}

/// Bytes returned for a set of ranges from one immutable object.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObjectRanges {
    /// Complete object length against which every range was interpreted.
    pub len: u64,
    /// Range bytes, in the same order as the request.
    pub parts: Vec<RangePart>,
}

/// Optional refinements and backend claims for an ambiguous prefix.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PrefixHints {
    /// Bounded prefixes which refine the ambiguous query.
    pub prefixes: Vec<String>,
    /// Backend claim that every match is covered by at least one prefix.
    pub covers_all_matches: bool,
    /// Backend claim that every prefix covers at least one match.
    pub all_prefixes_match: bool,
}

/// Result of resolving a hexadecimal BLAKE3 address prefix.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PrefixResolution {
    /// The provider does not support prefix lookup.
    Unsupported,
    /// No resident address has this prefix.
    Missing,
    /// Exactly one resident address has this prefix.
    Unique(O256),
    /// More than one resident address has this prefix.
    Ambiguous {
        /// Optional backend claims and bounded refinements.
        hints: Option<PrefixHints>,
    },
}

/// Failure at the transport-neutral CAS service boundary.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum CasServiceError {
    /// A concrete storage provider failed.
    #[snafu(display("CAS provider failed: {source}"))]
    Provider {
        /// Provider-specific error, preserved as the source.
        source: Box<dyn Error + Send + Sync + 'static>,
    },
    /// Bytes supplied for a known address did not match it.
    #[snafu(display("CAS bytes computed address {computed}, expected {expected}"))]
    AddressMismatch {
        /// Address named by the caller.
        expected: O256,
        /// Address computed from the supplied bytes.
        computed: O256,
    },
    /// A requested range did not lie within the object.
    #[snafu(display("range {start}..{end} lies outside an object of {len} bytes"))]
    InvalidRange {
        /// Inclusive start offset.
        start: u64,
        /// Exclusive end offset.
        end: u64,
        /// Complete object length.
        len: u64,
    },
    /// An upload resource was used after it was finished.
    #[snafu(display("CAS upload is already finished"))]
    UploadFinished,
    /// An object exceeded an admission or transport limit.
    #[snafu(display("object of {len} bytes exceeds the {limit} byte limit"))]
    ObjectTooLarge {
        /// Observed or declared object length.
        len: u64,
        /// Applicable limit.
        limit: u64,
    },
}

impl CasServiceError {
    /// Erases a concrete provider error at the composable service boundary.
    #[must_use]
    pub fn provider(source: impl Error + Send + Sync + 'static) -> Self {
        Self::Provider {
            source: Box::new(source),
        }
    }
}

/// A composable service for complete objects and byte ranges.
///
/// This interface contains no HTTP concepts. A runtime may expose the same
/// object through HTTP, a Wasm host resource, an in-process cache, or another
/// [`CasService`] implementation. Implementations remain untrusted: callers
/// needing a checked fact must still hash complete bytes or use the checked
/// CAS API.
pub trait CasService: Send + Sync {
    /// Starts a streaming upload.
    ///
    /// When `expected` is present, finishing must fail unless the complete
    /// stream has that BLAKE3 address. Dropping the returned resource aborts
    /// the upload.
    fn begin_upload(&self, expected: Option<O256>)
    -> CasServiceFuture<'_, Box<dyn CasUpload + '_>>;

    /// Hashes and admits complete bytes.
    ///
    /// This convenience operation is defined in terms of a streaming upload.
    fn upload(&self, bytes: Bytes) -> CasServiceFuture<'_, StoredObject> {
        Box::pin(async move {
            let mut upload = self.begin_upload(None).await?;
            upload.write(bytes).await?;
            upload.finish().await
        })
    }

    /// Verifies and admits complete bytes at a caller-supplied BLAKE3 address.
    fn put(&self, address: O256, bytes: Bytes) -> CasServiceFuture<'_, StoredObject> {
        Box::pin(async move {
            let mut upload = self.begin_upload(Some(address)).await?;
            upload.write(bytes).await?;
            upload.finish().await
        })
    }

    /// Gets complete untrusted bytes, or `None` when absent.
    fn get(&self, address: O256) -> CasServiceFuture<'_, Option<Bytes>>;

    /// Gets several ranges from one immutable object.
    ///
    /// The result preserves request order. An empty list is valid and returns
    /// only the object's length. Implementations should resolve all ranges
    /// against one pinned view of the object.
    fn get_ranges(
        &self,
        address: O256,
        ranges: Vec<ByteRange>,
    ) -> CasServiceFuture<'_, Option<ObjectRanges>>;

    /// Resolves a normalized lowercase hexadecimal BLAKE3 address prefix.
    ///
    /// Providers which cannot perform an efficient or policy-permitted lookup
    /// may retain this default. Callers must not interpret unsupported lookup
    /// as object absence.
    fn resolve_blake3_prefix(&self, _prefix: String) -> CasServiceFuture<'_, PrefixResolution> {
        Box::pin(async { Ok(PrefixResolution::Unsupported) })
    }
}

/// An in-progress streaming upload.
///
/// Implementations may buffer, stream directly to an object store, or select
/// a provider-specific multipart strategy. Dropping a value without calling
/// [`Self::finish`] aborts the upload.
pub trait CasUpload: Send {
    /// Appends the next bytes in stream order.
    fn write(&mut self, bytes: Bytes) -> CasServiceFuture<'_, ()>;

    /// Completes, verifies, and admits the object.
    fn finish(&mut self) -> CasServiceFuture<'_, StoredObject>;
}

struct IndexUpload<'a> {
    cas: &'a SharedIndexCas,
    expected: Option<O256>,
    bytes: Option<Vec<u8>>,
}

impl CasUpload for IndexUpload<'_> {
    fn write(&mut self, chunk: Bytes) -> CasServiceFuture<'_, ()> {
        Box::pin(async move {
            let Some(bytes) = self.bytes.as_mut() else {
                return Err(CasServiceError::UploadFinished);
            };
            let new_len = bytes.len().saturating_add(chunk.len());
            if new_len as u64 > self.cas.limit() {
                return Err(CasServiceError::ObjectTooLarge {
                    len: new_len as u64,
                    limit: self.cas.limit(),
                });
            }
            bytes.extend_from_slice(&chunk);
            Ok(())
        })
    }

    fn finish(&mut self) -> CasServiceFuture<'_, StoredObject> {
        Box::pin(async move {
            let bytes = self.bytes.take().ok_or(CasServiceError::UploadFinished)?;
            let bytes = Bytes::from(bytes);
            let computed = O256::from_bytes(&bytes);
            if let Some(expected) = self.expected
                && computed != expected
            {
                return Err(CasServiceError::AddressMismatch { expected, computed });
            }
            let len = bytes.len() as u64;
            let address = self.cas.insert(bytes).map_err(CasServiceError::provider)?;
            Ok(StoredObject {
                address,
                len,
                index: self.cas.id(address),
            })
        })
    }
}

impl CasService for SharedIndexCas {
    fn begin_upload(
        &self,
        expected: Option<O256>,
    ) -> CasServiceFuture<'_, Box<dyn CasUpload + '_>> {
        Box::pin(async move {
            Ok(Box::new(IndexUpload {
                cas: self,
                expected,
                bytes: Some(Vec::new()),
            }) as Box<dyn CasUpload>)
        })
    }

    fn get(&self, address: O256) -> CasServiceFuture<'_, Option<Bytes>> {
        Box::pin(async move { Ok(self.fact_at(address).map(|fact| fact.bytes().clone())) })
    }

    fn get_ranges(
        &self,
        address: O256,
        ranges: Vec<ByteRange>,
    ) -> CasServiceFuture<'_, Option<ObjectRanges>> {
        Box::pin(async move {
            let Some(fact) = self.fact_at(address) else {
                return Ok(None);
            };
            let bytes = fact.bytes();
            let len = bytes.len() as u64;
            let mut parts = Vec::with_capacity(ranges.len());
            for requested in ranges {
                let range = match requested {
                    ByteRange::Bounded(range) => range,
                    ByteRange::From(start) => start..len,
                    ByteRange::Suffix(count) => len.saturating_sub(count)..len,
                };
                if range.start >= range.end || range.end > len {
                    return Err(CasServiceError::InvalidRange {
                        start: range.start,
                        end: range.end,
                        len,
                    });
                }
                let start = usize::try_from(range.start).unwrap_or_else(|_| unreachable!());
                let end = usize::try_from(range.end).unwrap_or_else(|_| unreachable!());
                parts.push(RangePart {
                    range,
                    bytes: bytes.slice(start..end),
                });
            }
            Ok(Some(ObjectRanges { len, parts }))
        })
    }

    fn resolve_blake3_prefix(&self, prefix: String) -> CasServiceFuture<'_, PrefixResolution> {
        Box::pin(async move {
            let mut matches = self
                .addresses()
                .into_iter()
                .filter(|address| address.hex().to_string().starts_with(&prefix));
            let Some(address) = matches.next() else {
                return Ok(PrefixResolution::Missing);
            };
            let Some(second) = matches.next() else {
                return Ok(PrefixResolution::Unique(address));
            };
            let mut prefixes = vec![address.hex().to_string(), second.hex().to_string()];
            prefixes.extend(
                matches
                    .by_ref()
                    .take(PREFIX_HINT_LIMIT - prefixes.len())
                    .map(|address| address.hex().to_string()),
            );
            let covers_all_matches = matches.next().is_none();
            Ok(PrefixResolution::Ambiguous {
                hints: Some(PrefixHints {
                    prefixes,
                    covers_all_matches,
                    all_prefixes_match: true,
                }),
            })
        })
    }
}

#[cfg(test)]
mod tests {
    use covalence_lib_hash::O256;

    use super::{ByteRange, CasService, CasServiceError, PrefixResolution, RangePart};
    use crate::{Bytes, SharedIndexCas};

    #[test]
    fn verified_put_rejects_wrong_bytes_before_admission() {
        let cas = SharedIndexCas::new();
        let expected = O256::from_bytes(b"expected");
        let result = futures::executor::block_on(cas.put(expected, Bytes::from_static(b"wrong")));
        assert!(matches!(
            result,
            Err(CasServiceError::AddressMismatch {
                expected: actual,
                ..
            }) if actual == expected
        ));
        assert!(cas.is_empty());
    }

    #[test]
    fn several_ranges_share_one_object_view() {
        let cas = SharedIndexCas::new();
        let stored =
            futures::executor::block_on(cas.upload(Bytes::from_static(b"abcdefgh"))).unwrap();
        let result = futures::executor::block_on(cas.get_ranges(
            stored.address,
            vec![ByteRange::Bounded(0..2), ByteRange::Suffix(3)],
        ))
        .unwrap()
        .unwrap();
        assert_eq!(result.len, 8);
        assert_eq!(
            result.parts,
            [
                RangePart {
                    range: 0..2,
                    bytes: Bytes::from_static(b"ab"),
                },
                RangePart {
                    range: 5..8,
                    bytes: Bytes::from_static(b"fgh"),
                },
            ]
        );
    }

    #[test]
    fn ambiguous_prefix_hints_state_their_two_guarantees_independently() {
        let cas = SharedIndexCas::new();
        cas.insert(b"first".as_slice()).unwrap();
        cas.insert(b"second".as_slice()).unwrap();
        let resolution =
            futures::executor::block_on(cas.resolve_blake3_prefix(String::new())).unwrap();
        let PrefixResolution::Ambiguous { hints: Some(hints) } = resolution else {
            panic!("two objects must make the empty prefix ambiguous");
        };
        assert_eq!(hints.prefixes.len(), 2);
        assert!(hints.covers_all_matches);
        assert!(hints.all_prefixes_match);
    }
}
