//! Async HTTP client for whole-object CAS reads.

use covalence_data_cas::{
    AsyncCas, AsyncCasError, ByteRange, CasFuture, CasService, CasServiceError, CasServiceFuture,
    CasUpload, ObjectRanges, PrefixHints, PrefixResolution, RangePart, StoredObject,
};
use covalence_lib_error::snafu::Snafu;
use covalence_lib_hash::O256;
use covalence_logic_cas::Bytes;
use std::collections::TryReserveError;

use crate::server::{PrefixChoicesDto, StoredObjectDto};
use crate::{BLAKE3_PREFIX, MAX_RESPONSE_BYTES, MAX_UPLOAD_BYTES, UPLOAD_PATH};

/// A bounded, read-only HTTP CAS client.
///
/// The server is untrusted. [`Self::get_bytes`] deliberately returns raw
/// bytes, while the [`AsyncCas`] default fact lookup hashes the complete
/// response before it can introduce a checked fact.
#[derive(Clone, Debug)]
pub struct HttpCas {
    client: reqwest::Client,
    base: reqwest::Url,
    max_object_bytes: u64,
    max_upload_bytes: u64,
}

/// Failure to configure or query an [`HttpCas`].
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum HttpCasError {
    /// The configured base URL is invalid.
    #[snafu(display("invalid HTTP CAS base URL {base:?}: {source}"))]
    InvalidBase {
        /// Rejected URL text.
        base: String,
        /// URL parse failure.
        source: reqwest::Error,
    },
    /// The URL does not select an HTTP transport.
    #[snafu(display("unsupported HTTP CAS URL scheme {scheme:?}"))]
    UnsupportedScheme {
        /// Rejected URL scheme.
        scheme: String,
    },
    /// The HTTP request failed before a complete response was available.
    #[snafu(display("could not fetch HTTP CAS object {address}: {source}"))]
    Request {
        /// Requested content address.
        address: O256,
        /// Transport failure.
        source: reqwest::Error,
    },
    /// The service returned an unexpected HTTP status.
    #[snafu(display("HTTP CAS returned status {status} for {address}"))]
    Status {
        /// Requested content address.
        address: O256,
        /// Unexpected status.
        status: reqwest::StatusCode,
    },
    /// The response exceeded the configured whole-object limit.
    #[snafu(display("HTTP CAS object {address} exceeds the {limit}-byte limit"))]
    TooLarge {
        /// Requested content address.
        address: O256,
        /// Configured maximum response size.
        limit: u64,
    },
    /// Memory for the bounded response could not be reserved.
    #[snafu(display("could not allocate HTTP CAS object {address}: {source}"))]
    Allocate {
        /// Requested content address.
        address: O256,
        /// Allocation failure.
        source: TryReserveError,
    },
    /// An upload request failed before a complete response was available.
    #[snafu(display("could not upload HTTP CAS object: {source}"))]
    UploadRequest {
        /// Transport failure.
        source: reqwest::Error,
    },
    /// An upload returned an unexpected status.
    #[snafu(display("HTTP CAS upload returned status {status}"))]
    UploadStatus {
        /// Unexpected status.
        status: reqwest::StatusCode,
    },
    /// An upload receipt was malformed or inconsistent.
    #[snafu(display("invalid HTTP CAS upload receipt: {message}"))]
    InvalidReceipt {
        /// Reason the receipt was rejected.
        message: String,
    },
    /// A prefix lookup returned an unexpected status.
    #[snafu(display("HTTP CAS prefix lookup returned status {status}"))]
    PrefixStatus {
        /// Unexpected status.
        status: reqwest::StatusCode,
    },
}

impl HttpCas {
    /// Creates a client using the conventional `/cas/{blake3}` object layout.
    ///
    /// # Errors
    ///
    /// Returns [`HttpCasError::InvalidBase`] if `base` is not an absolute HTTP
    /// or HTTPS URL.
    pub fn new(base: &str) -> Result<Self, HttpCasError> {
        // A redirect can cross the network boundary approved for the original
        // CAS endpoint. Policy-aware runtimes can construct a different
        // adapter later; the first-party backend takes the conservative path.
        let client = reqwest::Client::builder()
            .redirect(reqwest::redirect::Policy::none())
            .build()
            .map_err(|source| HttpCasError::InvalidBase {
                base: base.to_owned(),
                source,
            })?;
        let base = client
            .get(base)
            .build()
            .map_err(|source| HttpCasError::InvalidBase {
                base: base.to_owned(),
                source,
            })?
            .url()
            .clone();
        if !matches!(base.scheme(), "http" | "https") {
            return Err(HttpCasError::UnsupportedScheme {
                scheme: base.scheme().to_owned(),
            });
        }
        Ok(Self {
            client,
            base,
            max_object_bytes: MAX_RESPONSE_BYTES,
            max_upload_bytes: MAX_UPLOAD_BYTES as u64,
        })
    }

    /// Sets the largest whole object this client will accept.
    #[must_use]
    pub const fn with_max_object_bytes(mut self, max_object_bytes: u64) -> Self {
        self.max_object_bytes = max_object_bytes;
        self
    }

    /// Sets the largest object this client will buffer for upload.
    #[must_use]
    pub const fn with_max_upload_bytes(mut self, max_upload_bytes: u64) -> Self {
        self.max_upload_bytes = max_upload_bytes;
        self
    }

    /// Gets untrusted bytes from the service.
    ///
    /// Absence is represented by `Ok(None)`. Any successful body remains
    /// untrusted until a caller hashes it or obtains it through
    /// [`AsyncCas::get_fact`].
    ///
    /// # Errors
    ///
    /// Returns a transport, HTTP status, or response-size failure.
    pub async fn get_bytes(&self, address: O256) -> Result<Option<Bytes>, HttpCasError> {
        let url = self.object_url(address);
        let mut response = self
            .client
            .get(url)
            .send()
            .await
            .map_err(|source| HttpCasError::Request { address, source })?;

        if response.status() == reqwest::StatusCode::NOT_FOUND {
            return Ok(None);
        }
        if !response.status().is_success() {
            return Err(HttpCasError::Status {
                address,
                status: response.status(),
            });
        }
        if response
            .content_length()
            .is_some_and(|length| length > self.max_object_bytes)
        {
            return Err(HttpCasError::TooLarge {
                address,
                limit: self.max_object_bytes,
            });
        }

        let capacity = response
            .content_length()
            .unwrap_or(0)
            .min(self.max_object_bytes);
        let mut bytes = Vec::new();
        if let Ok(capacity) = usize::try_from(capacity) {
            reserve_response(&mut bytes, capacity, address)?;
        }
        while let Some(chunk) = response
            .chunk()
            .await
            .map_err(|source| HttpCasError::Request { address, source })?
        {
            let new_len = u64::try_from(bytes.len())
                .unwrap_or(u64::MAX)
                .saturating_add(u64::try_from(chunk.len()).unwrap_or(u64::MAX));
            if new_len > self.max_object_bytes {
                return Err(HttpCasError::TooLarge {
                    address,
                    limit: self.max_object_bytes,
                });
            }
            reserve_response(&mut bytes, chunk.len(), address)?;
            // `try_reserve` above guarantees this append does not allocate.
            bytes.extend_from_slice(&chunk);
        }
        Ok(Some(Bytes::from(bytes)))
    }

    fn object_url(&self, address: O256) -> reqwest::Url {
        let mut url = self.base.clone();
        url.set_path(&format!("{BLAKE3_PREFIX}{}", address.hex()));
        url.set_query(None);
        url.set_fragment(None);
        url
    }
}

impl HttpCas {
    async fn upload_bytes(
        &self,
        expected: Option<O256>,
        bytes: Bytes,
    ) -> Result<StoredObject, HttpCasError> {
        let mut url = self.base.clone();
        let request = if let Some(address) = expected {
            url.set_path(&format!("{BLAKE3_PREFIX}{}", address.hex()));
            self.client.put(url)
        } else {
            url.set_path(UPLOAD_PATH);
            self.client.put(url)
        };
        let response = request
            .body(bytes.clone())
            .send()
            .await
            .map_err(|source| HttpCasError::UploadRequest { source })?;
        if !response.status().is_success() {
            return Err(HttpCasError::UploadStatus {
                status: response.status(),
            });
        }
        let receipt = response
            .json::<StoredObjectDto>()
            .await
            .map_err(|source| HttpCasError::UploadRequest { source })?;
        if receipt.algorithm != "blake3" {
            return Err(HttpCasError::InvalidReceipt {
                message: format!("unsupported algorithm {:?}", receipt.algorithm),
            });
        }
        let address =
            receipt
                .hash
                .parse::<O256>()
                .map_err(|source| HttpCasError::InvalidReceipt {
                    message: source.to_string(),
                })?;
        let computed = O256::from_bytes(&bytes);
        if address != computed || expected.is_some_and(|expected| expected != address) {
            return Err(HttpCasError::InvalidReceipt {
                message: format!("receipt address {address} does not match uploaded bytes"),
            });
        }
        if receipt.bytes != bytes.len() as u64 {
            return Err(HttpCasError::InvalidReceipt {
                message: format!(
                    "receipt length {} does not match {} uploaded bytes",
                    receipt.bytes,
                    bytes.len()
                ),
            });
        }
        Ok(StoredObject {
            address,
            len: receipt.bytes,
            index: receipt.index,
        })
    }

    async fn object_len(&self, address: O256) -> Result<Option<u64>, HttpCasError> {
        let response = self
            .client
            .head(self.object_url(address))
            .send()
            .await
            .map_err(|source| HttpCasError::Request { address, source })?;
        if response.status() == reqwest::StatusCode::NOT_FOUND {
            return Ok(None);
        }
        if !response.status().is_success() {
            return Err(HttpCasError::Status {
                address,
                status: response.status(),
            });
        }
        let len = response
            .content_length()
            .ok_or_else(|| HttpCasError::InvalidReceipt {
                message: "HEAD response omitted Content-Length".to_owned(),
            })?;
        Ok(Some(len))
    }

    async fn get_one_range(
        &self,
        address: O256,
        range: std::ops::Range<u64>,
    ) -> Result<Bytes, HttpCasError> {
        if range.end - range.start > self.max_object_bytes {
            return Err(HttpCasError::TooLarge {
                address,
                limit: self.max_object_bytes,
            });
        }
        let response = self
            .client
            .get(self.object_url(address))
            .header(
                reqwest::header::RANGE,
                format!("bytes={}-{}", range.start, range.end - 1),
            )
            .send()
            .await
            .map_err(|source| HttpCasError::Request { address, source })?;
        if response.status() != reqwest::StatusCode::PARTIAL_CONTENT {
            return Err(HttpCasError::Status {
                address,
                status: response.status(),
            });
        }
        let bytes = response
            .bytes()
            .await
            .map_err(|source| HttpCasError::Request { address, source })?;
        if bytes.len() as u64 != range.end - range.start {
            return Err(HttpCasError::InvalidReceipt {
                message: format!("range response has {} bytes", bytes.len()),
            });
        }
        Ok(bytes)
    }
}

struct HttpUpload<'a> {
    cas: &'a HttpCas,
    expected: Option<O256>,
    bytes: Option<Vec<u8>>,
}

impl CasUpload for HttpUpload<'_> {
    fn write(&mut self, chunk: Bytes) -> CasServiceFuture<'_, ()> {
        Box::pin(async move {
            let Some(bytes) = self.bytes.as_mut() else {
                return Err(CasServiceError::UploadFinished);
            };
            let new_len = (bytes.len() as u64).saturating_add(chunk.len() as u64);
            if new_len > self.cas.max_upload_bytes {
                return Err(CasServiceError::ObjectTooLarge {
                    len: new_len,
                    limit: self.cas.max_upload_bytes,
                });
            }
            bytes.extend_from_slice(&chunk);
            Ok(())
        })
    }

    fn finish(&mut self) -> CasServiceFuture<'_, StoredObject> {
        Box::pin(async move {
            let bytes = self.bytes.take().ok_or(CasServiceError::UploadFinished)?;
            self.cas
                .upload_bytes(self.expected, Bytes::from(bytes))
                .await
                .map_err(CasServiceError::provider)
        })
    }
}

impl CasService for HttpCas {
    fn begin_upload(
        &self,
        expected: Option<O256>,
    ) -> CasServiceFuture<'_, Box<dyn CasUpload + '_>> {
        Box::pin(async move {
            Ok(Box::new(HttpUpload {
                cas: self,
                expected,
                bytes: Some(Vec::new()),
            }) as Box<dyn CasUpload>)
        })
    }

    fn get(&self, address: O256) -> CasServiceFuture<'_, Option<Bytes>> {
        Box::pin(async move {
            self.get_bytes(address)
                .await
                .map_err(CasServiceError::provider)
        })
    }

    fn get_ranges(
        &self,
        address: O256,
        ranges: Vec<ByteRange>,
    ) -> CasServiceFuture<'_, Option<ObjectRanges>> {
        Box::pin(async move {
            let Some(len) = self
                .object_len(address)
                .await
                .map_err(CasServiceError::provider)?
            else {
                return Ok(None);
            };
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
                let bytes = self
                    .get_one_range(address, range.clone())
                    .await
                    .map_err(CasServiceError::provider)?;
                parts.push(RangePart { range, bytes });
            }
            Ok(Some(ObjectRanges { len, parts }))
        })
    }

    fn resolve_blake3_prefix(&self, prefix: String) -> CasServiceFuture<'_, PrefixResolution> {
        Box::pin(async move {
            let mut url = self.base.clone();
            url.set_path(&format!("{BLAKE3_PREFIX}{prefix}"));
            let response = self
                .client
                .get(url)
                .send()
                .await
                .map_err(|source| HttpCasError::UploadRequest { source })
                .map_err(CasServiceError::provider)?;
            match response.status() {
                reqwest::StatusCode::TEMPORARY_REDIRECT => {
                    let address = response
                        .headers()
                        .get(reqwest::header::LOCATION)
                        .and_then(|location| location.to_str().ok())
                        .and_then(|location| location.rsplit('/').next())
                        .and_then(|address| address.parse::<O256>().ok())
                        .ok_or_else(|| {
                            CasServiceError::provider(HttpCasError::InvalidReceipt {
                                message: "prefix redirect omitted a canonical BLAKE3 location"
                                    .to_owned(),
                            })
                        })?;
                    Ok(PrefixResolution::Unique(address))
                }
                reqwest::StatusCode::NOT_FOUND => Ok(PrefixResolution::Missing),
                reqwest::StatusCode::MULTIPLE_CHOICES => {
                    let choices = response
                        .json::<PrefixChoicesDto>()
                        .await
                        .map_err(|source| {
                            CasServiceError::provider(HttpCasError::UploadRequest { source })
                        })?;
                    if choices.algorithm != "blake3" || choices.prefix != prefix {
                        return Err(CasServiceError::provider(HttpCasError::InvalidReceipt {
                            message: "prefix choices do not describe the request".to_owned(),
                        }));
                    }
                    if choices.hints.as_ref().is_some_and(|hints| {
                        hints.prefixes.iter().any(|candidate| {
                            candidate.len() > 64
                                || !candidate.starts_with(&prefix)
                                || !candidate.bytes().all(|byte| byte.is_ascii_hexdigit())
                        })
                    }) {
                        return Err(CasServiceError::provider(HttpCasError::InvalidReceipt {
                            message: "prefix choices contain an invalid refinement".to_owned(),
                        }));
                    }
                    Ok(PrefixResolution::Ambiguous {
                        hints: choices.hints.map(|hints| PrefixHints {
                            prefixes: hints.prefixes,
                            covers_all_matches: hints.covers_all_matches,
                            all_prefixes_match: hints.all_prefixes_match,
                        }),
                    })
                }
                reqwest::StatusCode::NOT_IMPLEMENTED => Ok(PrefixResolution::Unsupported),
                status => Err(CasServiceError::provider(HttpCasError::PrefixStatus {
                    status,
                })),
            }
        })
    }
}

fn reserve_response(
    bytes: &mut Vec<u8>,
    additional: usize,
    address: O256,
) -> Result<(), HttpCasError> {
    bytes
        .try_reserve(additional)
        .map_err(|source| HttpCasError::Allocate { address, source })
}

impl AsyncCas for HttpCas {
    fn get_bytes(&self, address: O256) -> CasFuture<'_, Option<Bytes>> {
        Box::pin(async move {
            HttpCas::get_bytes(self, address)
                .await
                .map_err(AsyncCasError::provider)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{HttpCasError, reserve_response};
    use covalence_lib_hash::O256;

    #[test]
    fn allocation_failure_is_typed() {
        let address = O256::from_bytes(b"allocation test");
        let error = reserve_response(&mut Vec::new(), usize::MAX, address).unwrap_err();
        assert!(matches!(
            error,
            HttpCasError::Allocate {
                address: actual,
                ..
            } if actual == address
        ));
    }
}
