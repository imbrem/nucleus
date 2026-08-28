//! Async content-addressed storage over the S3 object API.
//!
//! Objects use the portable key `cas/{lowercase-blake3}` by default. The
//! endpoint, region, credentials, and addressing style remain S3 client
//! configuration rather than CAS semantics, allowing the same implementation
//! to target AWS S3, Cloudflare R2, Backblaze B2, and local test servers.
//!
//! S3 and its responses are untrusted. [`S3Cas::get_bytes`] deliberately
//! returns ordinary bytes; the [`AsyncCas`] default hashes the complete
//! response before it can introduce a checked whole-object CAS fact.

use bytes::Bytes;
use covalence_data_cas::{
    AsyncCas, AsyncCasError, ByteRange, CasFuture, CasService, CasServiceError, CasServiceFuture,
    CasUpload, ObjectRanges, RangePart, StoredObject,
};
use covalence_lib_error::snafu::Snafu;
use covalence_lib_hash::O256;
use covalence_lib_s3::{S3Client, S3Config, S3Error};

/// Conventional top-level key prefix for whole CAS objects.
pub const DEFAULT_PREFIX: &str = "cas";

/// Default largest object accepted from an S3 response (64 MiB).
pub const DEFAULT_MAX_OBJECT_BYTES: u64 = 64 * 1024 * 1024;

/// Configuration for one S3-compatible CAS namespace.
#[derive(Clone, Debug)]
pub struct S3CasConfig {
    bucket: String,
    prefix: String,
    endpoint: Option<String>,
    region: Option<String>,
    force_path_style: bool,
    credentials: Option<(String, String, Option<String>)>,
    max_object_bytes: u64,
}

impl S3CasConfig {
    /// Creates configuration for `bucket` using `cas/` and the standard AWS
    /// region and credential provider chains.
    #[must_use]
    pub fn new(bucket: impl Into<String>) -> Self {
        Self {
            bucket: bucket.into(),
            prefix: DEFAULT_PREFIX.to_owned(),
            endpoint: None,
            region: None,
            force_path_style: false,
            credentials: None,
            max_object_bytes: DEFAULT_MAX_OBJECT_BYTES,
        }
    }

    /// Sets the key prefix. Leading and trailing slashes are ignored.
    #[must_use]
    pub fn with_prefix(mut self, prefix: impl Into<String>) -> Self {
        prefix.into().trim_matches('/').clone_into(&mut self.prefix);
        self
    }

    /// Sets an S3-compatible endpoint URL.
    #[must_use]
    pub fn with_endpoint(mut self, endpoint: impl Into<String>) -> Self {
        self.endpoint = Some(endpoint.into());
        self
    }

    /// Sets the signing region.
    #[must_use]
    pub fn with_region(mut self, region: impl Into<String>) -> Self {
        self.region = Some(region.into());
        self
    }

    /// Selects path-style (`endpoint/bucket/key`) addressing.
    #[must_use]
    pub const fn with_path_style(mut self, enabled: bool) -> Self {
        self.force_path_style = enabled;
        self
    }

    /// Sets the largest response body this CAS will accept.
    ///
    /// The limit is checked against both the declared response length and the
    /// bytes actually received, so a missing or dishonest `Content-Length`
    /// cannot bypass it.
    #[must_use]
    pub const fn with_max_object_bytes(mut self, max_object_bytes: u64) -> Self {
        self.max_object_bytes = max_object_bytes;
        self
    }

    /// Sets credentials explicitly instead of using the AWS provider chain.
    ///
    /// Prefer the provider chain for applications. This hook is useful for
    /// isolated tests and runtimes which already hold scoped credentials.
    #[must_use]
    pub fn with_credentials(
        mut self,
        access_key_id: impl Into<String>,
        secret_access_key: impl Into<String>,
        session_token: Option<String>,
    ) -> Self {
        self.credentials = Some((
            access_key_id.into(),
            secret_access_key.into(),
            session_token,
        ));
        self
    }
}

/// An async whole-object CAS backed by one S3 bucket and key prefix.
#[derive(Clone, Debug)]
pub struct S3Cas {
    client: S3Client,
    bucket: String,
    prefix: String,
    max_object_bytes: u64,
}

impl S3Cas {
    /// Builds an S3 client using the configured values and standard AWS
    /// provider chains for values which were omitted.
    pub async fn new(config: S3CasConfig) -> Self {
        let mut client_config = S3Config::new().with_path_style(config.force_path_style);
        if let Some(region) = config.region {
            client_config = client_config.with_region(region);
        }
        if let Some(endpoint) = config.endpoint {
            client_config = client_config.with_endpoint(endpoint);
        }
        if let Some((access_key_id, secret_access_key, session_token)) = config.credentials {
            client_config =
                client_config.with_credentials(access_key_id, secret_access_key, session_token);
        }
        Self {
            client: S3Client::new(client_config).await,
            bucket: config.bucket,
            prefix: config.prefix,
            max_object_bytes: config.max_object_bytes,
        }
    }

    /// Returns the canonical object key for `address`.
    #[must_use]
    pub fn key(&self, address: O256) -> String {
        if self.prefix.is_empty() {
            address.to_string()
        } else {
            format!("{}/{address}", self.prefix)
        }
    }

    /// Fetches untrusted bytes, or `None` when the object is absent.
    ///
    /// # Errors
    ///
    /// Returns an S3 request or response-body failure, or rejects a response
    /// which exceeds the configured object-size limit.
    pub async fn get_bytes(&self, address: O256) -> Result<Option<Bytes>, S3CasError> {
        self.client
            .get_bounded(&self.bucket, &self.key(address), self.max_object_bytes)
            .await
            .map_err(|source| match source {
                S3Error::Get { .. } | S3Error::Put { .. } => S3CasError::Get { source },
                S3Error::ReadBody { .. } => S3CasError::ReadBody { source },
                S3Error::ReserveBody { source } => S3CasError::ReserveBody { source },
                S3Error::InvalidContentLength { declared } => {
                    S3CasError::InvalidContentLength { declared }
                }
                S3Error::ObjectTooLarge { limit, observed } => {
                    S3CasError::ObjectTooLarge { limit, observed }
                }
            })
    }

    /// Stores bytes at their canonical content-derived key and returns their
    /// BLAKE3 address.
    ///
    /// # Errors
    ///
    /// Returns [`S3CasError::ObjectTooLarge`] before making a request when the
    /// bytes exceed the configured object-size limit, or an S3 upload failure.
    pub async fn insert(&self, bytes: Bytes) -> Result<O256, S3CasError> {
        let observed = u64::try_from(bytes.len()).unwrap_or(u64::MAX);
        if observed > self.max_object_bytes {
            return Err(S3CasError::ObjectTooLarge {
                limit: self.max_object_bytes,
                observed,
            });
        }
        let address = O256::from_bytes(&bytes);
        self.client
            .put(&self.bucket, &self.key(address), bytes)
            .await
            .map_err(|source| S3CasError::Put { source })?;
        Ok(address)
    }
}

impl AsyncCas for S3Cas {
    fn get_bytes(&self, address: O256) -> CasFuture<'_, Option<Bytes>> {
        Box::pin(async move {
            S3Cas::get_bytes(self, address)
                .await
                .map_err(AsyncCasError::provider)
        })
    }
}

struct S3Upload<'a> {
    cas: &'a S3Cas,
    expected: Option<O256>,
    bytes: Option<Vec<u8>>,
}

impl CasUpload for S3Upload<'_> {
    fn write(&mut self, chunk: Bytes) -> CasServiceFuture<'_, ()> {
        Box::pin(async move {
            let Some(bytes) = self.bytes.as_mut() else {
                return Err(CasServiceError::UploadFinished);
            };
            let new_len = bytes.len().saturating_add(chunk.len()) as u64;
            if new_len > self.cas.max_object_bytes {
                return Err(CasServiceError::ObjectTooLarge {
                    len: new_len,
                    limit: self.cas.max_object_bytes,
                });
            }
            bytes.extend_from_slice(&chunk);
            Ok(())
        })
    }

    fn finish(&mut self) -> CasServiceFuture<'_, StoredObject> {
        Box::pin(async move {
            let bytes = Bytes::from(self.bytes.take().ok_or(CasServiceError::UploadFinished)?);
            let computed = O256::from_bytes(&bytes);
            if let Some(expected) = self.expected
                && expected != computed
            {
                return Err(CasServiceError::AddressMismatch { expected, computed });
            }
            let len = bytes.len() as u64;
            let address = self
                .cas
                .insert(bytes)
                .await
                .map_err(CasServiceError::provider)?;
            Ok(StoredObject {
                address,
                len,
                index: None,
            })
        })
    }
}

impl CasService for S3Cas {
    fn begin_upload(
        &self,
        expected: Option<O256>,
    ) -> CasServiceFuture<'_, Box<dyn CasUpload + '_>> {
        Box::pin(async move {
            Ok(Box::new(S3Upload {
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
            let Some(bytes) = self
                .get_bytes(address)
                .await
                .map_err(CasServiceError::provider)?
            else {
                return Ok(None);
            };
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
}

/// Failure to access or validate an S3-backed CAS object.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum S3CasError {
    /// The object request failed.
    #[snafu(display("could not get S3 CAS object: {source}"))]
    Get {
        /// Facade-level S3 failure.
        source: S3Error,
    },
    /// Reading a successful object's response body failed.
    #[snafu(display("could not read S3 CAS object body: {source}"))]
    ReadBody {
        /// Facade-level S3 streaming failure.
        source: S3Error,
    },
    /// Memory for a bounded response body could not be reserved.
    #[snafu(display("could not reserve memory for S3 CAS object body: {source}"))]
    ReserveBody {
        /// Allocation reservation failure.
        source: std::collections::TryReserveError,
    },
    /// S3 supplied a negative declared response length.
    #[snafu(display("S3 CAS object declared invalid content length {declared}"))]
    InvalidContentLength {
        /// Invalid signed content length.
        declared: i64,
    },
    /// The response or upload exceeded this CAS's configured admission limit.
    #[snafu(display("S3 CAS object exceeds {limit}-byte limit after {observed} bytes"))]
    ObjectTooLarge {
        /// Configured largest accepted object.
        limit: u64,
        /// Declared, received, or upload byte count which crossed the limit.
        observed: u64,
    },
    /// Uploading an object failed.
    #[snafu(display("could not put S3 CAS object: {source}"))]
    Put {
        /// Facade-level S3 upload failure.
        source: S3Error,
    },
}
