//! Async content-addressed storage over the S3 object API.
//!
//! Objects use the portable key `cas/{lowercase-blake3}` by default. The
//! endpoint, region, credentials, and addressing style remain S3 client
//! configuration rather than CAS semantics, allowing the same implementation
//! to target AWS S3, Cloudflare R2, Backblaze B2, and local test servers.
//!
//! S3 and its responses are untrusted. [`S3Cas::get_bytes`] deliberately
//! returns ordinary bytes; [`S3Cas::get_fact`] hashes the complete response
//! before it can introduce a checked whole-object CAS fact.

use aws_config::{BehaviorVersion, Region, meta::region::RegionProviderChain};
use aws_sdk_s3::{
    Client,
    config::Credentials,
    error::SdkError,
    operation::{get_object::GetObjectError, put_object::PutObjectError},
    primitives::ByteStream,
};
use aws_smithy_types::byte_stream::error::Error as ByteStreamError;
use bytes::Bytes;
use covalence_data_cas::{AsyncCas, AsyncCasError, CasFuture};
use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_hash::O256;
use covalence_logic_cas::{CasCheckError, CasFact};

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
    credentials: Option<Credentials>,
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
        self.credentials = Some(Credentials::new(
            access_key_id,
            secret_access_key,
            session_token,
            None,
            "nucleus-explicit",
        ));
        self
    }
}

/// An async whole-object CAS backed by one S3 bucket and key prefix.
#[derive(Clone, Debug)]
pub struct S3Cas {
    client: Client,
    bucket: String,
    prefix: String,
    max_object_bytes: u64,
}

impl S3Cas {
    /// Builds an S3 client using the configured values and standard AWS
    /// provider chains for values which were omitted.
    pub async fn new(config: S3CasConfig) -> Self {
        let region = RegionProviderChain::first_try(config.region.map(Region::new))
            .or_default_provider()
            .or_else(Region::new("us-east-1"));
        let mut loader = aws_config::defaults(BehaviorVersion::latest()).region(region);
        if let Some(credentials) = config.credentials {
            loader = loader.credentials_provider(credentials);
        }
        if let Some(endpoint) = &config.endpoint {
            loader = loader.endpoint_url(endpoint);
        }
        let shared = loader.load().await;
        let service = aws_sdk_s3::config::Builder::from(&shared)
            .force_path_style(config.force_path_style)
            .build();
        Self {
            client: Client::from_conf(service),
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
        let result = self
            .client
            .get_object()
            .bucket(&self.bucket)
            .key(self.key(address))
            .send()
            .await;
        let output = match result {
            Ok(output) => output,
            Err(error) if is_not_found(&error) => return Ok(None),
            Err(source) => {
                return Err(S3CasError::Get {
                    source: Box::new(source),
                });
            }
        };
        if let Some(declared) = output.content_length() {
            let declared = u64::try_from(declared)
                .map_err(|_| S3CasError::InvalidContentLength { declared })?;
            if declared > self.max_object_bytes {
                return Err(S3CasError::ObjectTooLarge {
                    limit: self.max_object_bytes,
                    observed: declared,
                });
            }
        }

        let mut body = output.body;
        let initial = body.size_hint().1.unwrap_or(0).min(self.max_object_bytes);
        let initial = usize::try_from(initial).unwrap_or(usize::MAX);
        let mut bytes = Vec::new();
        bytes.try_reserve(initial).context(ReserveBodySnafu)?;
        while let Some(chunk) = body.try_next().await.context(ReadBodySnafu)? {
            let chunk_len = u64::try_from(chunk.len()).unwrap_or(u64::MAX);
            let observed = u64::try_from(bytes.len())
                .unwrap_or(u64::MAX)
                .saturating_add(chunk_len);
            if observed > self.max_object_bytes {
                return Err(S3CasError::ObjectTooLarge {
                    limit: self.max_object_bytes,
                    observed,
                });
            }
            bytes.try_reserve(chunk.len()).context(ReserveBodySnafu)?;
            bytes.extend_from_slice(&chunk);
        }
        Ok(Some(Bytes::from(bytes)))
    }

    /// Fetches and validates a whole-object CAS fact.
    ///
    /// # Errors
    ///
    /// Returns an S3 failure or [`S3CasError::Check`] when the bytes do not
    /// hash to the requested address.
    pub async fn get_fact(&self, address: O256) -> Result<Option<CasFact>, S3CasError> {
        self.get_bytes(address)
            .await?
            .map(|bytes| CasFact::new(address, bytes).context(CheckSnafu { address }))
            .transpose()
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
            .put_object()
            .bucket(&self.bucket)
            .key(self.key(address))
            .body(ByteStream::from(bytes))
            .send()
            .await
            .map_err(|source| S3CasError::Put {
                source: Box::new(source),
            })?;
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

fn is_not_found(error: &SdkError<GetObjectError>) -> bool {
    error
        .as_service_error()
        .is_some_and(GetObjectError::is_no_such_key)
}

/// Failure to access or validate an S3-backed CAS object.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum S3CasError {
    /// The object request failed.
    #[snafu(display("could not get S3 CAS object: {source}"))]
    Get {
        /// S3 SDK failure.
        source: Box<SdkError<GetObjectError>>,
    },
    /// Reading a successful object's response body failed.
    #[snafu(display("could not read S3 CAS object body: {source}"))]
    ReadBody {
        /// Streaming response failure.
        source: ByteStreamError,
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
    /// The response exceeded this CAS's configured admission limit.
    #[snafu(display("S3 CAS object exceeds {limit}-byte limit after {observed} bytes"))]
    ObjectTooLarge {
        /// Configured largest accepted object.
        limit: u64,
        /// Declared or received byte count which crossed the limit.
        observed: u64,
    },
    /// The downloaded object did not match its requested address.
    #[snafu(display("S3 CAS bytes for {address} failed validation: {source}"))]
    Check {
        /// Requested content address.
        address: O256,
        /// Whole-object validation failure.
        source: CasCheckError,
    },
    /// Uploading an object failed.
    #[snafu(display("could not put S3 CAS object: {source}"))]
    Put {
        /// S3 SDK failure.
        source: Box<SdkError<PutObjectError>>,
    },
}
