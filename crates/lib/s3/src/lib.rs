//! Narrow S3-compatible object operations used by Nucleus.
//!
//! This crate owns the AWS SDK dependency and translates its provider-specific
//! types into a small interface shared by AWS S3, Cloudflare R2, Backblaze B2,
//! and test servers. It deliberately does not define CAS key or trust policy.

use aws_config::{BehaviorVersion, Region, meta::region::RegionProviderChain};
use aws_sdk_s3::{
    Client, config::Credentials, error::SdkError, operation::get_object::GetObjectError,
    primitives::ByteStream,
};
use bytes::Bytes;
use covalence_lib_error::snafu::{ResultExt, Snafu};

/// Configuration for an S3-compatible service client.
#[derive(Clone, Debug, Default)]
pub struct S3Config {
    endpoint: Option<String>,
    region: Option<String>,
    force_path_style: bool,
    credentials: Option<Credentials>,
}

impl S3Config {
    /// Creates configuration using the standard AWS region and credential
    /// provider chains.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
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

    /// Sets credentials explicitly instead of using the AWS provider chain.
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

/// A client for the small subset of S3 object operations Nucleus uses.
#[derive(Clone, Debug)]
pub struct S3Client {
    client: Client,
}

impl S3Client {
    /// Builds a client from explicit settings and the standard AWS provider
    /// chains for omitted values.
    pub async fn new(config: S3Config) -> Self {
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
        }
    }

    /// Fetches one complete object, returning `None` only for `NoSuchKey`.
    ///
    /// Both declared and observed lengths are bounded. This method uses
    /// fallible allocation so an admitted remote response cannot abort the
    /// process merely because its buffer cannot be reserved.
    ///
    /// # Errors
    ///
    /// Returns a request or response streaming error, an invalid declared
    /// length, an allocation failure, or [`S3Error::ObjectTooLarge`].
    pub async fn get_bounded(
        &self,
        bucket: &str,
        key: &str,
        max_bytes: u64,
    ) -> Result<Option<Bytes>, S3Error> {
        let result = self
            .client
            .get_object()
            .bucket(bucket)
            .key(key)
            .send()
            .await;
        let output = match result {
            Ok(output) => output,
            Err(error) if is_not_found(&error) => return Ok(None),
            Err(source) => {
                return Err(S3Error::Get {
                    source: Box::new(source),
                });
            }
        };
        if let Some(declared) = output.content_length() {
            let declared =
                u64::try_from(declared).map_err(|_| S3Error::InvalidContentLength { declared })?;
            if declared > max_bytes {
                return Err(S3Error::ObjectTooLarge {
                    limit: max_bytes,
                    observed: declared,
                });
            }
        }

        let mut body = output.body;
        let initial = body.size_hint().1.unwrap_or(0).min(max_bytes);
        let initial = usize::try_from(initial).unwrap_or(usize::MAX);
        let mut bytes = Vec::new();
        bytes.try_reserve(initial).context(ReserveBodySnafu)?;
        while let Some(chunk) = body.try_next().await.map_err(|source| S3Error::ReadBody {
            source: Box::new(source),
        })? {
            let chunk_len = u64::try_from(chunk.len()).unwrap_or(u64::MAX);
            let observed = u64::try_from(bytes.len())
                .unwrap_or(u64::MAX)
                .saturating_add(chunk_len);
            if observed > max_bytes {
                return Err(S3Error::ObjectTooLarge {
                    limit: max_bytes,
                    observed,
                });
            }
            bytes.try_reserve(chunk.len()).context(ReserveBodySnafu)?;
            bytes.extend_from_slice(&chunk);
        }
        Ok(Some(Bytes::from(bytes)))
    }

    /// Stores one complete object.
    ///
    /// # Errors
    ///
    /// Returns an S3 upload failure.
    pub async fn put(&self, bucket: &str, key: &str, bytes: Bytes) -> Result<(), S3Error> {
        self.client
            .put_object()
            .bucket(bucket)
            .key(key)
            .body(ByteStream::from(bytes))
            .send()
            .await
            .map_err(|source| S3Error::Put {
                source: Box::new(source),
            })?;
        Ok(())
    }
}

fn is_not_found(error: &SdkError<GetObjectError>) -> bool {
    error
        .as_service_error()
        .is_some_and(GetObjectError::is_no_such_key)
}

/// Failure while accessing an S3-compatible object service.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum S3Error {
    /// The object request failed.
    #[snafu(display("could not get S3 object: {source}"))]
    Get {
        /// Provider failure, intentionally erased at the facade boundary.
        source: Box<dyn std::error::Error + Send + Sync>,
    },
    /// Reading a successful object's response body failed.
    #[snafu(display("could not read S3 object body: {source}"))]
    ReadBody {
        /// Provider streaming failure, intentionally erased at the facade boundary.
        source: Box<dyn std::error::Error + Send + Sync>,
    },
    /// Memory for a bounded response body could not be reserved.
    #[snafu(display("could not reserve memory for S3 object body: {source}"))]
    ReserveBody {
        /// Allocation reservation failure.
        source: std::collections::TryReserveError,
    },
    /// S3 supplied a negative declared response length.
    #[snafu(display("S3 object declared invalid content length {declared}"))]
    InvalidContentLength {
        /// Invalid signed content length.
        declared: i64,
    },
    /// The response exceeded the caller's configured admission limit.
    #[snafu(display("S3 object exceeds {limit}-byte limit after {observed} bytes"))]
    ObjectTooLarge {
        /// Configured largest accepted object.
        limit: u64,
        /// Declared or received byte count which crossed the limit.
        observed: u64,
    },
    /// Uploading an object failed.
    #[snafu(display("could not put S3 object: {source}"))]
    Put {
        /// Provider failure, intentionally erased at the facade boundary.
        source: Box<dyn std::error::Error + Send + Sync>,
    },
}
