//! Async HTTP client for whole-object CAS reads.

use covalence_data_cas::{AsyncCas, AsyncCasError, CasFuture};
use covalence_lib_error::snafu::Snafu;
use covalence_lib_hash::O256;
use covalence_logic_cas::{Bytes, CasFact, CasLookupError};
use std::collections::TryReserveError;

use crate::{MAX_RESPONSE_BYTES, OBJECT_PREFIX};

/// A bounded, read-only HTTP CAS client.
///
/// The server is untrusted. [`Self::get_bytes`] deliberately returns raw
/// bytes, while [`Self::get_fact`] hashes the complete response before it can
/// introduce a checked [`CasFact`].
#[derive(Clone, Debug)]
pub struct HttpCas {
    client: reqwest::Client,
    base: reqwest::Url,
    max_object_bytes: u64,
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
        })
    }

    /// Sets the largest whole object this client will accept.
    #[must_use]
    pub const fn with_max_object_bytes(mut self, max_object_bytes: u64) -> Self {
        self.max_object_bytes = max_object_bytes;
        self
    }

    /// Gets untrusted bytes from the service.
    ///
    /// Absence is represented by `Ok(None)`. Any successful body remains
    /// untrusted until a caller hashes it or obtains it through
    /// [`Self::get_fact`].
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

    /// Gets a checked whole-object fact from the service.
    ///
    /// The client hashes the complete response against the requested address.
    /// An HTTP service cannot confer trust merely by naming a response after a
    /// hash.
    ///
    /// # Errors
    ///
    /// Returns [`CasLookupError::Provider`] for HTTP failures and
    /// [`CasLookupError::Check`] when returned bytes do not match `address`.
    pub async fn get_fact(
        &self,
        address: O256,
    ) -> Result<Option<CasFact>, CasLookupError<HttpCasError>> {
        self.get_bytes(address)
            .await
            .map_err(|source| CasLookupError::Provider {
                requested: address,
                source,
            })?
            .map(|bytes| {
                CasFact::new(address, bytes).map_err(|source| CasLookupError::Check {
                    requested: address,
                    source,
                })
            })
            .transpose()
    }

    fn object_url(&self, address: O256) -> reqwest::Url {
        let mut url = self.base.clone();
        url.set_path(&format!("{OBJECT_PREFIX}{}", address.hex()));
        url.set_query(None);
        url.set_fragment(None);
        url
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
