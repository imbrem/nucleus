//! Object-safe asynchronous CAS composition.

use std::error::Error;
use std::future::Future;
use std::pin::Pin;

use covalence_lib_error::snafu::Snafu;
use covalence_lib_hash::O256;
use covalence_logic_cas::{CasCheckError, CasFact};

use crate::{Bytes, Cas, IndexCas, SharedIndexCas};

/// A boxed CAS operation which may suspend.
pub type CasFuture<'a, T> = Pin<Box<dyn Future<Output = Result<T, AsyncCasError>> + Send + 'a>>;

/// Failure at the type-erased asynchronous CAS boundary.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum AsyncCasError {
    /// A concrete provider failed.
    #[snafu(display("CAS provider failed: {source}"))]
    Provider {
        /// Provider-specific error, preserved as the error source.
        source: Box<dyn Error + Send + Sync + 'static>,
    },
    /// Raw bytes did not match the requested address.
    #[snafu(display("CAS bytes for {requested} failed validation: {source}"))]
    Check {
        /// Requested address.
        requested: O256,
        /// Failed whole-object check.
        source: CasCheckError,
    },
}

impl AsyncCasError {
    /// Erases a concrete provider error while preserving its source chain.
    #[must_use]
    pub fn provider(source: impl Error + Send + Sync + 'static) -> Self {
        Self::Provider {
            source: Box::new(source),
        }
    }
}

/// An object-safe asynchronous source of content-addressed bytes and facts.
///
/// Implementations are untrusted. A runtime using an optimized [`get_fact`]
/// result must still check that its address equals the requested address.
/// Provider-specific APIs should retain concrete error types; errors are
/// erased only at this heterogeneous composition boundary.
///
/// [`get_fact`]: Self::get_fact
pub trait AsyncCas: Send + Sync {
    /// Gets all bytes at `address`, or `None` when absent.
    fn get_bytes(&self, address: O256) -> CasFuture<'_, Option<Bytes>>;

    /// Gets a checked whole-object fact, or `None` when absent.
    ///
    /// The default fetches raw bytes and hashes them. Providers that cache
    /// checked facts may override it, but callers must still verify the result
    /// answers the requested address.
    fn get_fact(&self, address: O256) -> CasFuture<'_, Option<CasFact>> {
        Box::pin(async move {
            self.get_bytes(address)
                .await?
                .map(|bytes| {
                    CasFact::new(address, bytes).map_err(|source| AsyncCasError::Check {
                        requested: address,
                        source,
                    })
                })
                .transpose()
        })
    }
}

macro_rules! async_resident_cas {
    ($cas:ty) => {
        impl AsyncCas for $cas {
            fn get_bytes(&self, address: O256) -> CasFuture<'_, Option<Bytes>> {
                Box::pin(
                    async move { Cas::get_bytes(self, address).map_err(AsyncCasError::provider) },
                )
            }

            fn get_fact(&self, address: O256) -> CasFuture<'_, Option<CasFact>> {
                Box::pin(async move { Ok(self.fact_at(address).map(|fact| fact.to_owned())) })
            }
        }
    };
}

async_resident_cas!(IndexCas);

impl AsyncCas for SharedIndexCas {
    fn get_bytes(&self, address: O256) -> CasFuture<'_, Option<Bytes>> {
        Box::pin(async move { Cas::get_bytes(self, address).map_err(AsyncCasError::provider) })
    }

    fn get_fact(&self, address: O256) -> CasFuture<'_, Option<CasFact>> {
        Box::pin(async move { Ok(self.fact_at(address)) })
    }
}
