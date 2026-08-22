use covalence_lib_error::snafu::Snafu;

use crate::{CasFact, O256};

/// A provider of checked whole-object CAS facts.
///
/// "Trusted" describes the result type, not the implementation: this trait is
/// deliberately public and unsealed, and any safe implementation can return
/// only a [`CasFact`] produced by the crate's checking rules. Implementations
/// may fetch, generate, or cache the complete bytes however they choose.
///
/// Calling [`Self::get`] establishes that its result is a valid hash/blob pair,
/// but an incorrect implementation can still return a valid fact for a
/// different request. Consumers must use [`get_exact`] to enforce that second
/// relation at their boundary.
pub trait TrustedCas {
    /// Implementation-specific lookup failure, including absence when
    /// applicable.
    type Error: std::error::Error + 'static;

    /// Gets a checked fact in response to `address`.
    ///
    /// The returned fact owns all of the object's bytes independently of the
    /// provider.
    ///
    /// # Errors
    ///
    /// Returns the provider's error when it cannot return a checked fact.
    fn get(&self, address: O256) -> Result<CasFact, Self::Error>;
}

/// Failure to get a fact for one exact requested address.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum GetError<E>
where
    E: std::error::Error + 'static,
{
    /// The provider failed to return a fact.
    #[snafu(display("could not get CAS object {requested}: {source}"))]
    Provider {
        /// Requested address.
        requested: O256,
        /// Provider-specific failure.
        source: E,
    },
    /// The provider returned a valid fact for a different address.
    #[snafu(display("CAS returned address {returned} for request {requested}"))]
    WrongAddress {
        /// Requested address.
        requested: O256,
        /// Address carried by the returned checked fact.
        returned: O256,
    },
}

impl<E> GetError<E>
where
    E: std::error::Error + 'static,
{
    /// Returns the requested address associated with this failure.
    #[must_use]
    pub const fn requested(&self) -> O256 {
        match self {
            Self::Provider { requested, .. } | Self::WrongAddress { requested, .. } => *requested,
        }
    }
}

/// Gets a checked fact and verifies that it answers the exact request.
///
/// This is the uniform consumer boundary for [`TrustedCas`]. It prevents a
/// buggy or adversarial implementation from making a valid fact for one hash
/// appear to answer a request for another.
///
/// # Errors
///
/// Returns [`GetError::Provider`] when the provider fails, or
/// [`GetError::WrongAddress`] when its checked fact carries another hash.
pub fn get_exact<C>(cas: &C, requested: O256) -> Result<CasFact, GetError<C::Error>>
where
    C: TrustedCas + ?Sized,
{
    let fact = cas
        .get(requested)
        .map_err(|source| GetError::Provider { requested, source })?;
    let returned = fact.hash();
    if returned == requested {
        Ok(fact)
    } else {
        Err(GetError::WrongAddress {
            requested,
            returned,
        })
    }
}
