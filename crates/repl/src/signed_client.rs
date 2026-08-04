//! Transport-free client state for signed kernel-service invocations.
//!
//! This module deliberately performs no I/O. A native HTTP client, browser `fetch` adapter, Worker
//! bridge, or in-process endpoint can carry the exact grant, invocation, and result bytes while
//! sharing the same controller identity and replay discipline.

use std::collections::HashMap;
use std::error::Error as StdError;
use std::fmt;

use covalence_kernel_service::{
    Operation, operation_schema,
    rpc::{RpcCodecError, ServiceRequest, ServiceResponse},
    wire::{
        ChannelGrant, ChannelNonce, MessageSigningError, PublicKeyIdentity, SignedInvocation,
        SignedResult, StatementSigner, WireError,
    },
};
use covalence_lib_crypto::ed25519::VerifyingKey;

use super::KernelId;

/// Transport-independent signed client with one independently keyed controller identity.
///
/// Each kernel route has at most one recipient-issued channel and at most one in-flight
/// invocation. Preparing an invocation does not advance its sequence; only accepting the exact
/// verified result advances it. Callers must abandon a pending invocation after an ambiguous I/O
/// failure so the sequence is never guessed or reused.
pub struct SignedKernelClient {
    controller: covalence_nucleus::Kernel,
    routes: HashMap<KernelId, ClientRoute>,
}

struct ClientRoute {
    recipient: VerifyingKey,
    grant: ChannelGrant,
    next_sequence: Option<u64>,
    in_flight: bool,
}

/// One signed invocation awaiting the exact recipient-signed result.
///
/// This value is intentionally not cloneable. Transport code may encode it repeatedly, but must
/// consume it through [`SignedKernelClient::accept_result`] or
/// [`SignedKernelClient::abandon_pending`].
pub struct PendingInvocation {
    kernel: KernelId,
    operation: Operation,
    invocation: SignedInvocation,
}

impl PendingInvocation {
    /// Kernel route which must receive this invocation.
    #[must_use]
    pub const fn kernel(&self) -> KernelId {
        self.kernel
    }

    /// Exact canonical signed invocation bytes for an endpoint transport.
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        self.invocation.encode()
    }

    /// Monotonic sequence reserved by this invocation but not yet advanced by the client.
    #[must_use]
    pub const fn sequence(&self) -> u64 {
        self.invocation.sequence()
    }

    /// Public route coordinates to retain before consuming this value through result acceptance.
    ///
    /// An endpoint adapter can use these for best-effort revocation if acceptance poisons and
    /// removes the client route.
    #[must_use]
    pub const fn channel_coordinates(&self) -> ChannelCoordinates {
        ChannelCoordinates {
            caller: self.invocation.caller(),
            recipient: self.invocation.recipient(),
            channel: self.invocation.channel(),
        }
    }
}

/// Public coordinates identifying one recipient-issued route.
///
/// These values contain no secret material. An endpoint adapter can retain them for a bounded,
/// authenticated channel-revocation protocol.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ChannelCoordinates {
    /// Controller key authorized to sign invocations.
    pub caller: PublicKeyIdentity,
    /// Exact pinned recipient key which issued the channel.
    pub recipient: PublicKeyIdentity,
    /// Fresh recipient-issued channel nonce.
    pub channel: ChannelNonce,
}

impl SignedKernelClient {
    /// Creates a client with a fresh controller key independent of every managed kernel.
    #[must_use]
    pub fn ephemeral() -> Self {
        Self {
            controller: covalence_nucleus::Kernel::ephemeral(),
            routes: HashMap::new(),
        }
    }

    /// Returns the controller public key which recipients must bind into channel grants.
    #[must_use]
    pub fn caller_public_key(&self) -> PublicKeyIdentity {
        *self.controller.verifying_key().as_bytes()
    }

    /// Accepts one canonical recipient-signed channel grant for `kernel`.
    ///
    /// The grant must bind this client's exact controller key and the exact caller-pinned
    /// recipient key. An existing route is never silently replaced.
    ///
    /// # Errors
    ///
    /// Returns an error for an existing route, malformed recipient key or grant, caller/recipient
    /// mismatch, or invalid recipient signature.
    pub fn accept_grant(
        &mut self,
        kernel: KernelId,
        pinned_recipient: PublicKeyIdentity,
        encoded_grant: &[u8],
    ) -> Result<(), SignedClientError> {
        if self.routes.contains_key(&kernel) {
            return Err(SignedClientError::RouteAlreadyExists(kernel));
        }
        let recipient = VerifyingKey::from_bytes(&pinned_recipient)
            .map_err(|_| SignedClientError::InvalidRecipientKey)?;
        let grant = ChannelGrant::decode(encoded_grant).map_err(SignedClientError::Wire)?;
        grant
            .verify(self.caller_public_key(), &recipient)
            .map_err(SignedClientError::Wire)?;
        self.routes.insert(
            kernel,
            ClientRoute {
                next_sequence: Some(grant.initial_sequence()),
                recipient,
                grant,
                in_flight: false,
            },
        );
        Ok(())
    }

    /// Returns the exact verified grant currently installed for `kernel`.
    #[must_use]
    pub fn grant(&self, kernel: KernelId) -> Option<&ChannelGrant> {
        self.routes.get(&kernel).map(|route| &route.grant)
    }

    /// Returns public caller, recipient, and channel coordinates for `kernel`.
    #[must_use]
    pub fn channel_coordinates(&self, kernel: KernelId) -> Option<ChannelCoordinates> {
        self.routes
            .get(&kernel)
            .map(|route| coordinates(&route.grant))
    }

    /// Signs one request on the route's exact next sequence without advancing it.
    ///
    /// A route permits only one outstanding [`PendingInvocation`].
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown route, an already in-flight request, sequence exhaustion,
    /// canonical frame bounds, or controller signing failure.
    pub fn prepare(
        &mut self,
        kernel: KernelId,
        request: &ServiceRequest,
    ) -> Result<PendingInvocation, SignedClientError> {
        let route = self
            .routes
            .get(&kernel)
            .ok_or(SignedClientError::UnknownRoute(kernel))?;
        if route.in_flight {
            return Err(SignedClientError::InvocationInFlight(kernel));
        }
        let sequence = route
            .next_sequence
            .ok_or(SignedClientError::SequenceExhausted(kernel))?;
        let payload = request.encode();
        let invocation = SignedInvocation::sign(
            operation_schema(request.operation()),
            &NucleusStatementSigner(self.controller.signer()),
            route.grant.recipient(),
            route.grant.channel(),
            sequence,
            request.value_id(),
            payload,
        )
        .map_err(SignedClientError::signing)?;
        self.routes
            .get_mut(&kernel)
            .ok_or(SignedClientError::UnknownRoute(kernel))?
            .in_flight = true;
        Ok(PendingInvocation {
            kernel,
            operation: request.operation(),
            invocation,
        })
    }

    /// Verifies and decodes the exact result for one pending invocation, then advances the route.
    ///
    /// Any malformed frame, authentication failure, stale pending value, payload-codec failure,
    /// operation mismatch, or output-value mismatch poisons and removes the entire route. A valid
    /// result at sequence `u64::MAX` is accepted once and leaves the route exhausted.
    ///
    /// # Errors
    ///
    /// Returns a strongly classified route, wire, codec, operation, or value-identity error.
    #[allow(clippy::needless_pass_by_value)] // Consuming the linear pending token prevents reuse.
    pub fn accept_result(
        &mut self,
        pending: PendingInvocation,
        encoded_result: &[u8],
    ) -> Result<ServiceResponse, SignedClientError> {
        let verified = self.verify_result(&pending, encoded_result);
        let response = match verified {
            Ok(response) => response,
            Err(error) => {
                self.routes.remove(&pending.kernel);
                return Err(error);
            }
        };
        let route = self
            .routes
            .get_mut(&pending.kernel)
            .ok_or(SignedClientError::UnknownRoute(pending.kernel))?;
        route.in_flight = false;
        route.next_sequence = pending.invocation.sequence().checked_add(1);
        Ok(response)
    }

    /// Abandons an invocation after ambiguous transport failure and removes its route.
    ///
    /// The route is removed only when `pending` still names its exact in-flight channel and
    /// sequence. Returned public coordinates can be used for best-effort endpoint revocation.
    #[must_use]
    #[allow(clippy::needless_pass_by_value)] // Consuming the linear pending token prevents reuse.
    pub fn abandon_pending(&mut self, pending: PendingInvocation) -> Option<ChannelCoordinates> {
        let matches = self
            .routes
            .get(&pending.kernel)
            .is_some_and(|route| pending_matches(route, &pending));
        matches
            .then(|| self.routes.remove(&pending.kernel))
            .flatten()
            .map(|route| coordinates(&route.grant))
    }

    /// Removes a route explicitly and returns its public revocation coordinates.
    #[must_use]
    pub fn remove_route(&mut self, kernel: KernelId) -> Option<ChannelCoordinates> {
        self.routes
            .remove(&kernel)
            .map(|route| coordinates(&route.grant))
    }

    fn verify_result(
        &self,
        pending: &PendingInvocation,
        encoded_result: &[u8],
    ) -> Result<ServiceResponse, SignedClientError> {
        let route = self
            .routes
            .get(&pending.kernel)
            .ok_or(SignedClientError::UnknownRoute(pending.kernel))?;
        if !pending_matches(route, pending) {
            return Err(SignedClientError::PendingMismatch(pending.kernel));
        }
        let result = SignedResult::decode(encoded_result).map_err(SignedClientError::Wire)?;
        result
            .verify(&pending.invocation, &route.recipient)
            .map_err(SignedClientError::Wire)?;
        let response =
            ServiceResponse::decode(result.payload()).map_err(SignedClientError::Codec)?;
        if response.operation() != pending.operation {
            return Err(SignedClientError::OperationMismatch {
                expected: pending.operation,
                actual: response.operation(),
            });
        }
        if result.output_id() != response.value_id() {
            return Err(SignedClientError::OutputIdentityMismatch);
        }
        Ok(response)
    }
}

fn pending_matches(route: &ClientRoute, pending: &PendingInvocation) -> bool {
    route.in_flight
        && route.next_sequence == Some(pending.invocation.sequence())
        && route.grant.caller() == pending.invocation.caller()
        && route.grant.recipient() == pending.invocation.recipient()
        && route.grant.channel() == pending.invocation.channel()
}

fn coordinates(grant: &ChannelGrant) -> ChannelCoordinates {
    ChannelCoordinates {
        caller: grant.caller(),
        recipient: grant.recipient(),
        channel: grant.channel(),
    }
}

struct NucleusStatementSigner<'a>(&'a covalence_nucleus::Ed25519Signer);

impl StatementSigner for NucleusStatementSigner<'_> {
    type Error = NucleusSignerAdapterError;

    fn public_key(&self) -> PublicKeyIdentity {
        *self.0.verifying_key().as_bytes()
    }

    fn sign_statement(&self, statement: covalence_lib_hash::O256) -> Result<[u8; 64], Self::Error> {
        use covalence_nucleus::Signer as _;

        self.0
            .sign(self.0.key_id(), statement)
            .map_err(NucleusSignerAdapterError::Sign)?
            .as_ref()
            .try_into()
            .map_err(|_| NucleusSignerAdapterError::InvalidLength)
    }
}

#[derive(Debug)]
enum NucleusSignerAdapterError {
    Sign(covalence_nucleus::SignError),
    InvalidLength,
}

/// Failure to establish or advance a signed kernel-client route.
#[derive(Debug)]
pub enum SignedClientError {
    /// A route already has one recipient-issued channel.
    RouteAlreadyExists(KernelId),
    /// No verified channel exists for this kernel.
    UnknownRoute(KernelId),
    /// The pinned bytes are not a valid Ed25519 verification key.
    InvalidRecipientKey,
    /// One request is already awaiting a result on this route.
    InvocationInFlight(KernelId),
    /// The route accepted sequence `u64::MAX` and cannot issue another invocation.
    SequenceExhausted(KernelId),
    /// The pending value does not name the route's exact outstanding invocation.
    PendingMismatch(KernelId),
    /// Canonical signed-frame syntax, context, or authentication failed.
    Wire(WireError),
    /// Canonical typed response payload decoding failed.
    Codec(RpcCodecError),
    /// A verified response carried another operation variant.
    OperationMismatch {
        /// Operation signed into the invocation schema.
        expected: Operation,
        /// Operation encoded by the response payload.
        actual: Operation,
    },
    /// A verified result's output ID did not name its exact typed response.
    OutputIdentityMismatch,
    /// Nucleus refused or failed controller signing.
    Signing(covalence_nucleus::SignError),
    /// A signing backend returned a non-Ed25519 signature length.
    InvalidSignatureLength,
}

impl SignedClientError {
    fn signing(error: MessageSigningError<NucleusSignerAdapterError>) -> Self {
        match error {
            MessageSigningError::Wire(error) => Self::Wire(error),
            MessageSigningError::Signer(NucleusSignerAdapterError::Sign(error)) => {
                Self::Signing(error)
            }
            MessageSigningError::Signer(NucleusSignerAdapterError::InvalidLength) => {
                Self::InvalidSignatureLength
            }
        }
    }
}

impl fmt::Display for SignedClientError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RouteAlreadyExists(kernel) => {
                write!(
                    formatter,
                    "kernel {kernel} already has a signed client route"
                )
            }
            Self::UnknownRoute(kernel) => write!(formatter, "kernel {kernel} has no signed route"),
            Self::InvalidRecipientKey => {
                formatter.write_str("invalid recipient Ed25519 public key")
            }
            Self::InvocationInFlight(kernel) => {
                write!(
                    formatter,
                    "kernel {kernel} already has an invocation in flight"
                )
            }
            Self::SequenceExhausted(kernel) => {
                write!(
                    formatter,
                    "kernel {kernel} signed route sequence is exhausted"
                )
            }
            Self::PendingMismatch(kernel) => {
                write!(
                    formatter,
                    "pending invocation does not match kernel {kernel} route"
                )
            }
            Self::Wire(error) => error.fmt(formatter),
            Self::Codec(error) => {
                write!(formatter, "invalid canonical service response: {error:?}")
            }
            Self::OperationMismatch { expected, actual } => write!(
                formatter,
                "signed response operation mismatch: expected {expected:?}, got {actual:?}"
            ),
            Self::OutputIdentityMismatch => {
                formatter.write_str("signed response output identity mismatch")
            }
            Self::Signing(error) => error.fmt(formatter),
            Self::InvalidSignatureLength => {
                formatter.write_str("signer returned a non-Ed25519 signature")
            }
        }
    }
}

impl StdError for SignedClientError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Wire(error) => Some(error),
            Self::Signing(error) => Some(error),
            Self::RouteAlreadyExists(_)
            | Self::UnknownRoute(_)
            | Self::InvalidRecipientKey
            | Self::InvocationInFlight(_)
            | Self::SequenceExhausted(_)
            | Self::PendingMismatch(_)
            | Self::Codec(_)
            | Self::OperationMismatch { .. }
            | Self::OutputIdentityMismatch
            | Self::InvalidSignatureLength => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_kernel_service::{ServiceError, SqlConnectionId};

    fn grant(
        client: &SignedKernelClient,
        recipient: &covalence_nucleus::Kernel,
        channel: u8,
        initial_sequence: u64,
    ) -> ChannelGrant {
        ChannelGrant::issue(
            &NucleusStatementSigner(recipient.signer()),
            client.caller_public_key(),
            ChannelNonce::new([channel; 32]),
            initial_sequence,
        )
        .unwrap()
    }

    fn install(
        client: &mut SignedKernelClient,
        kernel: KernelId,
        recipient: &covalence_nucleus::Kernel,
        channel: u8,
    ) {
        let grant = grant(client, recipient, channel, 0);
        client
            .accept_grant(
                kernel,
                *recipient.verifying_key().as_bytes(),
                &grant.encode(),
            )
            .unwrap();
    }

    fn result(
        pending: &PendingInvocation,
        recipient: &covalence_nucleus::Kernel,
        response: &ServiceResponse,
    ) -> Vec<u8> {
        SignedResult::sign(
            &pending.invocation,
            &NucleusStatementSigner(recipient.signer()),
            response.value_id(),
            response.encode(),
        )
        .unwrap()
        .encode()
    }

    #[test]
    fn verifies_grant_result_and_advances_only_after_acceptance() {
        let mut client = SignedKernelClient::ephemeral();
        let recipient = covalence_nucleus::Kernel::ephemeral();
        let kernel = KernelId::from_u32(7);
        install(&mut client, kernel, &recipient, 1);

        let pending = client.prepare(kernel, &ServiceRequest::Open).unwrap();
        assert_eq!(pending.sequence(), 0);
        assert!(matches!(
            client.prepare(kernel, &ServiceRequest::Open),
            Err(SignedClientError::InvocationInFlight(id)) if id == kernel
        ));
        let response = ServiceResponse::Open(Ok(SqlConnectionId::from_u64(9)));
        let encoded = result(&pending, &recipient, &response);
        assert_eq!(client.accept_result(pending, &encoded).unwrap(), response);

        let next = client.prepare(kernel, &ServiceRequest::Open).unwrap();
        assert_eq!(next.sequence(), 1);
    }

    #[test]
    fn rejects_wrong_grant_caller_and_does_not_install_route() {
        let mut client = SignedKernelClient::ephemeral();
        let recipient = covalence_nucleus::Kernel::ephemeral();
        let other = SignedKernelClient::ephemeral();
        let kernel = KernelId::from_u32(3);
        let wrong = ChannelGrant::issue(
            &NucleusStatementSigner(recipient.signer()),
            other.caller_public_key(),
            ChannelNonce::new([2; 32]),
            0,
        )
        .unwrap();
        assert!(matches!(
            client.accept_grant(
                kernel,
                *recipient.verifying_key().as_bytes(),
                &wrong.encode()
            ),
            Err(SignedClientError::Wire(WireError::ChannelMismatch))
        ));
        assert!(client.grant(kernel).is_none());
    }

    #[test]
    fn verified_response_mismatch_poisons_the_route() {
        let mut client = SignedKernelClient::ephemeral();
        let recipient = covalence_nucleus::Kernel::ephemeral();
        let kernel = KernelId::from_u32(4);
        install(&mut client, kernel, &recipient, 3);
        let pending = client.prepare(kernel, &ServiceRequest::Open).unwrap();
        let wrong = ServiceResponse::ListImages(Err(ServiceError::NotFound));
        let encoded = result(&pending, &recipient, &wrong);
        assert!(matches!(
            client.accept_result(pending, &encoded),
            Err(SignedClientError::OperationMismatch {
                expected: Operation::OpenSql,
                actual: Operation::ListImages
            })
        ));
        assert!(client.grant(kernel).is_none());
    }

    #[test]
    fn wrong_output_identity_and_tampering_poison_routes() {
        let recipient = covalence_nucleus::Kernel::ephemeral();
        let kernel = KernelId::from_u32(5);
        let mut client = SignedKernelClient::ephemeral();
        install(&mut client, kernel, &recipient, 4);
        let pending = client.prepare(kernel, &ServiceRequest::Open).unwrap();
        let response = ServiceResponse::Open(Ok(SqlConnectionId::from_u64(1)));
        let wrong_id = SignedResult::sign(
            &pending.invocation,
            &NucleusStatementSigner(recipient.signer()),
            covalence_lib_hash::O256::from_bytes(b"wrong output"),
            response.encode(),
        )
        .unwrap()
        .encode();
        assert!(matches!(
            client.accept_result(pending, &wrong_id),
            Err(SignedClientError::OutputIdentityMismatch)
        ));
        assert!(client.grant(kernel).is_none());

        install(&mut client, kernel, &recipient, 5);
        let pending = client.prepare(kernel, &ServiceRequest::Open).unwrap();
        let mut tampered = result(&pending, &recipient, &response);
        *tampered.last_mut().unwrap() ^= 1;
        assert!(matches!(
            client.accept_result(pending, &tampered),
            Err(SignedClientError::Wire(WireError::InvalidSignature))
        ));
        assert!(client.grant(kernel).is_none());
    }

    #[test]
    fn abandoning_pending_returns_revoke_coordinates() {
        let mut client = SignedKernelClient::ephemeral();
        let recipient = covalence_nucleus::Kernel::ephemeral();
        let kernel = KernelId::from_u32(6);
        install(&mut client, kernel, &recipient, 6);
        let expected = client.channel_coordinates(kernel).unwrap();
        let pending = client.prepare(kernel, &ServiceRequest::Open).unwrap();
        assert_eq!(client.abandon_pending(pending), Some(expected));
        assert!(client.grant(kernel).is_none());
    }
}
