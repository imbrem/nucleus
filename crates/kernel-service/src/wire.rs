//! Canonical, signed point-to-point kernel messages.
//!
//! This is a transport codec, not a Nucleus protocol and not a trust decision. A recipient must
//! separately decide which semantic schemas and public keys it accepts. The recipient issues a
//! fresh [`ChannelNonce`] and retains the corresponding [`InvocationChannel`] replay state.

use std::{convert::Infallible, error::Error as StdError, fmt};

use covalence_lib_crypto::ed25519::{Signature, Signer as _, SigningKey, VerifyingKey};
use covalence_lib_hash::{O256, o256_path};

/// Maximum payload carried by one signed kernel message.
///
/// The largest canonical service payload is a maximum-sized serialized image plus its 18-byte RPC
/// response prefix. The signed frame's own fixed fields are accounted for separately.
pub const MAX_WIRE_PAYLOAD_BYTES: usize = super::MAX_IMAGE_BYTES + 18;

const VERSION: u8 = 0;
const RESERVED_BYTES: [u8; 3] = [0; 3];
const SIGNATURE_BYTES: usize = 64;
const LENGTH_BYTES: usize = 4;
const INVOCATION_MAGIC: [u8; 8] = *b"COVKINVK";
const RESULT_MAGIC: [u8; 8] = *b"COVKRESL";
const CHANNEL_GRANT_MAGIC: [u8; 8] = *b"COVKCHNL";
const CHANNEL_GRANT_BYTES: usize = 8 + 1 + 3 + 32 * 3 + 8 + SIGNATURE_BYTES;
const INVOCATION_FIXED_BYTES: usize = 8 + 1 + 3 + 32 * 6 + 8 + LENGTH_BYTES + SIGNATURE_BYTES;
const RESULT_FIXED_BYTES: usize = 8 + 1 + 3 + 32 * 7 + 8 + LENGTH_BYTES + SIGNATURE_BYTES;

/// Raw Ed25519 verification-key bytes used as an endpoint identity.
pub type PublicKeyIdentity = [u8; 32];

/// Capability to sign one already-domain-separated O256 statement.
///
/// Implementations own or proxy the secret material. Callers of this trait receive only the
/// public verification-key identity and an exact Ed25519 signature. In particular, a kernel can
/// adapt its private Nucleus signer without exposing its [`SigningKey`] or making this crate depend
/// on Nucleus.
pub trait StatementSigner {
    /// Backend-specific signing failure.
    type Error;

    /// Public verification-key bytes identifying this signing capability.
    fn public_key(&self) -> PublicKeyIdentity;

    /// Signs the exact O256 statement bytes.
    ///
    /// # Errors
    ///
    /// Returns the backend's precise failure without producing a partial frame.
    fn sign_statement(&self, statement: O256) -> Result<[u8; SIGNATURE_BYTES], Self::Error>;
}

impl StatementSigner for SigningKey {
    type Error = Infallible;

    fn public_key(&self) -> PublicKeyIdentity {
        *self.verifying_key().as_bytes()
    }

    fn sign_statement(&self, statement: O256) -> Result<[u8; SIGNATURE_BYTES], Self::Error> {
        Ok(self.sign(statement.as_ref()).to_bytes())
    }
}

/// Recipient-issued unpredictable channel identity.
///
/// Channel issuance and entropy are responsibilities of the recipient. The codec treats these
/// bytes as an opaque identity and commits them to every signed statement.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ChannelNonce([u8; 32]);

impl ChannelNonce {
    /// Wraps exact recipient-issued nonce bytes.
    #[must_use]
    pub const fn new(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }

    /// Returns the exact nonce bytes.
    #[must_use]
    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
}

/// Domain root for v0 signed kernel invocations.
#[must_use]
pub fn invocation_domain() -> O256 {
    o256_path!(::nucleus.kernel.invoke.v0)
}

/// Domain root for v0 signed kernel results.
#[must_use]
pub fn result_domain() -> O256 {
    o256_path!(::nucleus.kernel.result.v0)
}

/// Domain root for v0 recipient-issued channel grants.
#[must_use]
pub fn channel_grant_domain() -> O256 {
    o256_path!(::nucleus.kernel.channel.v0)
}

/// A recipient-signed grant binding one caller to a fresh replay channel.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ChannelGrant {
    caller: PublicKeyIdentity,
    recipient: PublicKeyIdentity,
    channel: ChannelNonce,
    initial_sequence: u64,
    signature: [u8; SIGNATURE_BYTES],
}

impl ChannelGrant {
    /// Issues a channel grant signed by the recipient.
    ///
    /// The caller identity is not trusted merely because it is named here. Every invocation on
    /// the granted channel must still carry a valid signature from that exact caller key.
    ///
    /// # Errors
    ///
    /// Returns the recipient signing capability's precise failure.
    pub fn issue<S: StatementSigner + ?Sized>(
        recipient: &S,
        caller: PublicKeyIdentity,
        channel: ChannelNonce,
        initial_sequence: u64,
    ) -> Result<Self, MessageSigningError<S::Error>> {
        let recipient_identity = recipient.public_key();
        let signature = recipient
            .sign_statement(channel_grant_statement(
                &caller,
                &recipient_identity,
                channel,
                initial_sequence,
            ))
            .map_err(MessageSigningError::Signer)?;
        Ok(Self {
            caller,
            recipient: recipient_identity,
            channel,
            initial_sequence,
            signature,
        })
    }

    /// Decodes one exact canonical channel-grant frame without authenticating it.
    ///
    /// # Errors
    ///
    /// Returns a precise wire error for malformed or non-canonical input.
    pub fn decode(bytes: &[u8]) -> Result<Self, WireError> {
        if bytes.len() < CHANNEL_GRANT_BYTES {
            return Err(WireError::Truncated);
        }
        if bytes.len() != CHANNEL_GRANT_BYTES {
            return Err(WireError::InvalidLength);
        }
        let mut cursor = Cursor::new(bytes);
        cursor.expect(&CHANNEL_GRANT_MAGIC)?;
        cursor.version_and_reserved()?;
        let caller = cursor.array()?;
        let recipient = cursor.array()?;
        let channel = ChannelNonce(cursor.array()?);
        let initial_sequence = cursor.u64()?;
        let signature = cursor.array()?;
        debug_assert!(cursor.is_empty());
        Ok(Self {
            caller,
            recipient,
            channel,
            initial_sequence,
            signature,
        })
    }

    /// Encodes the unique v0 frame representation.
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(CHANNEL_GRANT_BYTES);
        bytes.extend_from_slice(&CHANNEL_GRANT_MAGIC);
        bytes.push(VERSION);
        bytes.extend_from_slice(&RESERVED_BYTES);
        bytes.extend_from_slice(&self.caller);
        bytes.extend_from_slice(&self.recipient);
        bytes.extend_from_slice(self.channel.as_bytes());
        bytes.extend_from_slice(&self.initial_sequence.to_be_bytes());
        bytes.extend_from_slice(&self.signature);
        bytes
    }

    /// Verifies the recipient signature and the expected caller identity.
    ///
    /// # Errors
    ///
    /// Returns a public-key, channel-context, or signature error.
    pub fn verify(
        &self,
        caller: PublicKeyIdentity,
        recipient: &VerifyingKey,
    ) -> Result<(), WireError> {
        if self.caller != caller {
            return Err(WireError::ChannelMismatch);
        }
        if recipient.as_bytes() != &self.recipient {
            return Err(WireError::PublicKeyMismatch);
        }
        recipient
            .verify_strict(
                self.statement().as_ref(),
                &Signature::from_bytes(&self.signature),
            )
            .map_err(|_| WireError::InvalidSignature)
    }

    /// Returns the exact statement signed by the recipient.
    #[must_use]
    pub fn statement(&self) -> O256 {
        channel_grant_statement(
            &self.caller,
            &self.recipient,
            self.channel,
            self.initial_sequence,
        )
    }

    /// Caller authorized to authenticate invocations on this channel.
    #[must_use]
    pub const fn caller(&self) -> PublicKeyIdentity {
        self.caller
    }

    /// Recipient which issued and signed this channel.
    #[must_use]
    pub const fn recipient(&self) -> PublicKeyIdentity {
        self.recipient
    }

    /// Fresh recipient-issued channel nonce.
    #[must_use]
    pub const fn channel(&self) -> ChannelNonce {
        self.channel
    }

    /// First sequence accepted by the channel.
    #[must_use]
    pub const fn initial_sequence(&self) -> u64 {
        self.initial_sequence
    }
}

/// A bounded canonical invocation signed by its caller.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SignedInvocation {
    schema: O256,
    caller: PublicKeyIdentity,
    recipient: PublicKeyIdentity,
    channel: ChannelNonce,
    sequence: u64,
    input_id: O256,
    payload_hash: O256,
    payload: Vec<u8>,
    signature: [u8; SIGNATURE_BYTES],
}

impl SignedInvocation {
    /// Constructs and signs a canonical invocation.
    ///
    /// # Errors
    ///
    /// Returns [`WireError::PayloadTooLarge`] before hashing or copying an oversized payload.
    pub fn sign<S: StatementSigner + ?Sized>(
        schema: O256,
        caller: &S,
        recipient: PublicKeyIdentity,
        channel: ChannelNonce,
        sequence: u64,
        input_id: O256,
        payload: Vec<u8>,
    ) -> Result<Self, MessageSigningError<S::Error>> {
        check_payload_len(payload.len()).map_err(MessageSigningError::Wire)?;
        let caller_identity = caller.public_key();
        let payload_hash = O256::from_bytes(&payload);
        let statement = invocation_statement(
            schema,
            &caller_identity,
            &recipient,
            channel,
            sequence,
            input_id,
            payload_hash,
            payload.len(),
        );
        let signature = caller
            .sign_statement(statement)
            .map_err(MessageSigningError::Signer)?;
        Ok(Self {
            schema,
            caller: caller_identity,
            recipient,
            channel,
            sequence,
            input_id,
            payload_hash,
            payload,
            signature,
        })
    }

    /// Decodes one exact canonical invocation frame.
    ///
    /// This checks syntax, resource bounds, and the encoded payload hash, but does not authenticate
    /// the caller or apply replay state. Use [`Self::verify_signature`] or
    /// [`InvocationChannel::verify`] for authentication.
    ///
    /// # Errors
    ///
    /// Returns a precise [`WireError`] for malformed, non-canonical, or oversized input.
    pub fn decode(bytes: &[u8]) -> Result<Self, WireError> {
        let payload_len = frame_payload_len(bytes, INVOCATION_FIXED_BYTES, INVOCATION_MAGIC)?;
        let mut cursor = Cursor::new(bytes);
        cursor.expect(&INVOCATION_MAGIC)?;
        cursor.version_and_reserved()?;
        let schema = cursor.o256()?;
        let caller = cursor.array()?;
        let recipient = cursor.array()?;
        let channel = ChannelNonce(cursor.array()?);
        let sequence = cursor.u64()?;
        let input_id = cursor.o256()?;
        let payload_hash = cursor.o256()?;
        let encoded_len = cursor.u32()? as usize;
        if encoded_len != payload_len {
            return Err(WireError::InvalidLength);
        }
        let payload = cursor.take(payload_len)?.to_vec();
        let signature = cursor.array()?;
        if !cursor.is_empty() {
            return Err(WireError::InvalidLength);
        }
        if O256::from_bytes(&payload) != payload_hash {
            return Err(WireError::PayloadHashMismatch);
        }
        Ok(Self {
            schema,
            caller,
            recipient,
            channel,
            sequence,
            input_id,
            payload_hash,
            payload,
            signature,
        })
    }

    /// Encodes the unique v0 frame representation.
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(INVOCATION_FIXED_BYTES + self.payload.len());
        bytes.extend_from_slice(&INVOCATION_MAGIC);
        bytes.push(VERSION);
        bytes.extend_from_slice(&RESERVED_BYTES);
        bytes.extend_from_slice(self.schema.as_ref());
        bytes.extend_from_slice(&self.caller);
        bytes.extend_from_slice(&self.recipient);
        bytes.extend_from_slice(self.channel.as_bytes());
        bytes.extend_from_slice(&self.sequence.to_be_bytes());
        bytes.extend_from_slice(self.input_id.as_ref());
        bytes.extend_from_slice(self.payload_hash.as_ref());
        bytes.extend_from_slice(&payload_len_u32(self.payload.len()).to_be_bytes());
        bytes.extend_from_slice(&self.payload);
        bytes.extend_from_slice(&self.signature);
        bytes
    }

    /// Verifies that the supplied key is the encoded caller and signed the canonical statement.
    ///
    /// # Errors
    ///
    /// Returns [`WireError::PublicKeyMismatch`] or [`WireError::InvalidSignature`] on failure.
    pub fn verify_signature(&self, caller: &VerifyingKey) -> Result<(), WireError> {
        if caller.as_bytes() != &self.caller {
            return Err(WireError::PublicKeyMismatch);
        }
        caller
            .verify_strict(
                self.statement().as_ref(),
                &Signature::from_bytes(&self.signature),
            )
            .map_err(|_| WireError::InvalidSignature)
    }

    /// Returns the exact O256 statement signed by the caller.
    #[must_use]
    pub fn statement(&self) -> O256 {
        invocation_statement(
            self.schema,
            &self.caller,
            &self.recipient,
            self.channel,
            self.sequence,
            self.input_id,
            self.payload_hash,
            self.payload.len(),
        )
    }

    /// Semantic schema governing this input claim.
    #[must_use]
    pub const fn schema(&self) -> O256 {
        self.schema
    }

    /// Caller verification-key identity.
    #[must_use]
    pub const fn caller(&self) -> PublicKeyIdentity {
        self.caller
    }

    /// Intended recipient verification-key identity.
    #[must_use]
    pub const fn recipient(&self) -> PublicKeyIdentity {
        self.recipient
    }

    /// Recipient-issued channel nonce.
    #[must_use]
    pub const fn channel(&self) -> ChannelNonce {
        self.channel
    }

    /// Exact monotonic sequence number within the channel.
    #[must_use]
    pub const fn sequence(&self) -> u64 {
        self.sequence
    }

    /// Semantic identity of the input value.
    #[must_use]
    pub const fn input_id(&self) -> O256 {
        self.input_id
    }

    /// Hash of the exact payload bytes.
    #[must_use]
    pub const fn payload_hash(&self) -> O256 {
        self.payload_hash
    }

    /// Exact bounded input bytes.
    #[must_use]
    pub fn payload(&self) -> &[u8] {
        &self.payload
    }
}

/// A bounded canonical result signed by the invocation recipient.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SignedResult {
    schema: O256,
    caller: PublicKeyIdentity,
    executor: PublicKeyIdentity,
    channel: ChannelNonce,
    sequence: u64,
    invocation: O256,
    output_id: O256,
    payload_hash: O256,
    payload: Vec<u8>,
    signature: [u8; SIGNATURE_BYTES],
}

impl SignedResult {
    /// Constructs a result bound to an authenticated invocation statement.
    ///
    /// # Errors
    ///
    /// Rejects an executor other than the invocation recipient and an oversized payload.
    pub fn sign<S: StatementSigner + ?Sized>(
        invocation: &SignedInvocation,
        executor: &S,
        output_id: O256,
        payload: Vec<u8>,
    ) -> Result<Self, MessageSigningError<S::Error>> {
        check_payload_len(payload.len()).map_err(MessageSigningError::Wire)?;
        let executor_identity = executor.public_key();
        if executor_identity != invocation.recipient {
            return Err(MessageSigningError::Wire(WireError::PublicKeyMismatch));
        }
        let invocation_statement = invocation.statement();
        let payload_hash = O256::from_bytes(&payload);
        let statement = result_statement(
            invocation.schema,
            &invocation.caller,
            &executor_identity,
            invocation.channel,
            invocation.sequence,
            invocation_statement,
            output_id,
            payload_hash,
            payload.len(),
        );
        let signature = executor
            .sign_statement(statement)
            .map_err(MessageSigningError::Signer)?;
        Ok(Self {
            schema: invocation.schema,
            caller: invocation.caller,
            executor: executor_identity,
            channel: invocation.channel,
            sequence: invocation.sequence,
            invocation: invocation_statement,
            output_id,
            payload_hash,
            payload,
            signature,
        })
    }

    /// Decodes one exact canonical result frame without authenticating it.
    ///
    /// # Errors
    ///
    /// Returns a precise [`WireError`] for malformed, non-canonical, or oversized input.
    pub fn decode(bytes: &[u8]) -> Result<Self, WireError> {
        let payload_len = frame_payload_len(bytes, RESULT_FIXED_BYTES, RESULT_MAGIC)?;
        let mut cursor = Cursor::new(bytes);
        cursor.expect(&RESULT_MAGIC)?;
        cursor.version_and_reserved()?;
        let schema = cursor.o256()?;
        let caller = cursor.array()?;
        let executor = cursor.array()?;
        let channel = ChannelNonce(cursor.array()?);
        let sequence = cursor.u64()?;
        let invocation = cursor.o256()?;
        let output_id = cursor.o256()?;
        let payload_hash = cursor.o256()?;
        let encoded_len = cursor.u32()? as usize;
        if encoded_len != payload_len {
            return Err(WireError::InvalidLength);
        }
        let payload = cursor.take(payload_len)?.to_vec();
        let signature = cursor.array()?;
        if !cursor.is_empty() {
            return Err(WireError::InvalidLength);
        }
        if O256::from_bytes(&payload) != payload_hash {
            return Err(WireError::PayloadHashMismatch);
        }
        Ok(Self {
            schema,
            caller,
            executor,
            channel,
            sequence,
            invocation,
            output_id,
            payload_hash,
            payload,
            signature,
        })
    }

    /// Encodes the unique v0 frame representation.
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(RESULT_FIXED_BYTES + self.payload.len());
        bytes.extend_from_slice(&RESULT_MAGIC);
        bytes.push(VERSION);
        bytes.extend_from_slice(&RESERVED_BYTES);
        bytes.extend_from_slice(self.schema.as_ref());
        bytes.extend_from_slice(&self.caller);
        bytes.extend_from_slice(&self.executor);
        bytes.extend_from_slice(self.channel.as_bytes());
        bytes.extend_from_slice(&self.sequence.to_be_bytes());
        bytes.extend_from_slice(self.invocation.as_ref());
        bytes.extend_from_slice(self.output_id.as_ref());
        bytes.extend_from_slice(self.payload_hash.as_ref());
        bytes.extend_from_slice(&payload_len_u32(self.payload.len()).to_be_bytes());
        bytes.extend_from_slice(&self.payload);
        bytes.extend_from_slice(&self.signature);
        bytes
    }

    /// Verifies the executor signature and every field copied from `invocation`.
    ///
    /// The caller must already have authenticated `invocation`; binding a result to an
    /// unauthenticated invocation does not authenticate the invocation's caller.
    ///
    /// # Errors
    ///
    /// Returns [`WireError::InvocationMismatch`], [`WireError::PublicKeyMismatch`], or
    /// [`WireError::InvalidSignature`] on failure.
    pub fn verify(
        &self,
        invocation: &SignedInvocation,
        executor: &VerifyingKey,
    ) -> Result<(), WireError> {
        if self.schema != invocation.schema
            || self.caller != invocation.caller
            || self.executor != invocation.recipient
            || self.channel != invocation.channel
            || self.sequence != invocation.sequence
            || self.invocation != invocation.statement()
        {
            return Err(WireError::InvocationMismatch);
        }
        if executor.as_bytes() != &self.executor {
            return Err(WireError::PublicKeyMismatch);
        }
        executor
            .verify_strict(
                self.statement().as_ref(),
                &Signature::from_bytes(&self.signature),
            )
            .map_err(|_| WireError::InvalidSignature)
    }

    /// Returns the exact O256 statement signed by the executor.
    #[must_use]
    pub fn statement(&self) -> O256 {
        result_statement(
            self.schema,
            &self.caller,
            &self.executor,
            self.channel,
            self.sequence,
            self.invocation,
            self.output_id,
            self.payload_hash,
            self.payload.len(),
        )
    }

    /// Semantic identity of the output value.
    #[must_use]
    pub const fn output_id(&self) -> O256 {
        self.output_id
    }

    /// Hash of the exact payload bytes.
    #[must_use]
    pub const fn payload_hash(&self) -> O256 {
        self.payload_hash
    }

    /// Exact bounded output bytes.
    #[must_use]
    pub fn payload(&self) -> &[u8] {
        &self.payload
    }
}

/// Recipient-owned replay state for one caller and issued channel.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InvocationChannel {
    caller: PublicKeyIdentity,
    recipient: PublicKeyIdentity,
    channel: ChannelNonce,
    next_sequence: Option<u64>,
}

impl InvocationChannel {
    /// Creates recipient-side state for an issued channel and its first accepted sequence.
    #[must_use]
    pub const fn new(
        caller: PublicKeyIdentity,
        recipient: PublicKeyIdentity,
        channel: ChannelNonce,
        initial_sequence: u64,
    ) -> Self {
        Self {
            caller,
            recipient,
            channel,
            next_sequence: Some(initial_sequence),
        }
    }

    /// Authenticates and consumes exactly the next sequence number.
    ///
    /// State advances only after all context and signature checks succeed. Sequence `u64::MAX` is
    /// accepted once and then exhausts the channel.
    ///
    /// # Errors
    ///
    /// Returns a context, sequence, exhaustion, public-key, or signature error without advancing.
    pub fn verify(
        &mut self,
        invocation: &SignedInvocation,
        caller: &VerifyingKey,
    ) -> Result<(), WireError> {
        if invocation.caller != self.caller
            || invocation.recipient != self.recipient
            || invocation.channel != self.channel
        {
            return Err(WireError::ChannelMismatch);
        }
        let Some(expected) = self.next_sequence else {
            return Err(WireError::SequenceExhausted);
        };
        if invocation.sequence != expected {
            return Err(WireError::UnexpectedSequence {
                expected,
                actual: invocation.sequence,
            });
        }
        invocation.verify_signature(caller)?;
        self.next_sequence = expected.checked_add(1);
        Ok(())
    }

    /// Returns the next required sequence, or `None` after accepting `u64::MAX`.
    #[must_use]
    pub const fn next_sequence(&self) -> Option<u64> {
        self.next_sequence
    }
}

#[allow(clippy::too_many_arguments)]
fn invocation_statement(
    schema: O256,
    caller: &PublicKeyIdentity,
    recipient: &PublicKeyIdentity,
    channel: ChannelNonce,
    sequence: u64,
    input_id: O256,
    payload_hash: O256,
    payload_len: usize,
) -> O256 {
    let mut fields = Vec::with_capacity(32 * 6 + 8 + LENGTH_BYTES);
    fields.extend_from_slice(schema.as_ref());
    fields.extend_from_slice(caller);
    fields.extend_from_slice(recipient);
    fields.extend_from_slice(channel.as_bytes());
    fields.extend_from_slice(&sequence.to_be_bytes());
    fields.extend_from_slice(input_id.as_ref());
    fields.extend_from_slice(payload_hash.as_ref());
    fields.extend_from_slice(&payload_len_u32(payload_len).to_be_bytes());
    invocation_domain().tag(fields)
}

#[allow(clippy::too_many_arguments)]
fn result_statement(
    schema: O256,
    caller: &PublicKeyIdentity,
    executor: &PublicKeyIdentity,
    channel: ChannelNonce,
    sequence: u64,
    invocation: O256,
    output_id: O256,
    payload_hash: O256,
    payload_len: usize,
) -> O256 {
    let mut fields = Vec::with_capacity(32 * 7 + 8 + LENGTH_BYTES);
    fields.extend_from_slice(schema.as_ref());
    fields.extend_from_slice(caller);
    fields.extend_from_slice(executor);
    fields.extend_from_slice(channel.as_bytes());
    fields.extend_from_slice(&sequence.to_be_bytes());
    fields.extend_from_slice(invocation.as_ref());
    fields.extend_from_slice(output_id.as_ref());
    fields.extend_from_slice(payload_hash.as_ref());
    fields.extend_from_slice(&payload_len_u32(payload_len).to_be_bytes());
    result_domain().tag(fields)
}

fn channel_grant_statement(
    caller: &PublicKeyIdentity,
    recipient: &PublicKeyIdentity,
    channel: ChannelNonce,
    initial_sequence: u64,
) -> O256 {
    let mut fields = Vec::with_capacity(32 * 3 + 8);
    fields.extend_from_slice(caller);
    fields.extend_from_slice(recipient);
    fields.extend_from_slice(channel.as_bytes());
    fields.extend_from_slice(&initial_sequence.to_be_bytes());
    channel_grant_domain().tag(fields)
}

fn check_payload_len(len: usize) -> Result<(), WireError> {
    if len > MAX_WIRE_PAYLOAD_BYTES || u32::try_from(len).is_err() {
        return Err(WireError::PayloadTooLarge);
    }
    Ok(())
}

fn payload_len_u32(len: usize) -> u32 {
    u32::try_from(len).expect("checked payload length")
}

fn frame_payload_len(bytes: &[u8], fixed: usize, magic: [u8; 8]) -> Result<usize, WireError> {
    if bytes.len() < 8 {
        return Err(WireError::Truncated);
    }
    if bytes[..8] != magic {
        return Err(WireError::InvalidMagic);
    }
    if bytes.len() < fixed {
        return Err(WireError::Truncated);
    }
    let payload_len = bytes.len() - fixed;
    check_payload_len(payload_len)?;
    Ok(payload_len)
}

struct Cursor<'a> {
    remaining: &'a [u8],
}

impl<'a> Cursor<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { remaining: bytes }
    }

    fn take(&mut self, len: usize) -> Result<&'a [u8], WireError> {
        let Some((value, remaining)) = self.remaining.split_at_checked(len) else {
            return Err(WireError::Truncated);
        };
        self.remaining = remaining;
        Ok(value)
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], WireError> {
        self.take(N)?.try_into().map_err(|_| WireError::Truncated)
    }

    fn expect(&mut self, expected: &[u8]) -> Result<(), WireError> {
        if self.take(expected.len())? != expected {
            return Err(WireError::InvalidMagic);
        }
        Ok(())
    }

    fn version_and_reserved(&mut self) -> Result<(), WireError> {
        if self.take(1)?[0] != VERSION {
            return Err(WireError::UnsupportedVersion);
        }
        if self.take(RESERVED_BYTES.len())? != RESERVED_BYTES {
            return Err(WireError::NonzeroReserved);
        }
        Ok(())
    }

    fn u32(&mut self) -> Result<u32, WireError> {
        Ok(u32::from_be_bytes(self.array()?))
    }

    fn u64(&mut self) -> Result<u64, WireError> {
        Ok(u64::from_be_bytes(self.array()?))
    }

    fn o256(&mut self) -> Result<O256, WireError> {
        Ok(O256::from_array(self.array()?))
    }

    const fn is_empty(&self) -> bool {
        self.remaining.is_empty()
    }
}

/// Rejected signed-wire syntax, authentication, context, or replay state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WireError {
    /// The frame ends before its declared fixed or variable fields.
    Truncated,
    /// The frame has the wrong message-kind magic.
    InvalidMagic,
    /// The frame version is not implemented.
    UnsupportedVersion,
    /// Reserved framing bytes are not canonical zeroes.
    NonzeroReserved,
    /// The encoded or physical frame length is inconsistent.
    InvalidLength,
    /// The payload exceeds [`MAX_WIRE_PAYLOAD_BYTES`].
    PayloadTooLarge,
    /// The encoded hash does not name the exact payload bytes.
    PayloadHashMismatch,
    /// A signing or verification key does not match the encoded endpoint identity.
    PublicKeyMismatch,
    /// The Ed25519 signature does not authenticate the canonical statement.
    InvalidSignature,
    /// The result is not bound to the supplied invocation.
    InvocationMismatch,
    /// The invocation is for a different caller, recipient, or channel.
    ChannelMismatch,
    /// The invocation did not carry the channel's exact next sequence.
    UnexpectedSequence {
        /// Required next sequence.
        expected: u64,
        /// Sequence carried by the invocation.
        actual: u64,
    },
    /// The channel already accepted sequence `u64::MAX`.
    SequenceExhausted,
}

impl fmt::Display for WireError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Truncated => formatter.write_str("truncated signed kernel frame"),
            Self::InvalidMagic => formatter.write_str("invalid signed kernel frame magic"),
            Self::UnsupportedVersion => {
                formatter.write_str("unsupported signed kernel frame version")
            }
            Self::NonzeroReserved => {
                formatter.write_str("nonzero reserved signed kernel frame bytes")
            }
            Self::InvalidLength => formatter.write_str("invalid signed kernel frame length"),
            Self::PayloadTooLarge => formatter.write_str("signed kernel payload exceeds its limit"),
            Self::PayloadHashMismatch => formatter.write_str("signed kernel payload hash mismatch"),
            Self::PublicKeyMismatch => formatter.write_str("signed kernel public key mismatch"),
            Self::InvalidSignature => formatter.write_str("invalid signed kernel signature"),
            Self::InvocationMismatch => {
                formatter.write_str("kernel result does not match invocation")
            }
            Self::ChannelMismatch => formatter.write_str("kernel invocation channel mismatch"),
            Self::UnexpectedSequence { expected, actual } => {
                write!(
                    formatter,
                    "expected kernel sequence {expected}, got {actual}"
                )
            }
            Self::SequenceExhausted => formatter.write_str("signed kernel channel is exhausted"),
        }
    }
}

impl StdError for WireError {}

/// Failure while constructing a signed message.
#[derive(Debug)]
pub enum MessageSigningError<E> {
    /// The proposed message violates a codec invariant or resource bound.
    Wire(WireError),
    /// The signing capability failed without exposing secret material.
    Signer(E),
}

impl<E: fmt::Display> fmt::Display for MessageSigningError<E> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Wire(error) => error.fmt(formatter),
            Self::Signer(error) => write!(formatter, "kernel statement signing failed: {error}"),
        }
    }
}

impl<E: StdError + 'static> StdError for MessageSigningError<E> {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Wire(error) => Some(error),
            Self::Signer(error) => Some(error),
        }
    }
}

#[cfg(test)]
mod tests {
    use covalence_lib_hash::assert_o256_path;

    use super::*;

    fn fixture() -> (SigningKey, SigningKey, SignedInvocation) {
        let caller = SigningKey::from_bytes(&[7; 32]);
        let executor = SigningKey::from_bytes(&[9; 32]);
        let invocation = SignedInvocation::sign(
            O256::from_bytes(b"schema"),
            &caller,
            *executor.verifying_key().as_bytes(),
            ChannelNonce::new([0xa5; 32]),
            42,
            O256::from_bytes(b"input id"),
            b"input".to_vec(),
        )
        .unwrap();
        (caller, executor, invocation)
    }

    #[test]
    fn domains_are_fixed_named_roots() {
        assert_o256_path!(invocation_domain(), ::nucleus.kernel.invoke.v0);
        assert_o256_path!(result_domain(), ::nucleus.kernel.result.v0);
        assert_o256_path!(channel_grant_domain(), ::nucleus.kernel.channel.v0);
        assert_ne!(invocation_domain(), result_domain());
        assert_ne!(channel_grant_domain(), invocation_domain());
    }

    #[test]
    fn recipient_signed_channel_grant_round_trips_and_authenticates() {
        let caller = SigningKey::from_bytes(&[7; 32]);
        let recipient = SigningKey::from_bytes(&[9; 32]);
        let grant = ChannelGrant::issue(
            &recipient,
            *caller.verifying_key().as_bytes(),
            ChannelNonce::new([0x35; 32]),
            17,
        )
        .unwrap();
        let decoded = ChannelGrant::decode(&grant.encode()).unwrap();
        assert_eq!(decoded, grant);
        decoded
            .verify(
                *caller.verifying_key().as_bytes(),
                &recipient.verifying_key(),
            )
            .unwrap();

        let wrong_caller = SigningKey::from_bytes(&[11; 32]);
        assert_eq!(
            decoded.verify(
                *wrong_caller.verifying_key().as_bytes(),
                &recipient.verifying_key(),
            ),
            Err(WireError::ChannelMismatch)
        );
        let mut tampered = decoded.encode();
        *tampered.last_mut().unwrap() ^= 1;
        assert_eq!(
            ChannelGrant::decode(&tampered).unwrap().verify(
                *caller.verifying_key().as_bytes(),
                &recipient.verifying_key(),
            ),
            Err(WireError::InvalidSignature)
        );
    }

    #[test]
    fn invocation_and_result_round_trip_and_authenticate() {
        let (caller, executor, invocation) = fixture();
        let decoded = SignedInvocation::decode(&invocation.encode()).unwrap();
        assert_eq!(decoded, invocation);
        decoded.verify_signature(&caller.verifying_key()).unwrap();

        let result = SignedResult::sign(
            &decoded,
            &executor,
            O256::from_bytes(b"output id"),
            b"output".to_vec(),
        )
        .unwrap();
        let decoded_result = SignedResult::decode(&result.encode()).unwrap();
        assert_eq!(decoded_result, result);
        decoded_result
            .verify(&decoded, &executor.verifying_key())
            .unwrap();
    }

    #[test]
    fn channel_rejects_replay_gap_and_wrong_context_without_advancing() {
        let (caller, executor, invocation) = fixture();
        let mut channel = InvocationChannel::new(
            invocation.caller(),
            invocation.recipient(),
            invocation.channel(),
            42,
        );
        channel
            .verify(&invocation, &caller.verifying_key())
            .unwrap();
        assert_eq!(channel.next_sequence(), Some(43));
        assert!(matches!(
            channel.verify(&invocation, &caller.verifying_key()),
            Err(WireError::UnexpectedSequence {
                expected: 43,
                actual: 42
            })
        ));

        let gap = SignedInvocation::sign(
            invocation.schema(),
            &caller,
            *executor.verifying_key().as_bytes(),
            invocation.channel(),
            44,
            invocation.input_id(),
            invocation.payload().to_vec(),
        )
        .unwrap();
        assert!(matches!(
            channel.verify(&gap, &caller.verifying_key()),
            Err(WireError::UnexpectedSequence {
                expected: 43,
                actual: 44
            })
        ));
        assert_eq!(channel.next_sequence(), Some(43));

        let wrong_channel = SignedInvocation::sign(
            invocation.schema(),
            &caller,
            *executor.verifying_key().as_bytes(),
            ChannelNonce::new([0x5a; 32]),
            43,
            invocation.input_id(),
            invocation.payload().to_vec(),
        )
        .unwrap();
        assert_eq!(
            channel.verify(&wrong_channel, &caller.verifying_key()),
            Err(WireError::ChannelMismatch)
        );
        assert_eq!(channel.next_sequence(), Some(43));

        let next = SignedInvocation::sign(
            invocation.schema(),
            &caller,
            *executor.verifying_key().as_bytes(),
            invocation.channel(),
            43,
            invocation.input_id(),
            invocation.payload().to_vec(),
        )
        .unwrap();
        channel.verify(&next, &caller.verifying_key()).unwrap();
        assert_eq!(channel.next_sequence(), Some(44));
    }

    #[test]
    fn channel_accepts_max_sequence_once_then_exhausts() {
        let (caller, _, invocation) = fixture();
        let invocation = SignedInvocation::sign(
            invocation.schema(),
            &caller,
            invocation.recipient(),
            invocation.channel(),
            u64::MAX,
            invocation.input_id(),
            invocation.payload().to_vec(),
        )
        .unwrap();
        let mut channel = InvocationChannel::new(
            invocation.caller(),
            invocation.recipient(),
            invocation.channel(),
            u64::MAX,
        );
        channel
            .verify(&invocation, &caller.verifying_key())
            .unwrap();
        assert_eq!(channel.next_sequence(), None);
        assert_eq!(
            channel.verify(&invocation, &caller.verifying_key()),
            Err(WireError::SequenceExhausted)
        );
    }

    #[test]
    fn malformed_and_tampered_invocations_are_rejected() {
        let (caller, _, invocation) = fixture();
        let encoded = invocation.encode();
        for end in 0..encoded.len() {
            assert!(SignedInvocation::decode(&encoded[..end]).is_err());
        }

        let mut bad_magic = encoded.clone();
        bad_magic[0] ^= 1;
        assert_eq!(
            SignedInvocation::decode(&bad_magic),
            Err(WireError::InvalidMagic)
        );
        let mut bad_version = encoded.clone();
        bad_version[8] = 1;
        assert_eq!(
            SignedInvocation::decode(&bad_version),
            Err(WireError::UnsupportedVersion)
        );
        let mut bad_reserved = encoded.clone();
        bad_reserved[9] = 1;
        assert_eq!(
            SignedInvocation::decode(&bad_reserved),
            Err(WireError::NonzeroReserved)
        );
        let mut bad_hash = encoded.clone();
        let payload_offset = INVOCATION_FIXED_BYTES - SIGNATURE_BYTES;
        bad_hash[payload_offset] ^= 1;
        assert_eq!(
            SignedInvocation::decode(&bad_hash),
            Err(WireError::PayloadHashMismatch)
        );
        let mut trailing = encoded.clone();
        trailing.push(0);
        assert_eq!(
            SignedInvocation::decode(&trailing),
            Err(WireError::InvalidLength)
        );

        let mut bad_signature = invocation.clone();
        bad_signature.signature[0] ^= 1;
        assert_eq!(
            bad_signature.verify_signature(&caller.verifying_key()),
            Err(WireError::InvalidSignature)
        );
    }

    #[test]
    fn results_are_bound_to_invocation_and_executor() {
        let (caller, executor, invocation) = fixture();
        let result = SignedResult::sign(
            &invocation,
            &executor,
            O256::from_bytes(b"output id"),
            b"output".to_vec(),
        )
        .unwrap();
        let other = SignedInvocation::sign(
            invocation.schema(),
            &caller,
            invocation.recipient(),
            invocation.channel(),
            invocation.sequence() + 1,
            invocation.input_id(),
            invocation.payload().to_vec(),
        )
        .unwrap();
        assert_eq!(
            result.verify(&other, &executor.verifying_key()),
            Err(WireError::InvocationMismatch)
        );
        let wrong_executor = SigningKey::from_bytes(&[11; 32]);
        assert!(matches!(
            SignedResult::sign(&invocation, &wrong_executor, O256::default(), Vec::new()),
            Err(MessageSigningError::Wire(WireError::PublicKeyMismatch))
        ));
    }

    #[test]
    fn malformed_and_tampered_results_are_rejected() {
        let (_, executor, invocation) = fixture();
        let result = SignedResult::sign(
            &invocation,
            &executor,
            O256::from_bytes(b"output id"),
            b"output".to_vec(),
        )
        .unwrap();
        let encoded = result.encode();
        for end in 0..encoded.len() {
            assert!(SignedResult::decode(&encoded[..end]).is_err());
        }
        let mut bad_reserved = encoded.clone();
        bad_reserved[10] = 1;
        assert_eq!(
            SignedResult::decode(&bad_reserved),
            Err(WireError::NonzeroReserved)
        );
        let mut bad_payload = encoded.clone();
        let payload_offset = RESULT_FIXED_BYTES - SIGNATURE_BYTES;
        bad_payload[payload_offset] ^= 1;
        assert_eq!(
            SignedResult::decode(&bad_payload),
            Err(WireError::PayloadHashMismatch)
        );
        let mut bad_signature = result.clone();
        bad_signature.signature[0] ^= 1;
        assert_eq!(
            bad_signature.verify(&invocation, &executor.verifying_key()),
            Err(WireError::InvalidSignature)
        );
    }

    #[derive(Debug)]
    struct SigningDenied;

    impl fmt::Display for SigningDenied {
        fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("denied")
        }
    }

    impl StdError for SigningDenied {}

    struct DenyingSigner {
        public_key: PublicKeyIdentity,
    }

    impl StatementSigner for DenyingSigner {
        type Error = SigningDenied;

        fn public_key(&self) -> PublicKeyIdentity {
            self.public_key
        }

        fn sign_statement(&self, _: O256) -> Result<[u8; SIGNATURE_BYTES], Self::Error> {
            Err(SigningDenied)
        }
    }

    #[test]
    fn signing_capability_failure_remains_distinct() {
        let signer = DenyingSigner {
            public_key: [7; 32],
        };
        let error = SignedInvocation::sign(
            O256::default(),
            &signer,
            [9; 32],
            ChannelNonce::new([1; 32]),
            0,
            O256::default(),
            Vec::new(),
        )
        .unwrap_err();
        assert!(matches!(error, MessageSigningError::Signer(SigningDenied)));
        assert_eq!(error.to_string(), "kernel statement signing failed: denied");
    }

    #[test]
    fn payload_limit_is_checked_before_signing() {
        let caller = SigningKey::from_bytes(&[7; 32]);
        assert!(matches!(
            SignedInvocation::sign(
                O256::default(),
                &caller,
                [0; 32],
                ChannelNonce::new([0; 32]),
                0,
                O256::default(),
                vec![0; MAX_WIRE_PAYLOAD_BYTES + 1],
            ),
            Err(MessageSigningError::Wire(WireError::PayloadTooLarge))
        ));
    }

    #[test]
    fn vectors_are_stable() {
        let (_, executor, invocation) = fixture();
        let result = SignedResult::sign(
            &invocation,
            &executor,
            O256::from_bytes(b"output id"),
            b"output".to_vec(),
        )
        .unwrap();
        // These fixture values are sufficient to reproduce and compare complete v0 frames in
        // another implementation without checking hundreds of hex digits into source.
        assert_eq!(
            hex(invocation.statement().as_ref()),
            "9663f2d9dbc4afe6da9fb7966b9b0cc94509689ba28dd29db1d5281ab0c323c1"
        );
        assert_eq!(
            hex(&invocation.signature),
            concat!(
                "e153221e5a9b2d5e378af702d635da490f8a9f13163e1180d9a0b954bc4903b",
                "2d0b0ff98ef411262fe9008826721ef624c63fe49daa326143c8eafcbad359c08"
            )
        );
        assert_eq!(invocation.encode().len(), 285);
        assert_eq!(
            hex(O256::from_bytes(invocation.encode()).as_ref()),
            "9561ac9a0c6076e6ea71cc5c764862000879dd1fe56cf37d29f5de7bdc8716d2"
        );
        assert_eq!(
            hex(result.statement().as_ref()),
            "b5e5fd183bcf584f7ec4859d1cf3298d01ce6a8e5739ba7156415dcd50695d93"
        );
        assert_eq!(
            hex(&result.signature),
            concat!(
                "66fadc8be3385d3eadbadf015202ff11c4278bdb0ab9a4b24b15a694f68db57f",
                "1ff574f3ac3b1810e147a6c14fc551d61465f00d4c0847c2eaf31427a91bba0f"
            )
        );
        assert_eq!(result.encode().len(), 318);
        assert_eq!(
            hex(O256::from_bytes(result.encode()).as_ref()),
            "4ff3d071da3df34b6c5bda11859da45b63a803b5533a590b9d146035999a9f6c"
        );
    }

    fn hex(bytes: &[u8]) -> String {
        use std::fmt::Write as _;
        let mut output = String::with_capacity(bytes.len() * 2);
        for byte in bytes {
            write!(output, "{byte:02x}").unwrap();
        }
        output
    }
}
