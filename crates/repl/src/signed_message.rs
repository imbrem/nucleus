//! Bounded binary encoding for the signed kernel service values.
//!
//! This module deliberately knows nothing about streams, frames, processes, or
//! browser messaging. Native pipes, Workers, `WebSockets`, and in-process
//! callers can carry the same versioned byte strings over their own transport.

use core::fmt;

use covalence_lib_hash::O256;

use crate::{KernelId, MAX_IMAGE_BYTES};

use super::{
    EndpointDescription, ExpectedKernelIdentity, ServiceIdentity, ServiceOperation,
    ServiceProducedHol, ServiceReceivedHol, ServiceResult, SessionAccepted, SessionRequest,
    SignedHolArtifact, SignedServiceCommand, SignedServiceReply,
};

const VERSION: u8 = 0;

/// Maximum encoded message size accepted or produced by this codec.
///
/// The allowance above [`MAX_IMAGE_BYTES`] covers the signed service envelope.
pub const MAX_SIGNED_MESSAGE_BYTES: usize = MAX_IMAGE_BYTES + 8192;

/// One requester-to-endpoint signed-service message.
#[derive(Clone)]
pub enum SignedMessageRequest {
    /// Requests the endpoint's self-signed description.
    Describe,
    /// Carries a requester-signed session handshake.
    OpenSession(SessionRequest),
    /// Carries one requester-signed service command.
    Execute(SignedServiceCommand),
}

/// One endpoint-to-requester signed-service message.
#[derive(Clone)]
pub enum SignedMessageResponse {
    /// Carries the endpoint's self-signed description.
    Description(EndpointDescription),
    /// Carries an endpoint-signed session acceptance.
    SessionAccepted(SessionAccepted),
    /// Carries an endpoint-signed command result.
    Reply(SignedServiceReply),
}

/// A rejected signed-message representation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SignedMessageError {
    /// The message violates a fixed tag, version, width, or structural rule.
    Protocol(&'static str),
    /// A bounded or cryptographic field is malformed.
    Invalid(String),
}

impl fmt::Display for SignedMessageError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Protocol(message) => {
                write!(formatter, "signed-message protocol error: {message}")
            }
            Self::Invalid(message) => write!(formatter, "invalid signed message: {message}"),
        }
    }
}

impl std::error::Error for SignedMessageError {}

/// Encodes one request as a versioned, bounded byte string.
///
/// # Errors
///
/// Returns an error when a field or the complete message exceeds its bound.
pub fn encode_signed_request(
    request: &SignedMessageRequest,
) -> Result<Vec<u8>, SignedMessageError> {
    let mut output = Encoder::new();
    match request {
        SignedMessageRequest::Describe => output.byte(0),
        SignedMessageRequest::OpenSession(request) => {
            output.byte(1);
            output.session_request(request)?;
        }
        SignedMessageRequest::Execute(command) => {
            output.byte(2);
            output.command(command)?;
        }
    }
    output.finish()
}

/// Decodes one complete versioned request.
///
/// # Errors
///
/// Returns an error for oversized input, unknown tags or versions, malformed
/// fields, truncation, or trailing bytes.
pub fn decode_signed_request(payload: &[u8]) -> Result<SignedMessageRequest, SignedMessageError> {
    let mut input = Decoder::new(payload)?;
    let request = match input.byte()? {
        0 => SignedMessageRequest::Describe,
        1 => SignedMessageRequest::OpenSession(input.session_request()?),
        2 => SignedMessageRequest::Execute(input.command()?),
        _ => return Err(SignedMessageError::Protocol("unknown request tag")),
    };
    input.finish()?;
    Ok(request)
}

/// Encodes one response as a versioned, bounded byte string.
///
/// # Errors
///
/// Returns an error when a field or the complete message exceeds its bound.
pub fn encode_signed_response(
    response: &SignedMessageResponse,
) -> Result<Vec<u8>, SignedMessageError> {
    let mut output = Encoder::new();
    match response {
        SignedMessageResponse::Description(description) => {
            output.byte(0);
            output.description(description)?;
        }
        SignedMessageResponse::SessionAccepted(accepted) => {
            output.byte(1);
            output.session_accepted(accepted)?;
        }
        SignedMessageResponse::Reply(reply) => {
            output.byte(2);
            output.reply(reply)?;
        }
    }
    output.finish()
}

/// Decodes one complete versioned response.
///
/// # Errors
///
/// Returns an error for oversized input, unknown tags or versions, malformed
/// fields, truncation, or trailing bytes.
pub fn decode_signed_response(payload: &[u8]) -> Result<SignedMessageResponse, SignedMessageError> {
    let mut input = Decoder::new(payload)?;
    let response = match input.byte()? {
        0 => SignedMessageResponse::Description(input.description()?),
        1 => SignedMessageResponse::SessionAccepted(input.session_accepted()?),
        2 => SignedMessageResponse::Reply(input.reply()?),
        _ => return Err(SignedMessageError::Protocol("unknown response tag")),
    };
    input.finish()?;
    Ok(response)
}

struct Encoder {
    bytes: Vec<u8>,
}

impl Encoder {
    fn new() -> Self {
        Self {
            bytes: vec![VERSION],
        }
    }

    fn finish(self) -> Result<Vec<u8>, SignedMessageError> {
        if self.bytes.len() > MAX_SIGNED_MESSAGE_BYTES {
            Err(SignedMessageError::Invalid(format!(
                "message is {} bytes; limit is {MAX_SIGNED_MESSAGE_BYTES}",
                self.bytes.len()
            )))
        } else {
            Ok(self.bytes)
        }
    }

    fn byte(&mut self, value: u8) {
        self.bytes.push(value);
    }

    fn u64(&mut self, value: u64) {
        self.bytes.extend_from_slice(&value.to_be_bytes());
    }

    fn i64(&mut self, value: i64) {
        self.bytes.extend_from_slice(&value.to_be_bytes());
    }

    fn bytes(&mut self, value: &[u8]) -> Result<(), SignedMessageError> {
        let length = u32::try_from(value.len())
            .map_err(|_| SignedMessageError::Protocol("field length does not fit u32"))?;
        let encoded_length = self
            .bytes
            .len()
            .checked_add(4)
            .and_then(|length| length.checked_add(value.len()))
            .ok_or(SignedMessageError::Protocol("message length overflow"))?;
        if encoded_length > MAX_SIGNED_MESSAGE_BYTES {
            return Err(SignedMessageError::Invalid(format!(
                "message exceeds {MAX_SIGNED_MESSAGE_BYTES} bytes"
            )));
        }
        self.bytes.extend_from_slice(&length.to_be_bytes());
        self.bytes.extend_from_slice(value);
        Ok(())
    }

    fn fixed_bytes<const N: usize>(
        &mut self,
        name: &str,
        value: &[u8],
    ) -> Result<(), SignedMessageError> {
        if value.len() != N {
            return Err(SignedMessageError::Invalid(format!(
                "{name} is {} bytes; expected {N}",
                value.len()
            )));
        }
        self.bytes(value)
    }

    fn string(&mut self, value: &str) -> Result<(), SignedMessageError> {
        self.bytes(value.as_bytes())
    }

    fn o256(&mut self, value: O256) -> Result<(), SignedMessageError> {
        self.string(&value.to_string())
    }

    fn identity(&mut self, identity: ServiceIdentity) -> Result<(), SignedMessageError> {
        self.o256(identity.signer)?;
        self.bytes(&identity.public_key)
    }

    fn description(&mut self, value: &EndpointDescription) -> Result<(), SignedMessageError> {
        self.identity(value.identity)?;
        self.bytes(&value.challenge)?;
        self.fixed_bytes::<64>("description signature", &value.signature)
    }

    fn session_request(&mut self, value: &SessionRequest) -> Result<(), SignedMessageError> {
        self.identity(value.endpoint)?;
        self.identity(value.requester)?;
        self.bytes(&value.challenge)?;
        self.bytes(&value.nonce)?;
        self.fixed_bytes::<64>("session request signature", &value.signature)
    }

    fn session_accepted(&mut self, value: &SessionAccepted) -> Result<(), SignedMessageError> {
        self.o256(value.session)?;
        self.identity(value.endpoint)?;
        self.identity(value.requester)?;
        self.o256(value.request_statement)?;
        self.fixed_bytes::<64>("session acceptance signature", &value.signature)
    }

    fn expected(&mut self, value: &ExpectedKernelIdentity) -> Result<(), SignedMessageError> {
        self.i64(value.kernel().get());
        self.o256(value.signer())?;
        self.bytes(value.public_key())
    }

    fn artifact(&mut self, value: &SignedHolArtifact) -> Result<(), SignedMessageError> {
        if value.image().len() > MAX_IMAGE_BYTES {
            return Err(SignedMessageError::Invalid(format!(
                "artifact image is {} bytes; limit is {MAX_IMAGE_BYTES}",
                value.image().len()
            )));
        }
        self.i64(value.namespace_id());
        self.bytes(value.image())?;
        self.o256(value.schema())?;
        self.o256(value.image_hash())?;
        self.o256(value.signer())?;
        self.fixed_bytes::<32>("artifact public key", value.public_key())?;
        self.fixed_bytes::<64>("artifact signature", value.signature())
    }

    fn operation(&mut self, value: &ServiceOperation) -> Result<(), SignedMessageError> {
        match value {
            ServiceOperation::OpenHol => self.byte(0),
            ServiceOperation::CloseHol(connection) => {
                self.byte(1);
                self.u64(*connection);
            }
            ServiceOperation::ProduceSignedHol(connection) => {
                self.byte(2);
                self.u64(*connection);
            }
            ServiceOperation::ReceiveSignedHol {
                connection,
                expected,
                artifact,
            } => {
                self.byte(3);
                self.u64(*connection);
                self.expected(expected)?;
                self.artifact(artifact)?;
            }
            ServiceOperation::Shutdown => self.byte(4),
        }
        Ok(())
    }

    fn command(&mut self, value: &SignedServiceCommand) -> Result<(), SignedMessageError> {
        self.o256(value.session)?;
        self.u64(value.sequence);
        self.o256(value.request_id)?;
        self.o256(value.requester)?;
        self.operation(&value.operation)?;
        self.o256(value.statement)?;
        self.fixed_bytes::<64>("command signature", &value.signature)
    }

    fn result(&mut self, value: &ServiceResult) -> Result<(), SignedMessageError> {
        match value {
            ServiceResult::Opened(connection) => {
                self.byte(0);
                self.u64(*connection);
            }
            ServiceResult::Closed => self.byte(1),
            ServiceResult::Produced(produced) => {
                self.byte(2);
                self.string(&produced.statement)?;
                self.artifact(&produced.artifact)?;
            }
            ServiceResult::Received(received) => {
                self.byte(3);
                self.i64(received.import);
                self.i64(received.namespace);
                self.i64(received.context);
                self.i64(received.conclusion);
            }
            ServiceResult::Goodbye => self.byte(4),
            ServiceResult::OperationError(message) => {
                self.byte(5);
                self.string(message)?;
            }
            ServiceResult::Rejected(message) => {
                self.byte(6);
                self.string(message)?;
            }
        }
        Ok(())
    }

    fn reply(&mut self, value: &SignedServiceReply) -> Result<(), SignedMessageError> {
        self.o256(value.session)?;
        self.u64(value.sequence);
        self.o256(value.request_id)?;
        self.o256(value.request_statement)?;
        self.o256(value.endpoint)?;
        self.result(&value.result)?;
        self.o256(value.result_digest)?;
        self.fixed_bytes::<64>("reply signature", &value.signature)
    }
}

struct Decoder<'a> {
    input: &'a [u8],
    offset: usize,
}

impl<'a> Decoder<'a> {
    fn new(input: &'a [u8]) -> Result<Self, SignedMessageError> {
        if input.len() > MAX_SIGNED_MESSAGE_BYTES {
            return Err(SignedMessageError::Invalid(format!(
                "message is {} bytes; limit is {MAX_SIGNED_MESSAGE_BYTES}",
                input.len()
            )));
        }
        if input.first().copied() != Some(VERSION) {
            return Err(SignedMessageError::Protocol("unsupported message version"));
        }
        Ok(Self { input, offset: 1 })
    }

    fn finish(self) -> Result<(), SignedMessageError> {
        if self.offset == self.input.len() {
            Ok(())
        } else {
            Err(SignedMessageError::Protocol("trailing message bytes"))
        }
    }

    fn take(&mut self, length: usize) -> Result<&'a [u8], SignedMessageError> {
        let end = self
            .offset
            .checked_add(length)
            .ok_or(SignedMessageError::Protocol("field length overflow"))?;
        let value = self
            .input
            .get(self.offset..end)
            .ok_or(SignedMessageError::Protocol("truncated field"))?;
        self.offset = end;
        Ok(value)
    }

    fn byte(&mut self) -> Result<u8, SignedMessageError> {
        Ok(self.take(1)?[0])
    }

    fn u64(&mut self) -> Result<u64, SignedMessageError> {
        Ok(u64::from_be_bytes(
            self.take(8)?.try_into().expect("exact width"),
        ))
    }

    fn i64(&mut self) -> Result<i64, SignedMessageError> {
        Ok(i64::from_be_bytes(
            self.take(8)?.try_into().expect("exact width"),
        ))
    }

    fn bytes(&mut self) -> Result<Vec<u8>, SignedMessageError> {
        let length = self.length()?;
        Ok(self.take(length)?.to_vec())
    }

    fn fixed<const N: usize>(&mut self, name: &str) -> Result<[u8; N], SignedMessageError> {
        let length = self.length()?;
        if length != N {
            return Err(SignedMessageError::Invalid(format!(
                "{name} is {length} bytes; expected {N}"
            )));
        }
        Ok(self.take(N)?.try_into().expect("exact width"))
    }

    fn length(&mut self) -> Result<usize, SignedMessageError> {
        Ok(u32::from_be_bytes(self.take(4)?.try_into().expect("exact width")) as usize)
    }

    fn string(&mut self) -> Result<String, SignedMessageError> {
        String::from_utf8(self.bytes()?)
            .map_err(|error| SignedMessageError::Invalid(error.to_string()))
    }

    fn o256(&mut self) -> Result<O256, SignedMessageError> {
        let encoded = self.string()?;
        let value = O256::from_hex(&encoded)
            .map_err(|error| SignedMessageError::Invalid(error.to_string()))?;
        if value.to_string() != encoded {
            return Err(SignedMessageError::Invalid(
                "O256 is not canonically encoded".to_owned(),
            ));
        }
        Ok(value)
    }

    fn identity(&mut self) -> Result<ServiceIdentity, SignedMessageError> {
        ServiceIdentity::new(self.o256()?, self.fixed::<32>("public key")?)
            .map_err(|error| SignedMessageError::Invalid(error.to_string()))
    }

    fn description(&mut self) -> Result<EndpointDescription, SignedMessageError> {
        Ok(EndpointDescription {
            identity: self.identity()?,
            challenge: self.fixed::<32>("challenge")?,
            signature: self.fixed::<64>("description signature")?.to_vec(),
        })
    }

    fn session_request(&mut self) -> Result<SessionRequest, SignedMessageError> {
        Ok(SessionRequest {
            endpoint: self.identity()?,
            requester: self.identity()?,
            challenge: self.fixed::<32>("challenge")?,
            nonce: self.fixed::<32>("nonce")?,
            signature: self.fixed::<64>("session request signature")?.to_vec(),
        })
    }

    fn session_accepted(&mut self) -> Result<SessionAccepted, SignedMessageError> {
        Ok(SessionAccepted {
            session: self.o256()?,
            endpoint: self.identity()?,
            requester: self.identity()?,
            request_statement: self.o256()?,
            signature: self.fixed::<64>("session acceptance signature")?.to_vec(),
        })
    }

    fn expected(&mut self) -> Result<ExpectedKernelIdentity, SignedMessageError> {
        let kernel = self.i64()?;
        let signer = self.o256()?;
        let public_key = self.fixed::<32>("expected public key")?;
        ExpectedKernelIdentity::from_untrusted_parts(
            KernelId::from_i64(kernel),
            &signer.to_string(),
            &public_key,
        )
        .map_err(|error| SignedMessageError::Invalid(error.to_string()))
    }

    fn artifact(&mut self) -> Result<SignedHolArtifact, SignedMessageError> {
        let namespace = self.i64()?;
        let image = self.bytes()?;
        if image.len() > MAX_IMAGE_BYTES {
            return Err(SignedMessageError::Invalid(format!(
                "artifact image is {} bytes; limit is {MAX_IMAGE_BYTES}",
                image.len()
            )));
        }
        let schema = self.o256()?;
        let image_hash = self.o256()?;
        let signer = self.o256()?;
        let public_key = self.fixed::<32>("artifact public key")?.to_vec();
        let signature = self.fixed::<64>("artifact signature")?.to_vec();
        SignedHolArtifact::from_untrusted_parts(
            namespace,
            image,
            &schema.to_string(),
            &image_hash.to_string(),
            &signer.to_string(),
            public_key,
            signature,
        )
        .map_err(|error| SignedMessageError::Invalid(error.to_string()))
    }

    fn operation(&mut self) -> Result<ServiceOperation, SignedMessageError> {
        match self.byte()? {
            0 => Ok(ServiceOperation::OpenHol),
            1 => Ok(ServiceOperation::CloseHol(self.u64()?)),
            2 => Ok(ServiceOperation::ProduceSignedHol(self.u64()?)),
            3 => Ok(ServiceOperation::ReceiveSignedHol {
                connection: self.u64()?,
                expected: self.expected()?,
                artifact: Box::new(self.artifact()?),
            }),
            4 => Ok(ServiceOperation::Shutdown),
            _ => Err(SignedMessageError::Protocol("unknown operation tag")),
        }
    }

    fn command(&mut self) -> Result<SignedServiceCommand, SignedMessageError> {
        Ok(SignedServiceCommand {
            session: self.o256()?,
            sequence: self.u64()?,
            request_id: self.o256()?,
            requester: self.o256()?,
            operation: self.operation()?,
            statement: self.o256()?,
            signature: self.fixed::<64>("command signature")?.to_vec(),
        })
    }

    fn result(&mut self) -> Result<ServiceResult, SignedMessageError> {
        match self.byte()? {
            0 => Ok(ServiceResult::Opened(self.u64()?)),
            1 => Ok(ServiceResult::Closed),
            2 => Ok(ServiceResult::Produced(Box::new(ServiceProducedHol {
                statement: self.string()?,
                artifact: self.artifact()?,
            }))),
            3 => Ok(ServiceResult::Received(ServiceReceivedHol {
                import: self.i64()?,
                namespace: self.i64()?,
                context: self.i64()?,
                conclusion: self.i64()?,
            })),
            4 => Ok(ServiceResult::Goodbye),
            5 => Ok(ServiceResult::OperationError(self.string()?)),
            6 => Ok(ServiceResult::Rejected(self.string()?)),
            _ => Err(SignedMessageError::Protocol("unknown result tag")),
        }
    }

    fn reply(&mut self) -> Result<SignedServiceReply, SignedMessageError> {
        Ok(SignedServiceReply {
            session: self.o256()?,
            sequence: self.u64()?,
            request_id: self.o256()?,
            request_statement: self.o256()?,
            endpoint: self.o256()?,
            result: self.result()?,
            result_digest: self.o256()?,
            signature: self.fixed::<64>("reply signature")?.to_vec(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{SessionInitiator, SignedKernelService, SignedServiceSession};

    fn hex(bytes: &[u8]) -> String {
        const DIGITS: &[u8; 16] = b"0123456789abcdef";
        let mut output = String::with_capacity(bytes.len() * 2);
        for byte in bytes {
            output.push(DIGITS[usize::from(byte >> 4)] as char);
            output.push(DIGITS[usize::from(byte & 0x0f)] as char);
        }
        output
    }

    fn round_trip_request(value: &SignedMessageRequest) -> SignedMessageRequest {
        decode_signed_request(&encode_signed_request(value).unwrap()).unwrap()
    }

    fn round_trip_response(value: &SignedMessageResponse) -> SignedMessageResponse {
        decode_signed_response(&encode_signed_response(value).unwrap()).unwrap()
    }

    #[test]
    fn codec_preserves_a_verified_signed_lifecycle() {
        let mut service = SignedKernelService::new().unwrap();
        let SignedMessageResponse::Description(description) = round_trip_response(
            &SignedMessageResponse::Description(service.description().clone()),
        ) else {
            panic!("wrong response");
        };
        let initiator = SessionInitiator::begin(description.identity(), &description).unwrap();
        let SignedMessageRequest::OpenSession(request) = round_trip_request(
            &SignedMessageRequest::OpenSession(initiator.request().clone()),
        ) else {
            panic!("wrong request");
        };
        let accepted = service.open_session(&request).unwrap();
        let SignedMessageResponse::SessionAccepted(accepted) =
            round_trip_response(&SignedMessageResponse::SessionAccepted(accepted))
        else {
            panic!("wrong response");
        };
        let mut session = initiator.accept(&accepted).unwrap();
        assert_open(&mut service, &mut session);
    }

    fn assert_open(service: &mut SignedKernelService, session: &mut SignedServiceSession) {
        let command = session.command(ServiceOperation::OpenHol).unwrap();
        let SignedMessageRequest::Execute(command) =
            round_trip_request(&SignedMessageRequest::Execute(command))
        else {
            panic!("wrong request");
        };
        let reply = service.execute(&command).unwrap();
        let SignedMessageResponse::Reply(reply) =
            round_trip_response(&SignedMessageResponse::Reply(reply))
        else {
            panic!("wrong response");
        };
        assert!(matches!(
            session.accept_reply(&command, reply).unwrap(),
            ServiceResult::Opened(1)
        ));
    }

    #[test]
    fn describe_request_has_a_stable_vector() {
        assert_eq!(
            encode_signed_request(&SignedMessageRequest::Describe).unwrap(),
            [0, 0]
        );
    }

    #[test]
    fn endpoint_description_has_a_stable_vector() {
        let public_key = [7; 32];
        let identity =
            ServiceIdentity::new(covalence_nucleus::ed25519_key_id(&public_key), public_key)
                .unwrap();
        let description = EndpointDescription {
            identity,
            challenge: [8; 32],
            signature: vec![9; 64],
        };
        let encoded =
            encode_signed_response(&SignedMessageResponse::Description(description)).unwrap();
        assert_eq!(
            hex(&encoded),
            "000000000040366563313563626539386630333437663462656634333565633266623366376232373739613366353461303338623463353233343133636361633534333661660000002007070707070707070707070707070707070707070707070707070707070707070000002008080808080808080808080808080808080808080808080808080808080808080000004009090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909"
        );
    }

    #[test]
    fn rejects_versions_tags_truncation_trailing_bytes_and_oversize() {
        assert!(matches!(
            decode_signed_request(&[1, 0]),
            Err(SignedMessageError::Protocol("unsupported message version"))
        ));
        assert!(matches!(
            decode_signed_request(&[0, 9]),
            Err(SignedMessageError::Protocol("unknown request tag"))
        ));
        assert!(matches!(
            decode_signed_request(&[0, 1]),
            Err(SignedMessageError::Protocol("truncated field"))
        ));
        assert!(matches!(
            decode_signed_request(&[0, 0, 0]),
            Err(SignedMessageError::Protocol("trailing message bytes"))
        ));
        let oversized = vec![0; MAX_SIGNED_MESSAGE_BYTES + 1];
        assert!(matches!(
            decode_signed_request(&oversized),
            Err(SignedMessageError::Invalid(_))
        ));
    }

    #[test]
    fn rejects_noncanonical_hashes_and_nested_unknown_tags() {
        let public_key = [7; 32];
        let identity =
            ServiceIdentity::new(covalence_nucleus::ed25519_key_id(&public_key), public_key)
                .unwrap();
        let description = EndpointDescription {
            identity,
            challenge: [8; 32],
            signature: vec![9; 64],
        };
        let mut uppercase =
            encode_signed_response(&SignedMessageResponse::Description(description)).unwrap();
        let letter = uppercase[6..70]
            .iter_mut()
            .find(|byte| matches!(byte, b'a'..=b'f'))
            .unwrap();
        *letter = letter.to_ascii_uppercase();
        assert!(matches!(
            decode_signed_response(&uppercase),
            Err(SignedMessageError::Invalid(message))
                if message == "O256 is not canonically encoded"
        ));

        let coordinate = O256::from_bytes(b"coordinate");
        let mut unknown_operation = Encoder::new();
        unknown_operation.byte(2);
        unknown_operation.o256(coordinate).unwrap();
        unknown_operation.u64(0);
        unknown_operation.o256(coordinate).unwrap();
        unknown_operation.o256(coordinate).unwrap();
        unknown_operation.byte(9);
        assert!(matches!(
            decode_signed_request(&unknown_operation.finish().unwrap()),
            Err(SignedMessageError::Protocol("unknown operation tag"))
        ));

        let mut unknown_result = Encoder::new();
        unknown_result.byte(2);
        unknown_result.o256(coordinate).unwrap();
        unknown_result.u64(0);
        unknown_result.o256(coordinate).unwrap();
        unknown_result.o256(coordinate).unwrap();
        unknown_result.o256(coordinate).unwrap();
        unknown_result.byte(9);
        assert!(matches!(
            decode_signed_response(&unknown_result.finish().unwrap()),
            Err(SignedMessageError::Protocol("unknown result tag"))
        ));
    }

    #[test]
    fn expected_kernel_routing_labels_round_trip_the_full_i64_domain() {
        let public_key = [11; 32];
        for kernel in [i64::MIN, -1, 0, i64::MAX] {
            let expected =
                ExpectedKernelIdentity::from_public_key(KernelId::from_i64(kernel), &public_key)
                    .unwrap();
            let mut encoded = Encoder::new();
            encoded.expected(&expected).unwrap();
            let bytes = encoded.finish().unwrap();
            let mut decoded = Decoder::new(&bytes).unwrap();
            assert_eq!(decoded.expected().unwrap().kernel().get(), kernel);
            decoded.finish().unwrap();
        }
    }
}
