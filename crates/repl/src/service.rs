//! Schema-qualified signed command semantics for inter-kernel adapters.
//!
//! This module owns no transport. Stdio, Workers, `WebSockets`, and in-process
//! tests can carry these values in different ways while sharing the same PKI
//! transcript and strict sequencing rules.

use std::collections::{HashMap, HashSet};
use std::error::Error as StdError;
use std::fmt;

use covalence_lib_hash::O256;
use covalence_nucleus::{Ed25519Verifier, Signer as _, Verifier as _, ed25519_key_id};

use super::{
    AllowAll, Connection, ExpectedKernelIdentity, Hol, Kernel, KernelId, ReceivedHolSnapshot,
    SignedHolArtifact, authenticate_pinned_signed_hol_artifact, produce_signed_hol_artifact,
    trust_and_receive_pinned_signed_hol_artifact,
};

#[path = "signed_message.rs"]
pub mod signed_message;

/// Returns the schema which defines command and response transcript hashing.
#[must_use]
pub fn signed_kernel_service_schema() -> O256 {
    O256::from_bytes(include_bytes!("service_semantics.txt"))
}

/// A coherent Ed25519 endpoint identity used outside logical trust state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ServiceIdentity {
    signer: O256,
    public_key: [u8; 32],
}

impl ServiceIdentity {
    /// Checks that `signer` is the standard identity of `public_key`.
    ///
    /// # Errors
    ///
    /// Returns an error when the coordinates are incoherent.
    pub fn new(signer: O256, public_key: [u8; 32]) -> Result<Self, ServiceError> {
        if ed25519_key_id(&public_key) != signer {
            return Err(ServiceError::Invalid("signer does not identify public key"));
        }
        Ok(Self { signer, public_key })
    }

    /// Returns the content-derived public-key identity.
    #[must_use]
    pub const fn signer(self) -> O256 {
        self.signer
    }

    /// Returns the exact Ed25519 public key.
    #[must_use]
    pub const fn public_key(self) -> [u8; 32] {
        self.public_key
    }

    fn verifier(self) -> Result<Ed25519Verifier, ServiceError> {
        let key = covalence_lib_crypto::ed25519::VerifyingKey::from_bytes(&self.public_key)
            .map_err(|_| ServiceError::Invalid("public key is not valid Ed25519"))?;
        Ok(Ed25519Verifier::new(key))
    }
}

/// Self-signed endpoint metadata and one fresh session challenge.
#[derive(Clone)]
pub struct EndpointDescription {
    identity: ServiceIdentity,
    challenge: [u8; 32],
    signature: Vec<u8>,
}

impl EndpointDescription {
    /// Returns the endpoint identity.
    #[must_use]
    pub const fn identity(&self) -> ServiceIdentity {
        self.identity
    }

    /// Returns the session challenge.
    #[must_use]
    pub const fn challenge(&self) -> [u8; 32] {
        self.challenge
    }

    /// Returns the endpoint signature over its schema-qualified description.
    #[must_use]
    pub fn signature(&self) -> &[u8] {
        &self.signature
    }

    fn statement(&self) -> O256 {
        description_statement(self.identity, &self.challenge)
    }
}

/// Requester-signed response to an endpoint challenge.
#[derive(Clone)]
pub struct SessionRequest {
    endpoint: ServiceIdentity,
    requester: ServiceIdentity,
    challenge: [u8; 32],
    nonce: [u8; 32],
    signature: Vec<u8>,
}

impl SessionRequest {
    /// Returns the requester identity.
    #[must_use]
    pub const fn requester(&self) -> ServiceIdentity {
        self.requester
    }

    fn statement(&self) -> O256 {
        session_request_statement(self.endpoint, self.requester, &self.challenge, &self.nonce)
    }
}

/// Endpoint-signed acceptance of one unique session transcript.
#[derive(Clone)]
pub struct SessionAccepted {
    session: O256,
    endpoint: ServiceIdentity,
    requester: ServiceIdentity,
    request_statement: O256,
    signature: Vec<u8>,
}

impl SessionAccepted {
    /// Returns the session coordinate.
    #[must_use]
    pub const fn session(&self) -> O256 {
        self.session
    }

    fn statement(&self) -> O256 {
        session_accepted_statement(
            self.session,
            self.endpoint,
            self.requester,
            self.request_statement,
        )
    }
}

/// One operation covered by a requester signature.
#[derive(Clone)]
pub enum ServiceOperation {
    /// Opens a connection and returns its session-local handle.
    OpenHol,
    /// Closes a session-local connection.
    CloseHol(u64),
    /// Produces the shared signed HOL demonstration artifact.
    ProduceSignedHol(u64),
    /// Pins, validates, explicitly trusts, imports, and reads an artifact.
    ReceiveSignedHol {
        /// Receiver connection handle.
        connection: u64,
        /// Independently selected source endpoint.
        expected: ExpectedKernelIdentity,
        /// Untrusted artifact transported from the source.
        artifact: Box<SignedHolArtifact>,
    },
    /// Runs the one endpoint-allowlisted HOL proof component identified by its
    /// exact content digest. Component bytes are never carried by this service.
    RunHolProofComponent(O256),
    /// Gracefully ends a stateful transport after its signed reply.
    Shutdown,
}

/// Artifact produced by one endpoint-allowlisted proof component.
#[derive(Clone)]
pub struct ServiceProducedHolComponent {
    component: O256,
    artifact: SignedHolArtifact,
}

impl ServiceProducedHolComponent {
    /// Returns the exact component digest selected by the signed request.
    #[must_use]
    pub const fn component(&self) -> O256 {
        self.component
    }

    /// Returns the independently signed, schema-qualified `SQLite` artifact.
    #[must_use]
    pub const fn artifact(&self) -> &SignedHolArtifact {
        &self.artifact
    }

    /// Takes ownership of the artifact.
    #[must_use]
    pub fn into_artifact(self) -> SignedHolArtifact {
        self.artifact
    }
}

/// Above-TCB producer presentation returned by a service.
#[derive(Clone)]
pub struct ServiceProducedHol {
    statement: String,
    artifact: SignedHolArtifact,
}

impl ServiceProducedHol {
    /// Returns the producer's presentation string.
    #[must_use]
    pub fn statement(&self) -> &str {
        &self.statement
    }

    /// Returns the signed artifact for independent pinned receipt.
    #[must_use]
    pub const fn artifact(&self) -> &SignedHolArtifact {
        &self.artifact
    }

    /// Takes ownership of the artifact.
    #[must_use]
    pub fn into_artifact(self) -> SignedHolArtifact {
        self.artifact
    }
}

/// Receiver-local coordinates returned by a signed service operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ServiceReceivedHol {
    import: i64,
    namespace: i64,
    context: i64,
    conclusion: i64,
}

impl ServiceReceivedHol {
    /// Returns the receiver-local import ID.
    #[must_use]
    pub const fn import_id(self) -> i64 {
        self.import
    }

    /// Returns the receiver-local imported namespace ID.
    #[must_use]
    pub const fn namespace_id(self) -> i64 {
        self.namespace
    }

    /// Returns the source context coordinate checked by the receiver.
    #[must_use]
    pub const fn context_id(self) -> i64 {
        self.context
    }

    /// Returns the source conclusion coordinate checked by the receiver.
    #[must_use]
    pub const fn conclusion_id(self) -> i64 {
        self.conclusion
    }
}

impl From<ReceivedHolSnapshot> for ServiceReceivedHol {
    fn from(received: ReceivedHolSnapshot) -> Self {
        Self {
            import: received.import_id(),
            namespace: received.namespace_id(),
            context: received.context_id(),
            conclusion: received.conclusion_id(),
        }
    }
}

/// One service result covered by an endpoint signature.
#[derive(Clone)]
pub enum ServiceResult {
    /// A connection was opened.
    Opened(u64),
    /// A connection was closed.
    Closed,
    /// A signed HOL artifact was produced.
    Produced(Box<ServiceProducedHol>),
    /// A pinned artifact was trusted, imported, and read.
    Received(ServiceReceivedHol),
    /// The selected allowlisted component produced a signed HOL artifact.
    ProducedByComponent(Box<ServiceProducedHolComponent>),
    /// A signed shutdown request was accepted.
    Goodbye,
    /// A request was authenticated but its operation failed.
    OperationError(String),
    /// A command failed authentication or ordering before dispatch.
    Rejected(String),
}

/// One requester-authenticated command.
#[derive(Clone)]
pub struct SignedServiceCommand {
    session: O256,
    sequence: u64,
    request_id: O256,
    requester: O256,
    operation: ServiceOperation,
    statement: O256,
    signature: Vec<u8>,
}

impl SignedServiceCommand {
    /// Returns the session coordinate.
    #[must_use]
    pub const fn session(&self) -> O256 {
        self.session
    }

    /// Returns the strict session sequence number.
    #[must_use]
    pub const fn sequence(&self) -> u64 {
        self.sequence
    }

    /// Returns the caller-selected request ID.
    #[must_use]
    pub const fn request_id(&self) -> O256 {
        self.request_id
    }

    /// Returns the signed operation.
    #[must_use]
    pub const fn operation(&self) -> &ServiceOperation {
        &self.operation
    }
}

/// Endpoint-authenticated result bound to one exact command statement.
#[derive(Clone)]
pub struct SignedServiceReply {
    session: O256,
    sequence: u64,
    request_id: O256,
    request_statement: O256,
    endpoint: O256,
    result: ServiceResult,
    result_digest: O256,
    signature: Vec<u8>,
}

impl SignedServiceReply {
    /// Checks server-produced shutdown state without exposing an unverified result.
    ///
    /// Client adapters must use [`SignedServiceSession::accept_reply`] instead.
    #[must_use]
    #[allow(dead_code, reason = "consumed by sibling transport adapters")]
    pub(crate) const fn is_goodbye(&self) -> bool {
        matches!(self.result, ServiceResult::Goodbye)
    }

    fn statement(&self) -> O256 {
        reply_statement(
            self.session,
            self.sequence,
            self.request_id,
            self.request_statement,
            self.result_digest,
        )
    }
}

struct ServerSession {
    requester: ServiceIdentity,
    next_sequence: u64,
    next_connection: u64,
    connections: HashMap<u64, Connection<Hol<AllowAll>>>,
    last_reply: Option<CachedReply>,
    closed: bool,
}

struct CachedReply {
    sequence: u64,
    request_id: O256,
    request_statement: O256,
    reply: SignedServiceReply,
}

enum Preflight {
    Dispatch,
    Replay(Box<SignedServiceReply>),
}

type HolComponentExecutor =
    Box<dyn FnMut(&Kernel) -> Result<SignedHolArtifact, &'static str> + Send + 'static>;

struct AllowedHolComponent {
    digest: O256,
    execute: HolComponentExecutor,
}

/// Transport-independent signed kernel command service.
pub struct SignedKernelService {
    kernel: Kernel,
    description: EndpointDescription,
    used_session_requests: HashSet<O256>,
    sessions: HashMap<O256, ServerSession>,
    next_session: u64,
    allowed_hol_component: Option<AllowedHolComponent>,
}

impl SignedKernelService {
    /// Creates a service with a fresh process-local key and challenge.
    ///
    /// # Errors
    ///
    /// Returns an error if the signing capability unexpectedly fails.
    pub fn new() -> Result<Self, ServiceError> {
        let kernel = Kernel::ephemeral();
        let identity = ServiceIdentity::new(kernel.key_id(), *kernel.verifying_key().as_bytes())?;
        let challenge = covalence_lib_rand::random::<[u8; 32]>();
        let statement = description_statement(identity, &challenge);
        let signature = kernel
            .signer()
            .sign(identity.signer, statement)
            .map_err(|error| ServiceError::Signing(error.to_string()))?
            .to_vec();
        Ok(Self {
            kernel,
            description: EndpointDescription {
                identity,
                challenge,
                signature,
            },
            used_session_requests: HashSet::new(),
            sessions: HashMap::new(),
            next_session: 0,
            allowed_hol_component: None,
        })
    }

    /// Installs one locally selected executor under its exact component digest.
    ///
    /// This crate-private hook deliberately accepts no component bytes from a
    /// service request. Native adapters use it only after local validation and
    /// compilation have completed, before accepting remote sessions.
    #[allow(dead_code, reason = "consumed by the native allowlist adapter")]
    pub(crate) fn allow_hol_proof_component(
        &mut self,
        digest: O256,
        execute: impl FnMut(&Kernel) -> Result<SignedHolArtifact, &'static str> + Send + 'static,
    ) -> Result<(), ServiceError> {
        if !self.sessions.is_empty() || !self.used_session_requests.is_empty() {
            return Err(ServiceError::Invalid(
                "HOL proof component must be configured before sessions",
            ));
        }
        if self.allowed_hol_component.is_some() {
            return Err(ServiceError::Invalid(
                "HOL proof component is already configured",
            ));
        }
        self.allowed_hol_component = Some(AllowedHolComponent {
            digest,
            execute: Box::new(execute),
        });
        Ok(())
    }

    /// Returns self-signed endpoint metadata for an out-of-band pinned peer.
    #[must_use]
    pub const fn description(&self) -> &EndpointDescription {
        &self.description
    }

    /// Authenticates a requester and creates a strictly sequenced session.
    ///
    /// # Errors
    ///
    /// Rejects identity mismatch, invalid signature, wrong challenge, and an
    /// exact replay before allocating session state.
    pub fn open_session(
        &mut self,
        request: &SessionRequest,
    ) -> Result<SessionAccepted, ServiceError> {
        if request.endpoint != self.description.identity {
            return Err(ServiceError::Invalid(
                "session targets a different endpoint",
            ));
        }
        if request.challenge != self.description.challenge {
            return Err(ServiceError::Invalid("session challenge does not match"));
        }
        let statement = request.statement();
        if self.used_session_requests.contains(&statement) {
            return Err(ServiceError::Invalid("session request was replayed"));
        }
        request
            .requester
            .verifier()?
            .verify(request.requester.signer, statement, &request.signature)
            .map_err(|error| ServiceError::Verification(error.to_string()))?;

        let counter = self.next_session;
        self.next_session = self
            .next_session
            .checked_add(1)
            .ok_or(ServiceError::Invalid("service session counter exhausted"))?;
        let session = digest(b"session", &[statement.as_ref(), &counter.to_be_bytes()]);
        self.used_session_requests.insert(statement);
        self.sessions.insert(
            session,
            ServerSession {
                requester: request.requester,
                next_sequence: 0,
                next_connection: 1,
                connections: HashMap::new(),
                last_reply: None,
                closed: false,
            },
        );
        let mut accepted = SessionAccepted {
            session,
            endpoint: self.description.identity,
            requester: request.requester,
            request_statement: statement,
            signature: Vec::new(),
        };
        accepted.signature = self.sign(accepted.statement())?;
        Ok(accepted)
    }

    /// Verifies and dispatches one command, then signs its exact result.
    ///
    /// Authentication and strict ordering are checked before connection state
    /// is read or mutated. Rejections are themselves signed and request-bound.
    ///
    /// # Errors
    ///
    /// Returns an error only if the endpoint cannot sign its response.
    pub fn execute(
        &mut self,
        command: &SignedServiceCommand,
    ) -> Result<SignedServiceReply, ServiceError> {
        match self.preflight(command) {
            Ok(Preflight::Replay(reply)) => Ok(*reply),
            Ok(Preflight::Dispatch) => {
                let result = self.dispatch(command);
                let reply = self.reply(command, result)?;
                let Some(session) = self.sessions.get_mut(&command.session) else {
                    return Err(ServiceError::Invalid(
                        "authenticated service session disappeared",
                    ));
                };
                session.last_reply = Some(CachedReply {
                    sequence: command.sequence,
                    request_id: command.request_id,
                    request_statement: command.statement,
                    reply: reply.clone(),
                });
                Ok(reply)
            }
            Err(error) => self.reply(command, ServiceResult::Rejected(error.to_string())),
        }
    }

    fn preflight(&self, command: &SignedServiceCommand) -> Result<Preflight, ServiceError> {
        let session = self
            .sessions
            .get(&command.session)
            .ok_or(ServiceError::Invalid("unknown service session"))?;
        if command.requester != session.requester.signer {
            return Err(ServiceError::Invalid(
                "command requester does not own session",
            ));
        }
        if command.statement
            != command_statement(
                command.session,
                command.sequence,
                command.request_id,
                command.requester,
                &command.operation,
            )
        {
            return Err(ServiceError::Invalid("command digest is incoherent"));
        }
        session
            .requester
            .verifier()?
            .verify(command.requester, command.statement, &command.signature)
            .map_err(|error| ServiceError::Verification(error.to_string()))?;
        if command.sequence == session.next_sequence {
            if session.closed {
                return Err(ServiceError::Invalid("service session is closed"));
            }
            if command.sequence == u64::MAX {
                return Err(ServiceError::Invalid("command sequence exhausted"));
            }
            return Ok(Preflight::Dispatch);
        }
        if let Some(cached) = &session.last_reply
            && cached.sequence == command.sequence
            && cached.request_id == command.request_id
            && cached.request_statement == command.statement
        {
            return Ok(Preflight::Replay(Box::new(cached.reply.clone())));
        }
        Err(ServiceError::Invalid("command sequence is not next"))
    }

    fn dispatch(&mut self, command: &SignedServiceCommand) -> ServiceResult {
        let session = self
            .sessions
            .get_mut(&command.session)
            .expect("preflight established session");
        session.next_sequence = session
            .next_sequence
            .checked_add(1)
            .expect("preflight excluded sequence exhaustion");
        match command.operation {
            ServiceOperation::OpenHol => match self.kernel.open_hol(AllowAll) {
                Ok(connection) => {
                    let id = session.next_connection;
                    let Some(next) = session.next_connection.checked_add(1) else {
                        return ServiceResult::OperationError(
                            "HOL connection counter exhausted".to_owned(),
                        );
                    };
                    session.next_connection = next;
                    session.connections.insert(id, connection);
                    ServiceResult::Opened(id)
                }
                Err(error) => ServiceResult::OperationError(error.to_string()),
            },
            ServiceOperation::CloseHol(id) => {
                if session.connections.remove(&id).is_some() {
                    ServiceResult::Closed
                } else {
                    ServiceResult::OperationError(format!("unknown HOL connection {id}"))
                }
            }
            ServiceOperation::ProduceSignedHol(id) => {
                let Some(connection) = session.connections.get_mut(&id) else {
                    return ServiceResult::OperationError(format!("unknown HOL connection {id}"));
                };
                match produce_signed_hol_artifact(&self.kernel, connection) {
                    Ok(produced) => ServiceResult::Produced(Box::new(ServiceProducedHol {
                        statement: produced.proof().statement().to_owned(),
                        artifact: produced.into_parts().1,
                    })),
                    Err(error) => ServiceResult::OperationError(error.to_string()),
                }
            }
            ServiceOperation::ReceiveSignedHol {
                connection,
                ref expected,
                ref artifact,
            } => {
                let Some(target) = session.connections.get_mut(&connection) else {
                    return ServiceResult::OperationError(format!(
                        "unknown HOL connection {connection}"
                    ));
                };
                let pinned = match authenticate_pinned_signed_hol_artifact(expected, artifact) {
                    Ok(pinned) => pinned,
                    Err(error) => return ServiceResult::OperationError(error.to_string()),
                };
                match trust_and_receive_pinned_signed_hol_artifact(target, pinned) {
                    Ok(received) => ServiceResult::Received(received.into()),
                    Err(error) => ServiceResult::OperationError(error.to_string()),
                }
            }
            ServiceOperation::RunHolProofComponent(component) => {
                let Some(allowed) = self.allowed_hol_component.as_mut() else {
                    return ServiceResult::OperationError(
                        "HOL proof component execution is unavailable".to_owned(),
                    );
                };
                if component != allowed.digest {
                    return ServiceResult::OperationError(
                        "HOL proof component is not allowlisted".to_owned(),
                    );
                }
                let artifact = match (allowed.execute)(&self.kernel) {
                    Ok(artifact) => artifact,
                    Err(error) => return ServiceResult::OperationError(error.to_owned()),
                };
                let expected = match ExpectedKernelIdentity::from_public_key(
                    KernelId::LOCAL,
                    self.kernel.verifying_key().as_bytes(),
                ) {
                    Ok(expected) => expected,
                    Err(error) => return ServiceResult::OperationError(error.to_string()),
                };
                if let Err(error) = authenticate_pinned_signed_hol_artifact(&expected, &artifact) {
                    return ServiceResult::OperationError(format!(
                        "component executor returned an invalid endpoint artifact: {error}"
                    ));
                }
                ServiceResult::ProducedByComponent(Box::new(ServiceProducedHolComponent {
                    component,
                    artifact,
                }))
            }
            ServiceOperation::Shutdown => {
                session.closed = true;
                ServiceResult::Goodbye
            }
        }
    }

    fn reply(
        &self,
        command: &SignedServiceCommand,
        result: ServiceResult,
    ) -> Result<SignedServiceReply, ServiceError> {
        let result_digest = service_result_digest(&result);
        let mut reply = SignedServiceReply {
            session: command.session,
            sequence: command.sequence,
            request_id: command.request_id,
            request_statement: command.statement,
            endpoint: self.description.identity.signer,
            result,
            result_digest,
            signature: Vec::new(),
        };
        reply.signature = self.sign(reply.statement())?;
        Ok(reply)
    }

    fn sign(&self, statement: O256) -> Result<Vec<u8>, ServiceError> {
        self.kernel
            .signer()
            .sign(self.kernel.key_id(), statement)
            .map(|signature| signature.to_vec())
            .map_err(|error| ServiceError::Signing(error.to_string()))
    }
}

/// Requester state before endpoint acceptance has been checked.
pub struct SessionInitiator {
    kernel: Kernel,
    endpoint: ServiceIdentity,
    request: SessionRequest,
}

impl SessionInitiator {
    /// Pins and verifies a description, then signs one fresh session request.
    ///
    /// # Errors
    ///
    /// Rejects a description which does not match `expected` or whose
    /// self-signature is invalid.
    pub fn begin(
        expected: ServiceIdentity,
        description: &EndpointDescription,
    ) -> Result<Self, ServiceError> {
        if description.identity != expected {
            return Err(ServiceError::Invalid(
                "described endpoint is not pinned endpoint",
            ));
        }
        expected
            .verifier()?
            .verify(
                expected.signer,
                description.statement(),
                &description.signature,
            )
            .map_err(|error| ServiceError::Verification(error.to_string()))?;
        let kernel = Kernel::ephemeral();
        let requester = ServiceIdentity::new(kernel.key_id(), *kernel.verifying_key().as_bytes())?;
        let nonce = covalence_lib_rand::random::<[u8; 32]>();
        let mut request = SessionRequest {
            endpoint: expected,
            requester,
            challenge: description.challenge,
            nonce,
            signature: Vec::new(),
        };
        request.signature = kernel
            .signer()
            .sign(requester.signer, request.statement())
            .map_err(|error| ServiceError::Signing(error.to_string()))?
            .to_vec();
        Ok(Self {
            kernel,
            endpoint: expected,
            request,
        })
    }

    /// Returns the requester-signed handshake message.
    #[must_use]
    pub const fn request(&self) -> &SessionRequest {
        &self.request
    }

    /// Verifies endpoint acceptance and enters a command session.
    ///
    /// # Errors
    ///
    /// Rejects any acceptance not bound to this exact handshake.
    pub fn accept(self, accepted: &SessionAccepted) -> Result<SignedServiceSession, ServiceError> {
        if accepted.endpoint != self.endpoint
            || accepted.requester != self.request.requester
            || accepted.request_statement != self.request.statement()
        {
            return Err(ServiceError::Invalid("session acceptance is misbound"));
        }
        self.endpoint
            .verifier()?
            .verify(
                self.endpoint.signer,
                accepted.statement(),
                &accepted.signature,
            )
            .map_err(|error| ServiceError::Verification(error.to_string()))?;
        Ok(SignedServiceSession {
            kernel: self.kernel,
            endpoint: self.endpoint,
            requester: self.request.requester,
            session: accepted.session,
            next_sequence: 0,
            pending: None,
        })
    }
}

/// Client capability for one mutually authenticated, sequenced session.
pub struct SignedServiceSession {
    kernel: Kernel,
    endpoint: ServiceIdentity,
    requester: ServiceIdentity,
    session: O256,
    next_sequence: u64,
    pending: Option<PendingCommand>,
}

struct PendingCommand {
    sequence: u64,
    request_id: O256,
    statement: O256,
}

impl SignedServiceSession {
    /// Signs the next command with a fresh request ID.
    ///
    /// The sequence advances only after [`Self::accept_reply`] verifies an
    /// endpoint-signed response bound to this command.
    ///
    /// # Errors
    ///
    /// Returns an error if signing unexpectedly fails.
    pub fn command(
        &mut self,
        operation: ServiceOperation,
    ) -> Result<SignedServiceCommand, ServiceError> {
        if self.pending.is_some() {
            return Err(ServiceError::Invalid(
                "a service command is already awaiting a reply",
            ));
        }
        if self.next_sequence == u64::MAX {
            return Err(ServiceError::Invalid("command sequence exhausted"));
        }
        let request_id = O256::from_bytes(covalence_lib_rand::random::<[u8; 32]>());
        let statement = command_statement(
            self.session,
            self.next_sequence,
            request_id,
            self.requester.signer,
            &operation,
        );
        let signature = self
            .kernel
            .signer()
            .sign(self.requester.signer, statement)
            .map_err(|error| ServiceError::Signing(error.to_string()))?
            .to_vec();
        let command = SignedServiceCommand {
            session: self.session,
            sequence: self.next_sequence,
            request_id,
            requester: self.requester.signer,
            operation,
            statement,
            signature,
        };
        self.pending = Some(PendingCommand {
            sequence: command.sequence,
            request_id: command.request_id,
            statement: command.statement,
        });
        Ok(command)
    }

    /// Verifies request/result binding and advances the sequence.
    ///
    /// # Errors
    ///
    /// Rejects an invalid endpoint signature, another request's response, or
    /// result bytes inconsistent with the signed digest.
    pub fn accept_reply(
        &mut self,
        command: &SignedServiceCommand,
        reply: SignedServiceReply,
    ) -> Result<ServiceResult, ServiceError> {
        let Some(pending) = &self.pending else {
            return Err(ServiceError::Invalid(
                "no service command is awaiting a reply",
            ));
        };
        if command.session != self.session
            || command.sequence != self.next_sequence
            || pending.sequence != command.sequence
            || pending.request_id != command.request_id
            || pending.statement != command.statement
        {
            return Err(ServiceError::Invalid(
                "command is not pending in this session",
            ));
        }
        if reply.session != command.session
            || reply.sequence != command.sequence
            || reply.request_id != command.request_id
            || reply.request_statement != command.statement
            || reply.endpoint != self.endpoint.signer
        {
            return Err(ServiceError::Invalid(
                "reply is not bound to pending command",
            ));
        }
        if reply.result_digest != service_result_digest(&reply.result) {
            return Err(ServiceError::Invalid("reply result digest is incoherent"));
        }
        self.endpoint
            .verifier()?
            .verify(self.endpoint.signer, reply.statement(), &reply.signature)
            .map_err(|error| ServiceError::Verification(error.to_string()))?;
        self.pending = None;
        if !matches!(reply.result, ServiceResult::Rejected(_)) {
            self.next_sequence = self
                .next_sequence
                .checked_add(1)
                .ok_or(ServiceError::Invalid("command sequence exhausted"))?;
        }
        Ok(reply.result)
    }
}

/// Failure of the signed service contract.
#[derive(Debug)]
pub enum ServiceError {
    /// A message is structurally or relationally invalid.
    Invalid(&'static str),
    /// A signing capability failed.
    Signing(String),
    /// A signature failed verification.
    Verification(String),
}

impl fmt::Display for ServiceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Invalid(message) => formatter.write_str(message),
            Self::Signing(message) => {
                write!(formatter, "could not sign service message: {message}")
            }
            Self::Verification(message) => {
                write!(formatter, "could not verify service message: {message}")
            }
        }
    }
}

impl StdError for ServiceError {}

fn description_statement(identity: ServiceIdentity, challenge: &[u8; 32]) -> O256 {
    digest(
        b"description",
        &[identity.signer.as_ref(), &identity.public_key, challenge],
    )
}

fn session_request_statement(
    endpoint: ServiceIdentity,
    requester: ServiceIdentity,
    challenge: &[u8; 32],
    nonce: &[u8; 32],
) -> O256 {
    digest(
        b"session-request",
        &[
            endpoint.signer.as_ref(),
            &endpoint.public_key,
            requester.signer.as_ref(),
            &requester.public_key,
            challenge,
            nonce,
        ],
    )
}

fn session_accepted_statement(
    session: O256,
    endpoint: ServiceIdentity,
    requester: ServiceIdentity,
    request_statement: O256,
) -> O256 {
    digest(
        b"session-accepted",
        &[
            session.as_ref(),
            endpoint.signer.as_ref(),
            requester.signer.as_ref(),
            request_statement.as_ref(),
        ],
    )
}

fn command_statement(
    session: O256,
    sequence: u64,
    request_id: O256,
    requester: O256,
    operation: &ServiceOperation,
) -> O256 {
    let operation = operation_digest(operation);
    digest(
        b"command",
        &[
            session.as_ref(),
            &sequence.to_be_bytes(),
            request_id.as_ref(),
            requester.as_ref(),
            operation.as_ref(),
        ],
    )
}

fn reply_statement(
    session: O256,
    sequence: u64,
    request_id: O256,
    request_statement: O256,
    result_digest: O256,
) -> O256 {
    digest(
        b"reply",
        &[
            session.as_ref(),
            &sequence.to_be_bytes(),
            request_id.as_ref(),
            request_statement.as_ref(),
            result_digest.as_ref(),
        ],
    )
}

fn operation_digest(operation: &ServiceOperation) -> O256 {
    match operation {
        ServiceOperation::OpenHol => digest(b"operation-open-hol", &[]),
        ServiceOperation::CloseHol(connection) => {
            digest(b"operation-close-hol", &[&connection.to_be_bytes()])
        }
        ServiceOperation::ProduceSignedHol(connection) => digest(
            b"operation-produce-signed-hol",
            &[&connection.to_be_bytes()],
        ),
        ServiceOperation::ReceiveSignedHol {
            connection,
            expected,
            artifact,
        } => {
            let artifact = artifact_digest(artifact);
            digest(
                b"operation-receive-signed-hol",
                &[
                    &connection.to_be_bytes(),
                    &expected.kernel().get().to_be_bytes(),
                    expected.signer().as_ref(),
                    expected.public_key(),
                    artifact.as_ref(),
                ],
            )
        }
        ServiceOperation::Shutdown => digest(b"operation-shutdown", &[]),
        ServiceOperation::RunHolProofComponent(component) => {
            digest(b"operation-run-hol-proof-component", &[component.as_ref()])
        }
    }
}

fn service_result_digest(result: &ServiceResult) -> O256 {
    match result {
        ServiceResult::Opened(connection) => digest(b"result-opened", &[&connection.to_be_bytes()]),
        ServiceResult::Closed => digest(b"result-closed", &[]),
        ServiceResult::Produced(produced) => {
            let artifact = artifact_digest(produced.artifact());
            digest(
                b"result-produced",
                &[produced.statement.as_bytes(), artifact.as_ref()],
            )
        }
        ServiceResult::Received(received) => digest(
            b"result-received",
            &[
                &received.import.to_be_bytes(),
                &received.namespace.to_be_bytes(),
                &received.context.to_be_bytes(),
                &received.conclusion.to_be_bytes(),
            ],
        ),
        ServiceResult::ProducedByComponent(produced) => {
            let artifact = artifact_digest(produced.artifact());
            digest(
                b"result-produced-by-hol-proof-component",
                &[produced.component.as_ref(), artifact.as_ref()],
            )
        }
        ServiceResult::Goodbye => digest(b"result-goodbye", &[]),
        ServiceResult::OperationError(message) => {
            digest(b"result-operation-error", &[message.as_bytes()])
        }
        ServiceResult::Rejected(message) => digest(b"result-rejected", &[message.as_bytes()]),
    }
}

fn artifact_digest(artifact: &SignedHolArtifact) -> O256 {
    let actual_image = O256::from_bytes(artifact.image());
    digest(
        b"signed-hol-artifact",
        &[
            &artifact.namespace_id().to_be_bytes(),
            actual_image.as_ref(),
            artifact.schema().as_ref(),
            artifact.image_hash().as_ref(),
            artifact.signer().as_ref(),
            artifact.public_key(),
            artifact.signature(),
        ],
    )
}

fn digest(domain: &[u8], fields: &[&[u8]]) -> O256 {
    let mut bytes = Vec::with_capacity(
        domain.len() + fields.iter().map(|field| 8 + field.len()).sum::<usize>(),
    );
    bytes.extend_from_slice(&(domain.len() as u64).to_be_bytes());
    bytes.extend_from_slice(domain);
    for field in fields {
        bytes.extend_from_slice(&(field.len() as u64).to_be_bytes());
        bytes.extend_from_slice(field);
    }
    signed_kernel_service_schema().tag(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::KernelId;

    #[test]
    fn service_schema_is_the_exact_normative_spec() {
        assert_eq!(
            signed_kernel_service_schema(),
            O256::from_hex("ad2989da210262051d1191149e2b64bb20a8884b78c88f1e1d36130760276b1d")
                .unwrap()
        );
        assert_ne!(
            signed_kernel_service_schema(),
            O256::from_bytes(b"covalence signed kernel service semantics v0\nchanged")
        );
    }

    #[test]
    fn canonical_statement_vectors_are_stable() {
        let endpoint_key = [1; 32];
        let requester_key = [2; 32];
        let endpoint = ServiceIdentity::new(ed25519_key_id(&endpoint_key), endpoint_key).unwrap();
        let requester =
            ServiceIdentity::new(ed25519_key_id(&requester_key), requester_key).unwrap();
        let challenge = [3; 32];
        let nonce = [4; 32];
        let description = description_statement(endpoint, &challenge);
        let request = session_request_statement(endpoint, requester, &challenge, &nonce);
        let session = digest(b"session", &[request.as_ref(), &7_u64.to_be_bytes()]);
        let acceptance = session_accepted_statement(session, endpoint, requester, request);
        let expected =
            ExpectedKernelIdentity::from_public_key(KernelId::from_u32(9), &endpoint_key).unwrap();
        let schema = O256::from_bytes(b"artifact-schema");
        let image_hash = O256::from_bytes(b"image");
        let artifact = SignedHolArtifact::from_untrusted_parts(
            3,
            b"image".to_vec(),
            &schema.to_string(),
            &image_hash.to_string(),
            &endpoint.signer.to_string(),
            endpoint_key.to_vec(),
            vec![5; 64],
        )
        .unwrap();
        let operation = ServiceOperation::ReceiveSignedHol {
            connection: 11,
            expected,
            artifact: Box::new(artifact.clone()),
        };
        let request_id = O256::from_bytes(b"request-id");
        let command = command_statement(session, 13, request_id, requester.signer, &operation);
        let produced =
            service_result_digest(&ServiceResult::Produced(Box::new(ServiceProducedHol {
                statement: "proof".to_owned(),
                artifact,
            })));
        let received = service_result_digest(&ServiceResult::Received(ServiceReceivedHol {
            import: 17,
            namespace: 19,
            context: 23,
            conclusion: 29,
        }));
        let error = service_result_digest(&ServiceResult::OperationError("failed".to_owned()));
        let vectors = [
            (
                description,
                "377d6de7a517ce1f5806ca78560852bbf2d3847614ea16e38b240033acf7c5c7",
            ),
            (
                request,
                "327791f2631bfbf3e751984eb7c9a89f4da4a42e413a8bb9b2bc417b9e7d9de2",
            ),
            (
                session,
                "b0f69fe0befa4c8b4fcf2214fe9c84b399598d0603273a361afed3a7734575d0",
            ),
            (
                acceptance,
                "3ea171a6654445048a26dcd3aade7e76458cdcf2ccdacc3be9ec34f999bebcc6",
            ),
            (
                operation_digest(&operation),
                "a86b4feecfb04d5565756f5b5a1b8144ef02e60534253d9e0b835f6e33aafb3c",
            ),
            (
                command,
                "576178263468b7188c41d944dbe16ce75078c214dba1bb7ad9f0633a6939e7f2",
            ),
            (
                produced,
                "27d2ee48274ef01ae747ce34507dac6f3ddf53e0753cd2b4f86c9ac752ce992d",
            ),
            (
                received,
                "3eb74333719674f4bcff60a1633bb0d0d75b6e31cb71ce52fc1614c0422a0ffc",
            ),
            (
                error,
                "c23e90afb8ed99060aa8c76003a2c87803eb019e665ed4d42593a949e16a6fbc",
            ),
            (
                reply_statement(session, 13, request_id, command, produced),
                "e7ae294c14f7fb790675a7f4aa7693e7d8947d6dbc75cc18b1d13143654ccfcb",
            ),
            (
                reply_statement(session, 13, request_id, command, received),
                "9f810aebbe48ee18baad94a5851272c72c662e277cb0f5eb1a054ac13901f566",
            ),
            (
                reply_statement(session, 13, request_id, command, error),
                "dac268e67ecbfd9f7cce56b4fec19c709a28e59dafeb9b87d4727e9b80673769",
            ),
        ];
        for (actual, expected) in vectors {
            assert_eq!(actual, O256::from_hex(expected).unwrap());
        }
    }

    fn establish_session(
        service: &mut SignedKernelService,
    ) -> (SignedServiceSession, SessionRequest) {
        let description = service.description().clone();
        let initiator =
            SessionInitiator::begin(description.identity(), &description).expect("begin session");
        let request = initiator.request().clone();
        let accepted = service.open_session(&request).expect("open session");
        let session = initiator.accept(&accepted).expect("accept session");
        (session, request)
    }

    fn accepted(
        service: &mut SignedKernelService,
        session: &mut SignedServiceSession,
        operation: ServiceOperation,
    ) -> ServiceResult {
        let command = session.command(operation).expect("sign command");
        let reply = service.execute(&command).expect("sign reply");
        session.accept_reply(&command, reply).expect("verify reply")
    }

    #[test]
    fn signs_a_complete_producer_lifecycle() {
        let mut service = SignedKernelService::new().unwrap();
        let (mut session, _) = establish_session(&mut service);
        let ServiceResult::Opened(connection) =
            accepted(&mut service, &mut session, ServiceOperation::OpenHol)
        else {
            panic!("expected opened connection");
        };
        let ServiceResult::Produced(produced) = accepted(
            &mut service,
            &mut session,
            ServiceOperation::ProduceSignedHol(connection),
        ) else {
            panic!("expected signed HOL artifact");
        };
        assert_eq!(produced.statement(), "(lambda x:bool. x) true = true");
        assert_eq!(
            produced.artifact().signer(),
            service.description().identity().signer()
        );
        assert!(matches!(
            accepted(
                &mut service,
                &mut session,
                ServiceOperation::CloseHol(connection)
            ),
            ServiceResult::Closed
        ));
        assert!(matches!(
            accepted(&mut service, &mut session, ServiceOperation::Shutdown),
            ServiceResult::Goodbye
        ));
    }

    #[test]
    fn runs_only_the_locally_allowlisted_component_and_binds_its_artifact() {
        let component = O256::from_bytes(b"operator-selected component");
        let other = O256::from_bytes(b"remote-selected component");
        let mut service = SignedKernelService::new().unwrap();
        service
            .allow_hol_proof_component(component, |kernel| {
                let mut connection = kernel
                    .open_hol(AllowAll)
                    .map_err(|_| "could not open executor HOL connection")?;
                produce_signed_hol_artifact(kernel, &mut connection)
                    .map(|produced| produced.into_parts().1)
                    .map_err(|_| "could not produce executor artifact")
            })
            .unwrap();
        let expected_signer = service.description().identity().signer();
        let (mut session, _) = establish_session(&mut service);

        assert!(matches!(
            accepted(
                &mut service,
                &mut session,
                ServiceOperation::RunHolProofComponent(other),
            ),
            ServiceResult::OperationError(message)
                if message == "HOL proof component is not allowlisted"
        ));
        let ServiceResult::ProducedByComponent(produced) = accepted(
            &mut service,
            &mut session,
            ServiceOperation::RunHolProofComponent(component),
        ) else {
            panic!("expected component artifact");
        };
        assert_eq!(produced.component(), component);
        assert_eq!(produced.artifact().signer(), expected_signer);
    }

    #[test]
    fn component_executor_is_installed_once_before_any_session() {
        let first = O256::from_bytes(b"first component");
        let second = O256::from_bytes(b"second component");
        let mut service = SignedKernelService::new().unwrap();
        service
            .allow_hol_proof_component(first, |_| Err("unused executor"))
            .unwrap();
        assert!(matches!(
            service.allow_hol_proof_component(second, |_| Err("unused executor")),
            Err(ServiceError::Invalid(
                "HOL proof component is already configured"
            ))
        ));

        let mut service = SignedKernelService::new().unwrap();
        let (_, _) = establish_session(&mut service);
        assert!(matches!(
            service.allow_hol_proof_component(first, |_| Err("unused executor")),
            Err(ServiceError::Invalid(
                "HOL proof component must be configured before sessions"
            ))
        ));
    }

    #[test]
    fn attacker_valid_artifact_fails_pin_before_receiver_mutation() {
        let mut service = SignedKernelService::new().unwrap();
        let (mut session, _) = establish_session(&mut service);
        let ServiceResult::Opened(source) =
            accepted(&mut service, &mut session, ServiceOperation::OpenHol)
        else {
            panic!("expected source connection");
        };
        let ServiceResult::Opened(target) =
            accepted(&mut service, &mut session, ServiceOperation::OpenHol)
        else {
            panic!("expected target connection");
        };
        let identity = service.description().identity();
        let expected = ExpectedKernelIdentity::from_untrusted_parts(
            super::super::KernelId::from_u32(1),
            &identity.signer().to_string(),
            &identity.public_key(),
        )
        .unwrap();

        let mut attacker = SignedKernelService::new().unwrap();
        let (mut attacker_session, _) = establish_session(&mut attacker);
        let ServiceResult::Opened(attacker_source) = accepted(
            &mut attacker,
            &mut attacker_session,
            ServiceOperation::OpenHol,
        ) else {
            panic!("expected attacker source");
        };
        let ServiceResult::Produced(attack) = accepted(
            &mut attacker,
            &mut attacker_session,
            ServiceOperation::ProduceSignedHol(attacker_source),
        ) else {
            panic!("expected attacker artifact");
        };
        let rejected = accepted(
            &mut service,
            &mut session,
            ServiceOperation::ReceiveSignedHol {
                connection: target,
                expected: expected.clone(),
                artifact: Box::new(attack.into_artifact()),
            },
        );
        assert!(matches!(
            rejected,
            ServiceResult::OperationError(message) if message.contains("signer-pinned")
        ));

        let ServiceResult::Produced(honest) = accepted(
            &mut service,
            &mut session,
            ServiceOperation::ProduceSignedHol(source),
        ) else {
            panic!("expected honest artifact");
        };
        let ServiceResult::Received(received) = accepted(
            &mut service,
            &mut session,
            ServiceOperation::ReceiveSignedHol {
                connection: target,
                expected,
                artifact: Box::new(honest.into_artifact()),
            },
        ) else {
            panic!("expected pinned receipt");
        };
        assert_eq!(received.import_id(), 0);
        assert_eq!(received.context_id(), 0);
        assert_eq!(received.conclusion_id(), 8);
    }

    #[test]
    fn pins_description_and_rejects_session_replay() {
        let mut service = SignedKernelService::new().unwrap();
        let attacker = SignedKernelService::new().unwrap();
        assert!(
            SessionInitiator::begin(attacker.description().identity(), service.description())
                .is_err()
        );

        let (_session, request) = establish_session(&mut service);
        assert!(service.open_session(&request).is_err());
    }

    #[test]
    fn rejects_payload_and_signature_mutation_before_dispatch() {
        let mut service = SignedKernelService::new().unwrap();
        let (mut session, _) = establish_session(&mut service);
        let command = session.command(ServiceOperation::OpenHol).unwrap();

        let mut changed_operation = command.clone();
        changed_operation.operation = ServiceOperation::CloseHol(44);
        let reply = service.execute(&changed_operation).unwrap();
        assert!(matches!(reply.result, ServiceResult::Rejected(_)));

        let mut changed_signature = command.clone();
        changed_signature.signature[0] ^= 1;
        let reply = service.execute(&changed_signature).unwrap();
        assert!(matches!(reply.result, ServiceResult::Rejected(_)));

        let mut changed_request_id = command.clone();
        changed_request_id.request_id = O256::from_bytes(b"misrouted request");
        let reply = service.execute(&changed_request_id).unwrap();
        assert!(matches!(reply.result, ServiceResult::Rejected(_)));

        let reply = service.execute(&command).unwrap();
        assert!(matches!(
            session.accept_reply(&command, reply).unwrap(),
            ServiceResult::Opened(1)
        ));
    }

    #[test]
    fn attacker_key_cannot_command_another_session() {
        let mut service = SignedKernelService::new().unwrap();
        let (mut honest, _) = establish_session(&mut service);
        let mut other_service = SignedKernelService::new().unwrap();
        let (mut attacker, _) = establish_session(&mut other_service);
        let mut forged = attacker.command(ServiceOperation::OpenHol).unwrap();
        forged.session = honest.session;
        forged.sequence = 0;
        forged.statement = command_statement(
            forged.session,
            forged.sequence,
            forged.request_id,
            forged.requester,
            &forged.operation,
        );
        forged.signature = attacker
            .kernel
            .signer()
            .sign(attacker.requester.signer, forged.statement)
            .unwrap()
            .to_vec();
        assert!(matches!(
            service.execute(&forged).unwrap().result,
            ServiceResult::Rejected(_)
        ));
        assert!(matches!(
            accepted(&mut service, &mut honest, ServiceOperation::OpenHol),
            ServiceResult::Opened(1)
        ));
    }

    #[test]
    fn rejects_gap_and_recovers_an_exact_lost_reply_without_redispatch() {
        let mut service = SignedKernelService::new().unwrap();
        let (mut session, _) = establish_session(&mut service);
        let command = session.command(ServiceOperation::OpenHol).unwrap();

        let mut gap = command.clone();
        gap.sequence = 1;
        gap.statement = command_statement(
            gap.session,
            gap.sequence,
            gap.request_id,
            gap.requester,
            &gap.operation,
        );
        gap.signature = session
            .kernel
            .signer()
            .sign(session.requester.signer, gap.statement)
            .unwrap()
            .to_vec();
        assert!(matches!(
            service.execute(&gap).unwrap().result,
            ServiceResult::Rejected(_)
        ));

        let lost_reply = service.execute(&command).unwrap();
        let retry_reply = service.execute(&command).unwrap();
        assert!(matches!(
            session.accept_reply(&command, retry_reply).unwrap(),
            ServiceResult::Opened(1)
        ));
        assert!(matches!(
            service.execute(&command).unwrap().result,
            ServiceResult::Opened(1)
        ));
        assert_eq!(
            lost_reply.statement(),
            service.execute(&command).unwrap().statement()
        );
        assert!(matches!(
            accepted(&mut service, &mut session, ServiceOperation::OpenHol),
            ServiceResult::Opened(2)
        ));
    }

    #[test]
    fn rejects_misrouted_and_mutated_replies() {
        let mut service = SignedKernelService::new().unwrap();
        let (mut first_session, _) = establish_session(&mut service);
        let (mut second_session, _) = establish_session(&mut service);
        let first_command = first_session.command(ServiceOperation::OpenHol).unwrap();
        let second_command = second_session.command(ServiceOperation::OpenHol).unwrap();
        let reply = service.execute(&first_command).unwrap();
        assert!(
            second_session
                .accept_reply(&second_command, reply.clone())
                .is_err()
        );
        assert!(matches!(
            first_session.accept_reply(&first_command, reply).unwrap(),
            ServiceResult::Opened(1)
        ));

        // The failed client-side check did not advance its sequence. A fresh
        // session gives us another authentic reply whose signed result is then
        // changed without updating its digest or signature.
        let mut second = SignedKernelService::new().unwrap();
        let (mut second_session, _) = establish_session(&mut second);
        let second_command = second_session.command(ServiceOperation::OpenHol).unwrap();
        let mut changed = second.execute(&second_command).unwrap();
        changed.result = ServiceResult::Opened(99);
        assert!(
            second_session
                .accept_reply(&second_command, changed)
                .is_err()
        );

        let mut third = SignedKernelService::new().unwrap();
        let (mut third_session, _) = establish_session(&mut third);
        let third_command = third_session.command(ServiceOperation::OpenHol).unwrap();
        let mut bad_signature = third.execute(&third_command).unwrap();
        bad_signature.signature[0] ^= 1;
        assert!(
            third_session
                .accept_reply(&third_command, bad_signature)
                .is_err()
        );
    }
}
