use covalence_lib_hash::O256;
use wasm_bindgen::prelude::*;

use super::{
    ConnectionId, ContextId, ExportId, KernelId, Kind, KindId, KindView, LocalImportedHolExport,
    LocalImportedHolTerm, LocalImportedHolValue, LocalRepl, LocalSignedHolSnapshot,
    LocalTrustedHolImport, NamespaceExport, NamespaceId, NamespaceView, Outcome, ProofError,
    QueryResult, ReplOperation, ReplOperationOutput, ReplOperationProgress, TermId, TermView,
    TrustedImportId, TypeId, TypeView, Value, compile_hol_schema_json,
};

/// Browser adapter for the shared REPL connection directory.
#[wasm_bindgen]
pub struct WebKernel {
    repl: LocalRepl,
}

/// Owned result of one statement executed by [`WebKernel`].
#[wasm_bindgen]
pub struct WebOutcome {
    outcome: Outcome,
}

/// One linear signed REPL operation waiting for transport.
///
/// JavaScript may inspect the destination and copy the opaque request bytes, but only Rust can
/// interpret or complete the operation. The value must be consumed exactly once by
/// [`WebKernel::accept_operation_result`] or [`WebKernel::abandon_operation`].
#[wasm_bindgen]
pub struct WebPendingReplOperation {
    operation: Option<super::PendingReplOperation>,
}

/// Rust-owned progress after accepting one transported operation result.
#[wasm_bindgen]
pub struct WebReplOperationProgress {
    value: Option<WebReplOperationProgressValue>,
}

enum WebReplOperationProgressValue {
    Complete(WebReplOperationOutput),
    Dispatch(Box<WebPendingReplOperation>),
    Failed { error: String, invalidated: bool },
}

/// Typed final result of one transported SQL/image operation.
#[wasm_bindgen]
pub struct WebReplOperationOutput {
    output: Option<ReplOperationOutput>,
}

/// Owned view of one admitted HOL kind.
#[wasm_bindgen]
pub struct WebKind {
    kind: KindView,
}

/// Owned view of one admitted HOL type.
#[wasm_bindgen]
pub struct WebType {
    ty: TypeView,
}

/// Owned view of one admitted HOL term.
#[wasm_bindgen]
pub struct WebTerm {
    term: TermView,
}

/// Owned view of one local HOL namespace.
#[wasm_bindgen]
pub struct WebNamespace {
    namespace: NamespaceView,
}

/// Owned view of one local HOL namespace export.
#[wasm_bindgen]
pub struct WebExport {
    sort: &'static str,
    local: i64,
    name: Option<String>,
}

/// Owned signed HOL image and verification envelope.
#[wasm_bindgen]
pub struct WebSignedHolSnapshot {
    snapshot: LocalSignedHolSnapshot,
}

/// Owned view of one persistent hash-first trusted-import assumption.
#[wasm_bindgen]
pub struct WebTrustedHolImport {
    trusted: LocalTrustedHolImport,
}

/// Owned structural export copied from one scoped immutable imported-image reader.
#[wasm_bindgen]
pub struct WebImportedHolExport {
    value: LocalImportedHolExport,
}

#[wasm_bindgen]
impl WebKernel {
    /// Creates a browser REPL with its own raw SQLite state database.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error if the state database cannot be opened.
    #[wasm_bindgen(constructor)]
    pub fn new() -> Result<WebKernel, JsValue> {
        LocalRepl::new().map(|repl| Self { repl }).map_err(js_error)
    }

    /// Returns the ephemeral controller public key which a remote grant must name as caller.
    #[must_use]
    pub fn controller_caller_key(&self) -> Vec<u8> {
        self.repl.remote_caller_public_key().to_vec()
    }

    /// Verifies a recipient-signed channel grant and records its transport-neutral route.
    ///
    /// `pinned_recipient` is an out-of-band identity pin. The descriptive transport and endpoint
    /// confer no authority, and no directory entry is created until the grant is authenticated.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for a non-32-byte identity, malformed or mismatched grant, an
    /// existing route, or a failed directory update.
    #[allow(clippy::needless_pass_by_value)]
    pub fn accept_remote_grant(
        &mut self,
        transport: &str,
        endpoint: Option<String>,
        pinned_recipient: &[u8],
        grant: &[u8],
    ) -> Result<u32, JsValue> {
        let pinned_recipient = pinned_recipient
            .try_into()
            .map_err(|_| JsValue::from_str("Ed25519 public key must contain exactly 32 bytes"))?;
        let id = self
            .repl
            .accept_remote_kernel(transport, endpoint.as_deref(), pinned_recipient, grant)
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Begins opening an in-memory raw SQL connection on `kernel` without performing transport.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error when the kernel route cannot prepare the signed operation.
    pub fn begin_open_sql(&mut self, kernel: u32) -> Result<WebPendingReplOperation, JsValue> {
        self.begin_operation(ReplOperation::OpenSql {
            kernel: KernelId::from_u32(kernel),
        })
    }

    /// Begins closing a managed raw SQL connection without performing transport.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for an unknown or wrong-protocol connection, or when its kernel
    /// route cannot prepare the signed operation.
    pub fn begin_close_sql(&mut self, connection: u32) -> Result<WebPendingReplOperation, JsValue> {
        self.begin_operation(ReplOperation::CloseSql {
            connection: ConnectionId::from_u32(connection),
        })
    }

    /// Begins executing one complete parameterless SQL statement without performing transport.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for an invalid statement, unknown or wrong-protocol connection,
    /// or unavailable kernel route.
    pub fn begin_run_sql(
        &mut self,
        connection: u32,
        sql: String,
    ) -> Result<WebPendingReplOperation, JsValue> {
        self.begin_operation(ReplOperation::RunSql {
            connection: ConnectionId::from_u32(connection),
            sql,
        })
    }

    /// Begins admitting one complete immutable image to a connection's kernel without transport.
    ///
    /// The expected operational address is computed inside Rust and checked again against the
    /// signed kernel result before local residency is recorded.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for an unknown connection, oversized image, or unavailable
    /// kernel route.
    pub fn begin_put_image(
        &mut self,
        connection: u32,
        bytes: Vec<u8>,
    ) -> Result<WebPendingReplOperation, JsValue> {
        let kernel = self
            .repl
            .directory
            .connection_kernel(ConnectionId::from_u32(connection))
            .map_err(js_error)?;
        let expected = O256::from_bytes(&bytes);
        self.begin_operation(ReplOperation::PutImage {
            kernel,
            expected,
            bytes,
        })
    }

    /// Begins checking whether an exact immutable image is resident on `kernel`.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for an invalid image address or unavailable kernel route.
    pub fn begin_has_image(
        &mut self,
        kernel: u32,
        image: &str,
    ) -> Result<WebPendingReplOperation, JsValue> {
        self.begin_operation(ReplOperation::HasImage {
            kernel: KernelId::from_u32(kernel),
            image: O256::from_hex(image).map_err(js_error)?,
        })
    }

    /// Begins attaching a resident immutable image to a managed raw SQL connection.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for an invalid image address, schema or connection, or an
    /// unavailable kernel route.
    pub fn begin_attach_image(
        &mut self,
        connection: u32,
        image: &str,
        schema: String,
    ) -> Result<WebPendingReplOperation, JsValue> {
        self.begin_operation(ReplOperation::AttachImage {
            connection: ConnectionId::from_u32(connection),
            image: O256::from_hex(image).map_err(js_error)?,
            schema,
        })
    }

    /// Begins serializing a managed raw SQL connection's writable `main` database.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for an unknown or wrong-protocol connection, or an unavailable
    /// kernel route.
    pub fn begin_serialize_main(
        &mut self,
        connection: u32,
    ) -> Result<WebPendingReplOperation, JsValue> {
        self.begin_operation(ReplOperation::SerializeMain {
            connection: ConnectionId::from_u32(connection),
        })
    }

    /// Authenticates one exact result and performs the operation's Rust-owned finalization.
    ///
    /// A `dispatch` progress value contains a signed close compensation which must itself be sent
    /// exactly once. JavaScript must never retry either request after an ambiguous failure.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error only if the pending value was already consumed. Authenticated
    /// operation failures and signed-route invalidation are returned as distinct progress kinds.
    pub fn accept_operation_result(
        &mut self,
        operation: &mut WebPendingReplOperation,
        result: &[u8],
    ) -> Result<WebReplOperationProgress, JsValue> {
        let operation = operation.take()?;
        match self.repl.accept_operation_result(operation, result) {
            ReplOperationProgress::Complete(Ok(output)) => {
                Ok(WebReplOperationProgress::complete(output))
            }
            ReplOperationProgress::Complete(Err(error)) => {
                Ok(WebReplOperationProgress::failed(error.to_string(), false))
            }
            ReplOperationProgress::Invalidated(error) => {
                Ok(WebReplOperationProgress::failed(error.to_string(), true))
            }
            ReplOperationProgress::Dispatch(operation) => {
                Ok(WebReplOperationProgress::dispatch(*operation))
            }
        }
    }

    /// Abandons an ambiguously transported operation and poisons its signed route.
    ///
    /// The request bytes must not be retried. For a close compensation this reports the original
    /// local commit failure which caused compensation.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error if the pending value was already consumed or represents a
    /// compensation whose original operation failed locally.
    pub fn abandon_operation(
        &mut self,
        operation: &mut WebPendingReplOperation,
    ) -> Result<(), JsValue> {
        let operation = operation.take()?;
        self.repl
            .abandon_operation(operation)
            .map_or(Ok(()), |error| Err(js_error(error)))
    }

    /// Opens a writable in-memory SQL connection and returns its local ID.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error when the connection or directory row cannot
    /// be opened.
    pub fn open_connection(&mut self) -> Result<u32, JsValue> {
        let id = self.repl.open_sql().map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Creates another independently keyed in-Worker kernel.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error if its identity cannot be recorded.
    pub fn create_local_kernel(&mut self) -> Result<u32, JsValue> {
        let id = self.repl.create_local_kernel().map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Lists authoritative live local kernel IDs.
    pub fn kernel_ids(&self) -> Result<Vec<u32>, JsValue> {
        self.repl
            .kernels()
            .into_iter()
            .map(|(id, _)| u32::try_from(id.get()).map_err(js_error))
            .collect()
    }

    /// Returns one kernel's exact public key.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for an unknown kernel.
    pub fn kernel_public_key(&self, kernel: u32) -> Result<Vec<u8>, JsValue> {
        self.repl
            .kernel(KernelId::from_u32(kernel))
            .map(|view| view.public_key.to_vec())
            .map_err(js_error)
    }

    /// Returns one kernel's transport label.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for an unknown kernel.
    pub fn kernel_transport(&self, kernel: u32) -> Result<String, JsValue> {
        self.repl
            .kernel(KernelId::from_u32(kernel))
            .map(|view| view.transport)
            .map_err(js_error)
    }

    /// Returns one kernel's optional transport endpoint.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for an unknown kernel.
    pub fn kernel_endpoint(&self, kernel: u32) -> Result<Option<String>, JsValue> {
        self.repl
            .kernel(KernelId::from_u32(kernel))
            .map(|view| view.endpoint)
            .map_err(js_error)
    }

    /// Opens a writable in-memory SQL connection on one local kernel.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for an unknown kernel or connection-opening failure.
    pub fn open_connection_on(&mut self, kernel: u32) -> Result<u32, JsValue> {
        let id = self
            .repl
            .open_sql_on(KernelId::from_u32(kernel))
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Opens a policy-enclosed HOL-omega connection and returns its local ID.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error when the connection/schema or directory row
    /// cannot be opened.
    pub fn open_hol_connection(&mut self) -> Result<u32, JsValue> {
        let id = self.repl.open_hol().map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Opens a policy-enclosed HOL-omega connection on one local kernel.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for an unknown kernel or connection-opening failure.
    pub fn open_hol_connection_on(&mut self, kernel: u32) -> Result<u32, JsValue> {
        let id = self
            .repl
            .open_hol_on(KernelId::from_u32(kernel))
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Opens a policy-enclosed HOL-omega connection from a canonical metadata descriptor.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error when the descriptor or connection/schema cannot be opened.
    pub fn open_hol_connection_with_descriptor(
        &mut self,
        descriptor: &[u8],
    ) -> Result<u32, JsValue> {
        let id = self
            .repl
            .open_hol_with_descriptor(descriptor)
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Opens a policy-enclosed HOL connection with a descriptor on one local kernel.
    pub fn open_hol_connection_with_descriptor_on(
        &mut self,
        kernel: u32,
        descriptor: &[u8],
    ) -> Result<u32, JsValue> {
        let id = self
            .repl
            .open_hol_with_descriptor_on(KernelId::from_u32(kernel), descriptor)
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Opens a policy-enclosed HOL-omega connection from a strict JSON metadata schema.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error when the JSON declaration or connection/schema is invalid.
    pub fn open_hol_connection_with_schema_json(&mut self, json: &str) -> Result<u32, JsValue> {
        let id = self
            .repl
            .open_hol_with_schema_json(json)
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Opens a policy-enclosed HOL connection from schema JSON on one local kernel.
    pub fn open_hol_connection_with_schema_json_on(
        &mut self,
        kernel: u32,
        json: &str,
    ) -> Result<u32, JsValue> {
        let id = self
            .repl
            .open_hol_with_schema_json_on(KernelId::from_u32(kernel), json)
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Compiles strict user-authored JSON into a canonical portable metadata descriptor.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error when the JSON declaration or checked schema is invalid.
    pub fn compile_hol_schema_json(&self, json: &str) -> Result<Vec<u8>, JsValue> {
        compile_hol_schema_json(json)
            .map(|descriptor| descriptor.encode().to_vec())
            .map_err(js_error)
    }

    /// Closes a connection.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for an unknown ID or state update failure.
    pub fn close_connection(&mut self, connection: u32) -> Result<(), JsValue> {
        self.repl
            .close(ConnectionId::from_u32(connection))
            .map_err(js_error)
    }

    /// Runs one parameterless SQL statement.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error when the statement fails.
    pub fn run(&mut self, connection: u32, sql: &str) -> Result<WebOutcome, JsValue> {
        self.repl
            .run_sql(ConnectionId::from_u32(connection), sql)
            .map(|outcome| WebOutcome { outcome })
            .map_err(js_error)
    }

    /// Stores a complete resident database image and returns its address.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error on a resident hash collision.
    pub fn put_image(&mut self, connection: u32, bytes: &[u8]) -> Result<String, JsValue> {
        self.repl
            .put_image_for_connection(ConnectionId::from_u32(connection), bytes)
            .map(|hash| hash.to_string())
            .map_err(js_error)
    }

    /// Authenticates and validates one signed HOL snapshot into the shared REPL cache.
    #[allow(clippy::too_many_arguments)]
    pub fn put_resident_hol_snapshot(
        &mut self,
        bytes: &[u8],
        descriptor: &[u8],
        schema: &str,
        image: &str,
        signer: &str,
        public_key: &[u8],
        signature: &[u8],
    ) -> Result<String, JsValue> {
        let public_key = public_key
            .try_into()
            .map_err(|_| JsValue::from_str("Ed25519 public key must contain exactly 32 bytes"))?;
        self.repl
            .put_signed_hol_snapshot_with_descriptor(
                bytes,
                descriptor,
                O256::from_hex(schema).map_err(js_error)?,
                O256::from_hex(image).map_err(js_error)?,
                O256::from_hex(signer).map_err(js_error)?,
                public_key,
                signature,
            )
            .map(|hash| hash.to_string())
            .map_err(js_error)
    }

    /// Attaches a resident image immutably under `schema`.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for an invalid address or failed attachment,
    /// including a post-attach VFS pointer mismatch.
    pub fn attach_image(
        &mut self,
        connection: u32,
        hash: &str,
        schema: &str,
    ) -> Result<(), JsValue> {
        let hash = O256::from_hex(hash).map_err(js_error)?;
        self.repl
            .attach_image(ConnectionId::from_u32(connection), hash, schema)
            .map_err(js_error)
    }

    /// Serializes the writable in-memory `main` database.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error when SQLite cannot serialize the database.
    pub fn serialize_main(&mut self, connection: u32) -> Result<Vec<u8>, JsValue> {
        self.repl
            .serialize_main(ConnectionId::from_u32(connection))
            .map_err(js_error)
    }

    /// Reads user-declared HOL metadata using the strict shared JSON request format.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for malformed JSON, a wrong connection protocol, or a rejected
    /// metadata read.
    pub fn hol_metadata(&mut self, connection: u32, request: &str) -> Result<String, JsValue> {
        self.repl
            .hol_metadata_json(ConnectionId::from_u32(connection), request)
            .map_err(js_error)
    }

    /// Replaces user-declared HOL metadata using the strict shared JSON request format.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for malformed JSON, a wrong connection protocol, or a rejected
    /// metadata write.
    pub fn set_hol_metadata(&mut self, connection: u32, request: &str) -> Result<(), JsValue> {
        self.repl
            .set_hol_metadata_json(ConnectionId::from_u32(connection), request)
            .map_err(js_error)
    }

    /// Returns the canonical `star` kind ID in a HOL connection.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for an unknown/wrong-protocol connection or
    /// denied/failed HOL admission.
    pub fn hol_star(&mut self, connection: u32) -> Result<u32, JsValue> {
        let id = self
            .repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .insert_kind(&Kind::Star)
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Canonically interns `domain -> codomain` in a HOL connection.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for invalid IDs, protocol mismatch, policy
    /// denial, or failed admission.
    pub fn hol_arrow(
        &mut self,
        connection: u32,
        domain: u32,
        codomain: u32,
    ) -> Result<u32, JsValue> {
        let id = self
            .repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .insert_kind_arrow(
                KindId::from_i64(i64::from(domain)),
                KindId::from_i64(i64::from(codomain)),
            )
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Reads one admitted HOL kind.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for an invalid ID, protocol mismatch, policy
    /// denial, or corrupt/unknown kind.
    pub fn hol_kind(&mut self, connection: u32, kind: u32) -> Result<WebKind, JsValue> {
        self.repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .kind(KindId::from_i64(i64::from(kind)))
            .map(|kind| WebKind { kind })
            .map_err(js_error)
    }

    /// Derives the order rank of one admitted HOL kind.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for invalid IDs, protocol mismatch, policy
    /// denial, malformed nodes, or rank overflow.
    pub fn hol_rank(&mut self, connection: u32, kind: u32) -> Result<u32, JsValue> {
        self.repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .kind_rank(KindId::from_i64(i64::from(kind)))
            .map_err(js_error)
    }

    /// Returns the canonical Boolean type ID.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for connection/policy/admission failure.
    pub fn hol_bool_type(&mut self, connection: u32) -> Result<u32, JsValue> {
        let id = self
            .repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .insert_bool_type()
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Canonically interns a closed function type.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for invalid IDs or failed admission.
    pub fn hol_arrow_type(
        &mut self,
        connection: u32,
        domain: u32,
        codomain: u32,
    ) -> Result<u32, JsValue> {
        let id = self
            .repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .insert_arrow_type(
                TypeId::from_i64(i64::from(domain)),
                TypeId::from_i64(i64::from(codomain)),
            )
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Reads one admitted HOL type.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for invalid IDs or a denied/corrupt read.
    pub fn hol_type(&mut self, connection: u32, ty: u32) -> Result<WebType, JsValue> {
        self.repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .type_view(TypeId::from_i64(i64::from(ty)))
            .map(|ty| WebType { ty })
            .map_err(js_error)
    }

    /// Canonically interns a Boolean term.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for connection/policy/admission failure.
    pub fn hol_bool_term(&mut self, connection: u32, value: bool) -> Result<u32, JsValue> {
        let id = self
            .repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .insert_bool_term(value)
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Canonically interns a closed free symbol with a declared type.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for invalid IDs or failed admission.
    pub fn hol_free_term(&mut self, connection: u32, symbol: u32, ty: u32) -> Result<u32, JsValue> {
        let id = self
            .repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .insert_free_term(i64::from(symbol), TypeId::from_i64(i64::from(ty)))
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Canonically interns an explicitly typed de Bruijn occurrence.
    pub fn hol_bound_term(&mut self, connection: u32, index: u32, ty: u32) -> Result<u32, JsValue> {
        let id = self
            .repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .insert_bound_term(index, TypeId::from_i64(i64::from(ty)))
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Checks and canonically interns a term application.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for invalid IDs, a typing failure, or failed
    /// admission.
    pub fn hol_application(
        &mut self,
        connection: u32,
        function: u32,
        argument: u32,
    ) -> Result<u32, JsValue> {
        let id = self
            .repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .insert_application(
                TermId::from_i64(i64::from(function)),
                TermId::from_i64(i64::from(argument)),
            )
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Checks and canonically interns a typed term abstraction.
    pub fn hol_lambda(
        &mut self,
        connection: u32,
        parameter_type: u32,
        body: u32,
    ) -> Result<u32, JsValue> {
        let id = self
            .repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .insert_lambda(
                TypeId::from_i64(i64::from(parameter_type)),
                TermId::from_i64(i64::from(body)),
            )
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Checks and canonically interns propositional equality.
    pub fn hol_equality(&mut self, connection: u32, left: u32, right: u32) -> Result<u32, JsValue> {
        let id = self
            .repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .insert_equality(
                TermId::from_i64(i64::from(left)),
                TermId::from_i64(i64::from(right)),
            )
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Reads one admitted HOL term.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for invalid IDs or a denied/corrupt read.
    pub fn hol_term(&mut self, connection: u32, term: u32) -> Result<WebTerm, JsValue> {
        self.repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .term(TermId::from_i64(i64::from(term)))
            .map(|term| WebTerm { term })
            .map_err(js_error)
    }

    /// Returns the admitted type ID of a term.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for invalid IDs or a denied/corrupt read.
    pub fn hol_term_type(&mut self, connection: u32, term: u32) -> Result<u32, JsValue> {
        let ty = self
            .repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .term_type(TermId::from_i64(i64::from(term)))
            .map_err(js_error)?;
        u32::try_from(ty.get()).map_err(js_error)
    }

    /// Returns sorted free-symbol IDs reachable from a term.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for invalid IDs, denied/corrupt reads, or a
    /// symbol outside the browser ABI's `u32` range.
    pub fn hol_term_free_variables(
        &mut self,
        connection: u32,
        term: u32,
    ) -> Result<Vec<u32>, JsValue> {
        self.repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .term_free_variables(TermId::from_i64(i64::from(term)))
            .map_err(js_error)?
            .into_iter()
            .map(|symbol| u32::try_from(symbol).map_err(js_error))
            .collect()
    }

    /// Reports whether a term has no external de Bruijn variables.
    pub fn hol_term_is_locally_closed(
        &mut self,
        connection: u32,
        term: u32,
    ) -> Result<bool, JsValue> {
        self.repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .term_is_locally_closed(TermId::from_i64(i64::from(term)))
            .map_err(js_error)
    }

    /// Returns flattened `(index, type)` pairs for external de Bruijn variables.
    pub fn hol_term_unbound_variables(
        &mut self,
        connection: u32,
        term: u32,
    ) -> Result<Vec<u32>, JsValue> {
        let variables = self
            .repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .term_unbound_variables(TermId::from_i64(i64::from(term)))
            .map_err(js_error)?;
        let mut flattened = Vec::with_capacity(variables.len() * 2);
        for variable in variables {
            flattened.push(variable.index);
            flattened.push(u32::try_from(variable.ty.get()).map_err(js_error)?);
        }
        Ok(flattened)
    }

    /// Defines or finds the immutable context containing exactly `members`.
    pub fn hol_define_context(
        &mut self,
        connection: u32,
        members: Vec<u32>,
    ) -> Result<u32, JsValue> {
        let members = members
            .into_iter()
            .map(|term| TermId::from_i64(i64::from(term)))
            .collect::<Vec<_>>();
        let id = self
            .repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .define_context(members)
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Returns the sorted members of an immutable context.
    pub fn hol_context_members(
        &mut self,
        connection: u32,
        context: u32,
    ) -> Result<Vec<u32>, JsValue> {
        self.repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .context_members(ContextId::from_i64(i64::from(context)))
            .map_err(js_error)?
            .into_iter()
            .map(|term| u32::try_from(term.get()).map_err(js_error))
            .collect()
    }

    /// Proves a context member using the HOL hypothesis rule.
    pub fn hol_prove_hypothesis(
        &mut self,
        connection: u32,
        context: u32,
        term: u32,
    ) -> Result<u32, JsValue> {
        let conclusion = self
            .repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .with_proof_session(|mut proof| {
                let theorem = proof.prove_hypothesis(
                    ContextId::from_i64(i64::from(context)),
                    TermId::from_i64(i64::from(term)),
                )?;
                let conclusion = theorem.conclusion();
                proof.persist_theorem(&theorem)?;
                Ok::<_, ProofError>(conclusion)
            })
            .map_err(js_error)?;
        u32::try_from(conclusion.get()).map_err(js_error)
    }

    /// Proves Boolean truth in the selected context.
    pub fn hol_prove_truth(&mut self, connection: u32, context: u32) -> Result<u32, JsValue> {
        let conclusion = self
            .repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .with_proof_session(|mut proof| {
                let theorem = proof.prove_truth(ContextId::from_i64(i64::from(context)))?;
                let conclusion = theorem.conclusion();
                proof.persist_theorem(&theorem)?;
                Ok::<_, ProofError>(conclusion)
            })
            .map_err(js_error)?;
        u32::try_from(conclusion.get()).map_err(js_error)
    }

    /// Proves a closed term equal to itself in the selected context.
    pub fn hol_prove_reflexivity(
        &mut self,
        connection: u32,
        context: u32,
        term: u32,
    ) -> Result<u32, JsValue> {
        let conclusion = self
            .repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .with_proof_session(|mut proof| {
                let theorem = proof.prove_reflexivity(
                    ContextId::from_i64(i64::from(context)),
                    TermId::from_i64(i64::from(term)),
                )?;
                let conclusion = theorem.conclusion();
                proof.persist_theorem(&theorem)?;
                Ok::<_, ProofError>(conclusion)
            })
            .map_err(js_error)?;
        u32::try_from(conclusion.get()).map_err(js_error)
    }

    /// Proves one closed beta reduction in the selected context.
    pub fn hol_prove_beta(
        &mut self,
        connection: u32,
        context: u32,
        abstraction: u32,
        argument: u32,
    ) -> Result<u32, JsValue> {
        let conclusion = self
            .repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .with_proof_session(|mut proof| {
                let theorem = proof.prove_beta(
                    ContextId::from_i64(i64::from(context)),
                    TermId::from_i64(i64::from(abstraction)),
                    TermId::from_i64(i64::from(argument)),
                )?;
                let conclusion = theorem.conclusion();
                proof.persist_theorem(&theorem)?;
                Ok::<_, ProofError>(conclusion)
            })
            .map_err(js_error)?;
        u32::try_from(conclusion.get()).map_err(js_error)
    }

    /// Applies `EqMp` to two exact persisted theorem keys.
    pub fn hol_equality_modus_ponens(
        &mut self,
        connection: u32,
        context: u32,
        equality: u32,
        premise: u32,
    ) -> Result<u32, JsValue> {
        let conclusion = self
            .repl
            .equality_modus_ponens(
                ConnectionId::from_u32(connection),
                ContextId::from_i64(i64::from(context)),
                TermId::from_i64(i64::from(equality)),
                TermId::from_i64(i64::from(premise)),
            )
            .map_err(js_error)?;
        u32::try_from(conclusion.get()).map_err(js_error)
    }

    /// Introduces one exact context implication from persisted witness terms.
    pub fn hol_prove_context_implication(
        &mut self,
        connection: u32,
        antecedent: u32,
        consequent: u32,
        witnesses: Vec<u32>,
    ) -> Result<(), JsValue> {
        let witnesses = witnesses
            .into_iter()
            .map(|term| TermId::from_i64(i64::from(term)))
            .collect::<Vec<_>>();
        self.repl
            .prove_context_implication(
                ConnectionId::from_u32(connection),
                ContextId::from_i64(i64::from(antecedent)),
                ContextId::from_i64(i64::from(consequent)),
                &witnesses,
            )
            .map_err(js_error)
    }

    /// Weakens one exact theorem along one exact context implication.
    pub fn hol_weaken(
        &mut self,
        connection: u32,
        antecedent: u32,
        consequent: u32,
        conclusion: u32,
    ) -> Result<u32, JsValue> {
        let conclusion = self
            .repl
            .weaken(
                ConnectionId::from_u32(connection),
                ContextId::from_i64(i64::from(antecedent)),
                ContextId::from_i64(i64::from(consequent)),
                TermId::from_i64(i64::from(conclusion)),
            )
            .map_err(js_error)?;
        u32::try_from(conclusion.get()).map_err(js_error)
    }

    /// Queries one exact persisted context implication.
    pub fn hol_context_implication_proved(
        &mut self,
        connection: u32,
        antecedent: u32,
        consequent: u32,
    ) -> Result<bool, JsValue> {
        self.repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .proved_context_implication(
                ContextId::from_i64(i64::from(antecedent)),
                ContextId::from_i64(i64::from(consequent)),
            )
            .map_err(js_error)
    }

    /// Queries whether the judgement has already been proved.
    pub fn hol_proved(
        &mut self,
        connection: u32,
        context: u32,
        term: u32,
    ) -> Result<bool, JsValue> {
        self.repl
            .hol_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .proved_judgement(
                ContextId::from_i64(i64::from(context)),
                TermId::from_i64(i64::from(term)),
            )
            .map_err(js_error)
    }

    /// Defines one local HOL namespace.
    pub fn hol_namespace_create(
        &mut self,
        connection: u32,
        parent: Option<u32>,
        name: Option<String>,
    ) -> Result<u32, JsValue> {
        let namespace = self
            .repl
            .create_hol_namespace(
                ConnectionId::from_u32(connection),
                parent.map(|id| NamespaceId::from_i64(i64::from(id))),
                name.as_deref(),
            )
            .map_err(js_error)?;
        u32::try_from(namespace.get()).map_err(js_error)
    }

    /// Reads one local HOL namespace.
    pub fn hol_namespace(
        &mut self,
        connection: u32,
        namespace: u32,
    ) -> Result<WebNamespace, JsValue> {
        self.repl
            .hol_namespace(
                ConnectionId::from_u32(connection),
                NamespaceId::from_i64(i64::from(namespace)),
            )
            .map(|namespace| WebNamespace { namespace })
            .map_err(js_error)
    }

    /// Binds one local HOL value to an explicit namespace-wide export ID.
    pub fn hol_export_bind(
        &mut self,
        connection: u32,
        namespace: u32,
        export: u32,
        sort: &str,
        local: u32,
        name: Option<String>,
    ) -> Result<(), JsValue> {
        let local = i64::from(local);
        let value = match sort {
            "kind" => NamespaceExport::Kind(KindId::from_i64(local)),
            "type" => NamespaceExport::Type(TypeId::from_i64(local)),
            "term" => NamespaceExport::Term(TermId::from_i64(local)),
            "context" => NamespaceExport::Context(ContextId::from_i64(local)),
            _ => return Err(JsValue::from_str("unknown HOL export sort")),
        };
        self.repl
            .bind_hol_export(
                ConnectionId::from_u32(connection),
                NamespaceId::from_i64(i64::from(namespace)),
                ExportId::from_i64(i64::from(export)),
                value,
                name.as_deref(),
            )
            .map_err(js_error)
    }

    /// Reads one local HOL namespace export.
    pub fn hol_export(
        &mut self,
        connection: u32,
        namespace: u32,
        export: u32,
    ) -> Result<WebExport, JsValue> {
        let view = self
            .repl
            .hol_export(
                ConnectionId::from_u32(connection),
                NamespaceId::from_i64(i64::from(namespace)),
                ExportId::from_i64(i64::from(export)),
            )
            .map_err(js_error)?
            .ok_or_else(|| JsValue::from_str("unknown HOL namespace export"))?;
        Ok(WebExport::new(view.value, view.name))
    }

    /// Resolves one namespace-local export name.
    pub fn hol_export_resolve(
        &mut self,
        connection: u32,
        namespace: u32,
        name: &str,
    ) -> Result<Option<u32>, JsValue> {
        self.repl
            .resolve_hol_export_name(
                ConnectionId::from_u32(connection),
                NamespaceId::from_i64(i64::from(namespace)),
                name,
            )
            .map_err(js_error)?
            .map(|(export, _)| u32::try_from(export.get()).map_err(js_error))
            .transpose()
    }

    /// Serializes and signs the complete persistent HOL database.
    pub fn hol_export_snapshot(
        &mut self,
        connection: u32,
    ) -> Result<WebSignedHolSnapshot, JsValue> {
        self.repl
            .export_hol_snapshot(ConnectionId::from_u32(connection))
            .map(|snapshot| WebSignedHolSnapshot { snapshot })
            .map_err(js_error)
    }

    /// Authenticates and persists one hash-first HOL import attestation.
    ///
    /// This operation does not fetch or attach the named database image.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed hashes or key bytes, invalid authentication evidence, a
    /// wrong connection protocol, or rejected trust/import persistence.
    pub fn hol_trust_import(
        &mut self,
        connection: u32,
        schema: &str,
        image: &str,
        signer: &str,
        public_key: &[u8],
        signature: &[u8],
    ) -> Result<WebTrustedHolImport, JsValue> {
        let schema = O256::from_hex(schema).map_err(js_error)?;
        let image = O256::from_hex(image).map_err(js_error)?;
        let signer = O256::from_hex(signer).map_err(js_error)?;
        let public_key = public_key
            .try_into()
            .map_err(|_| JsValue::from_str("Ed25519 public key must contain exactly 32 bytes"))?;
        self.repl
            .trust_hol_import(
                ConnectionId::from_u32(connection),
                schema,
                image,
                signer,
                public_key,
                signature,
            )
            .map(|trusted| WebTrustedHolImport { trusted })
            .map_err(js_error)
    }

    /// Reads one persistent trusted-import assumption.
    ///
    /// # Errors
    ///
    /// Returns an error for a wrong connection protocol, unknown ID, rejected read, or an ID that
    /// cannot be represented by the browser API.
    pub fn hol_trusted_import(
        &mut self,
        connection: u32,
        trusted_import: u32,
    ) -> Result<WebTrustedHolImport, JsValue> {
        self.repl
            .hol_trusted_import(
                ConnectionId::from_u32(connection),
                TrustedImportId::from_i64(i64::from(trusted_import)),
            )
            .map(|trusted| WebTrustedHolImport { trusted })
            .map_err(js_error)
    }

    /// Defines a local alias for one complete namespace in an unfetched import.
    pub fn hol_import_namespace(
        &mut self,
        connection: u32,
        parent: Option<u32>,
        name: Option<String>,
        import: u32,
        source_namespace: u32,
    ) -> Result<u32, JsValue> {
        let namespace = self
            .repl
            .create_hol_imported_namespace(
                ConnectionId::from_u32(connection),
                parent.map(|id| NamespaceId::from_i64(i64::from(id))),
                name.as_deref(),
                super::ImportId::from_i64(i64::from(import)),
                i64::from(source_namespace),
            )
            .map_err(js_error)?;
        u32::try_from(namespace.get()).map_err(js_error)
    }

    /// Authenticates downloaded bytes and structurally inspects one exact trusted namespace export.
    #[allow(clippy::too_many_arguments)]
    pub fn hol_inspect_trusted_export(
        &mut self,
        connection: u32,
        trusted_import: u32,
        bytes: &[u8],
        descriptor: &[u8],
        schema: &str,
        image: &str,
        signer: &str,
        public_key: &[u8],
        signature: &[u8],
        namespace: u32,
        export: u32,
    ) -> Result<Option<WebImportedHolExport>, JsValue> {
        let public_key = public_key
            .try_into()
            .map_err(|_| JsValue::from_str("Ed25519 public key must contain exactly 32 bytes"))?;
        self.repl
            .inspect_trusted_hol_export_with_descriptor(
                ConnectionId::from_u32(connection),
                TrustedImportId::from_i64(i64::from(trusted_import)),
                bytes,
                descriptor,
                O256::from_hex(schema).map_err(js_error)?,
                O256::from_hex(image).map_err(js_error)?,
                O256::from_hex(signer).map_err(js_error)?,
                public_key,
                signature,
                NamespaceId::from_i64(i64::from(namespace)),
                ExportId::from_i64(i64::from(export)),
            )
            .map(|value| value.map(|value| WebImportedHolExport { value }))
            .map_err(js_error)
    }

    /// Authenticates and inspects one exact trusted export from an already-resident image.
    #[allow(clippy::too_many_arguments)]
    pub fn hol_inspect_resident_trusted_export(
        &mut self,
        connection: u32,
        trusted_import: u32,
        image: &str,
        namespace: u32,
        export: u32,
    ) -> Result<Option<WebImportedHolExport>, JsValue> {
        self.repl
            .inspect_resident_trusted_hol_export(
                ConnectionId::from_u32(connection),
                TrustedImportId::from_i64(i64::from(trusted_import)),
                O256::from_hex(image).map_err(js_error)?,
                NamespaceId::from_i64(i64::from(namespace)),
                ExportId::from_i64(i64::from(export)),
            )
            .map(|value| value.map(|value| WebImportedHolExport { value }))
            .map_err(js_error)
    }
}

impl WebKernel {
    fn begin_operation(
        &mut self,
        operation: ReplOperation,
    ) -> Result<WebPendingReplOperation, JsValue> {
        self.repl
            .prepare_operation(operation)
            .map(WebPendingReplOperation::new)
            .map_err(js_error)
    }
}

impl WebPendingReplOperation {
    fn new(operation: super::PendingReplOperation) -> Self {
        Self {
            operation: Some(operation),
        }
    }

    fn take(&mut self) -> Result<super::PendingReplOperation, JsValue> {
        self.operation
            .take()
            .ok_or_else(|| JsValue::from_str("pending REPL operation was already consumed"))
    }
}

#[wasm_bindgen]
impl WebPendingReplOperation {
    /// Returns the kernel directory ID which must receive these bytes.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error after this linear value has been consumed.
    pub fn kernel(&self) -> Result<u32, JsValue> {
        let operation = self
            .operation
            .as_ref()
            .ok_or_else(|| JsValue::from_str("pending REPL operation was already consumed"))?;
        u32::try_from(operation.kernel().get()).map_err(js_error)
    }

    /// Copies the exact canonical signed request bytes for opaque transport.
    ///
    /// The returned bytes may be transported once. They must not be retried after an ambiguous
    /// transport failure.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error after this linear value has been consumed.
    pub fn request_bytes(&self) -> Result<Vec<u8>, JsValue> {
        self.operation
            .as_ref()
            .map(super::PendingReplOperation::encode)
            .ok_or_else(|| JsValue::from_str("pending REPL operation was already consumed"))
    }
}

impl WebReplOperationProgress {
    fn complete(output: ReplOperationOutput) -> Self {
        Self {
            value: Some(WebReplOperationProgressValue::Complete(
                WebReplOperationOutput {
                    output: Some(output),
                },
            )),
        }
    }

    fn dispatch(operation: super::PendingReplOperation) -> Self {
        Self {
            value: Some(WebReplOperationProgressValue::Dispatch(Box::new(
                WebPendingReplOperation::new(operation),
            ))),
        }
    }

    fn failed(error: String, invalidated: bool) -> Self {
        Self {
            value: Some(WebReplOperationProgressValue::Failed { error, invalidated }),
        }
    }
}

#[wasm_bindgen]
impl WebReplOperationProgress {
    /// Returns `complete`, `dispatch`, `error`, or `invalidated`.
    ///
    /// A `dispatch` value is a close compensation and must be transported exactly once before its
    /// result is accepted.
    #[must_use]
    pub fn kind(&self) -> String {
        match self.value {
            Some(WebReplOperationProgressValue::Complete(_)) => "complete",
            Some(WebReplOperationProgressValue::Dispatch(_)) => "dispatch",
            Some(WebReplOperationProgressValue::Failed {
                invalidated: false, ..
            }) => "error",
            Some(WebReplOperationProgressValue::Failed {
                invalidated: true, ..
            }) => "invalidated",
            None => "consumed",
        }
        .to_owned()
    }

    /// Takes the typed final output from a `complete` progress value.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for `dispatch` or after the value was consumed.
    pub fn take_output(&mut self) -> Result<WebReplOperationOutput, JsValue> {
        match self.value.take() {
            Some(WebReplOperationProgressValue::Complete(output)) => Ok(output),
            Some(value @ WebReplOperationProgressValue::Dispatch(_)) => {
                self.value = Some(value);
                Err(JsValue::from_str("operation progress requires dispatch"))
            }
            Some(value @ WebReplOperationProgressValue::Failed { .. }) => {
                self.value = Some(value);
                Err(JsValue::from_str("operation progress contains an error"))
            }
            None => Err(JsValue::from_str("operation progress was already consumed")),
        }
    }

    /// Takes the next linear request from a `dispatch` progress value.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for `complete` or after the value was consumed.
    pub fn take_pending(&mut self) -> Result<WebPendingReplOperation, JsValue> {
        match self.value.take() {
            Some(WebReplOperationProgressValue::Dispatch(operation)) => Ok(*operation),
            Some(value @ WebReplOperationProgressValue::Complete(_)) => {
                self.value = Some(value);
                Err(JsValue::from_str("operation progress is already complete"))
            }
            Some(value @ WebReplOperationProgressValue::Failed { .. }) => {
                self.value = Some(value);
                Err(JsValue::from_str("operation progress contains an error"))
            }
            None => Err(JsValue::from_str("operation progress was already consumed")),
        }
    }

    /// Returns the authenticated operation error or invalidation diagnostic.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error unless this is an `error` or `invalidated` progress value.
    pub fn error(&self) -> Result<String, JsValue> {
        match self.value.as_ref() {
            Some(WebReplOperationProgressValue::Failed { error, .. }) => Ok(error.clone()),
            _ => Err(JsValue::from_str(
                "operation progress does not contain an error",
            )),
        }
    }
}

#[wasm_bindgen]
impl WebReplOperationOutput {
    /// Returns the typed output discriminator.
    #[must_use]
    pub fn kind(&self) -> String {
        match self.output {
            Some(ReplOperationOutput::Opened(_)) => "opened",
            Some(ReplOperationOutput::Closed) => "closed",
            Some(ReplOperationOutput::Sql(_)) => "sql",
            Some(ReplOperationOutput::Image(_)) => "image",
            Some(ReplOperationOutput::ImageResident(_)) => "image-resident",
            Some(ReplOperationOutput::Attached) => "attached",
            Some(ReplOperationOutput::Serialized(_)) => "serialized",
            None => "consumed",
        }
        .to_owned()
    }

    /// Returns the newly opened REPL connection ID.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for another output kind or an out-of-range ID.
    pub fn connection(&self) -> Result<u32, JsValue> {
        match self.output.as_ref() {
            Some(ReplOperationOutput::Opened(connection)) => {
                u32::try_from(connection.get()).map_err(js_error)
            }
            _ => Err(JsValue::from_str(
                "operation output is not an opened connection",
            )),
        }
    }

    /// Takes the SQL statement outcome.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for another output kind or after this output was consumed.
    pub fn take_sql_outcome(&mut self) -> Result<WebOutcome, JsValue> {
        if !matches!(self.output, Some(ReplOperationOutput::Sql(_))) {
            return Err(JsValue::from_str("operation output is not a SQL outcome"));
        }
        match self.output.take() {
            Some(ReplOperationOutput::Sql(outcome)) => Ok(WebOutcome { outcome }),
            _ => unreachable!("output kind was checked"),
        }
    }

    /// Returns the admitted image's exact operational address.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for another output kind.
    pub fn image(&self) -> Result<String, JsValue> {
        match self.output.as_ref() {
            Some(ReplOperationOutput::Image(image)) => Ok(image.to_string()),
            _ => Err(JsValue::from_str(
                "operation output is not an image address",
            )),
        }
    }

    /// Returns whether the queried image is resident.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for another output kind.
    pub fn image_resident(&self) -> Result<bool, JsValue> {
        match self.output {
            Some(ReplOperationOutput::ImageResident(resident)) => Ok(resident),
            _ => Err(JsValue::from_str(
                "operation output is not an image-residency result",
            )),
        }
    }

    /// Takes exact serialized `main` database bytes.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for another output kind or after this output was consumed.
    pub fn take_serialized(&mut self) -> Result<Vec<u8>, JsValue> {
        if !matches!(self.output, Some(ReplOperationOutput::Serialized(_))) {
            return Err(JsValue::from_str(
                "operation output is not serialized bytes",
            ));
        }
        match self.output.take() {
            Some(ReplOperationOutput::Serialized(bytes)) => Ok(bytes),
            _ => unreachable!("output kind was checked"),
        }
    }
}

#[wasm_bindgen]
impl WebImportedHolExport {
    /// Returns `kind`, `type`, `term`, or `context`.
    pub fn sort(&self) -> String {
        match self.value.value {
            LocalImportedHolValue::Kind(_) => "kind",
            LocalImportedHolValue::Type(_) => "type",
            LocalImportedHolValue::Term { .. } => "term",
            LocalImportedHolValue::Context(_) => "context",
        }
        .to_owned()
    }

    /// Returns the destination connection whose trust state authorized the read.
    pub fn connection_id(&self) -> Result<u32, JsValue> {
        u32::try_from(self.value.connection.get()).map_err(js_error)
    }

    /// Returns the exact persistent trusted-import assumption.
    pub fn trusted_import_id(&self) -> Result<u32, JsValue> {
        u32::try_from(self.value.trusted_import.get()).map_err(js_error)
    }

    /// Returns the exact inert import-directory row.
    pub fn import_id(&self) -> Result<u32, JsValue> {
        u32::try_from(self.value.import.get()).map_err(js_error)
    }

    /// Returns the destination-local imported namespace alias.
    pub fn namespace_id(&self) -> Result<u32, JsValue> {
        u32::try_from(self.value.namespace.get()).map_err(js_error)
    }

    /// Returns the requested export coordinate.
    pub fn export_id(&self) -> Result<u32, JsValue> {
        u32::try_from(self.value.export.get()).map_err(js_error)
    }

    /// Returns the inert source-database value coordinate.
    pub fn source_id(&self) -> Result<u32, JsValue> {
        u32::try_from(match self.value.value {
            LocalImportedHolValue::Kind(id)
            | LocalImportedHolValue::Type(id)
            | LocalImportedHolValue::Context(id)
            | LocalImportedHolValue::Term { id, .. } => id,
        })
        .map_err(js_error)
    }

    /// Returns the structural term tag, or no value for another export sort.
    pub fn term_tag(&self) -> Option<String> {
        self.term().map(|term| {
            match term {
                LocalImportedHolTerm::Bool(_) => "bool",
                LocalImportedHolTerm::Free { .. } => "free",
                LocalImportedHolTerm::Bound { .. } => "bound",
                LocalImportedHolTerm::Application { .. } => "application",
                LocalImportedHolTerm::Lambda { .. } => "lambda",
                LocalImportedHolTerm::Equality { .. } => "equality",
            }
            .to_owned()
        })
    }

    pub fn boolean(&self) -> Result<bool, JsValue> {
        match self.term() {
            Some(LocalImportedHolTerm::Bool(value)) => Ok(value),
            _ => Err(JsValue::from_str("imported export is not a Boolean term")),
        }
    }

    pub fn source_lhs(&self) -> Result<u32, JsValue> {
        let id = match self.term() {
            Some(LocalImportedHolTerm::Free { symbol, .. }) => {
                i64::try_from(symbol).map_err(js_error)?
            }
            Some(LocalImportedHolTerm::Bound { index, .. }) => {
                i64::try_from(index).map_err(js_error)?
            }
            Some(LocalImportedHolTerm::Application { function, .. }) => function,
            Some(LocalImportedHolTerm::Lambda { parameter_type, .. }) => parameter_type,
            Some(LocalImportedHolTerm::Equality { left, .. }) => left,
            _ => return Err(JsValue::from_str("imported term has no lhs coordinate")),
        };
        u32::try_from(id).map_err(js_error)
    }

    pub fn source_rhs(&self) -> Result<u32, JsValue> {
        let id = match self.term() {
            Some(LocalImportedHolTerm::Application { argument, .. }) => argument,
            Some(LocalImportedHolTerm::Lambda { body, .. }) => body,
            Some(LocalImportedHolTerm::Equality { right, .. }) => right,
            _ => return Err(JsValue::from_str("imported term has no rhs coordinate")),
        };
        u32::try_from(id).map_err(js_error)
    }

    pub fn source_type(&self) -> Result<u32, JsValue> {
        let ty = match self.term() {
            Some(
                LocalImportedHolTerm::Free { ty, .. }
                | LocalImportedHolTerm::Bound { ty, .. }
                | LocalImportedHolTerm::Application { ty, .. }
                | LocalImportedHolTerm::Lambda { ty, .. }
                | LocalImportedHolTerm::Equality { ty, .. },
            ) => ty,
            _ => {
                return Err(JsValue::from_str(
                    "imported export has no structural term type",
                ));
            }
        };
        u32::try_from(ty).map_err(js_error)
    }
}

impl WebImportedHolExport {
    fn term(&self) -> Option<LocalImportedHolTerm> {
        match self.value.value {
            LocalImportedHolValue::Term { term, .. } => Some(term),
            _ => None,
        }
    }
}

impl WebExport {
    fn new(value: NamespaceExport, name: Option<String>) -> Self {
        let (sort, local) = match value {
            NamespaceExport::Kind(id) => ("kind", id.get()),
            NamespaceExport::Type(id) => ("type", id.get()),
            NamespaceExport::Term(id) => ("term", id.get()),
            NamespaceExport::Context(id) => ("context", id.get()),
        };
        Self { sort, local, name }
    }
}

#[wasm_bindgen]
impl WebNamespace {
    /// Returns the parent ID, or no value for a top-level namespace.
    pub fn parent(&self) -> Result<Option<u32>, JsValue> {
        self.namespace
            .parent
            .map(|parent| u32::try_from(parent.get()).map_err(js_error))
            .transpose()
    }

    /// Returns the optional local name.
    #[must_use]
    pub fn name(&self) -> Option<String> {
        self.namespace.name.clone()
    }
}

#[wasm_bindgen]
impl WebExport {
    /// Returns `kind`, `type`, `term`, or `context`.
    #[must_use]
    pub fn sort(&self) -> String {
        self.sort.to_owned()
    }

    /// Returns the database-local ID.
    pub fn local(&self) -> Result<u32, JsValue> {
        u32::try_from(self.local).map_err(js_error)
    }

    /// Returns the optional export name.
    #[must_use]
    pub fn name(&self) -> Option<String> {
        self.name.clone()
    }
}

#[wasm_bindgen]
impl WebSignedHolSnapshot {
    /// Returns the exact `SQLite` bytes.
    #[must_use]
    pub fn bytes(&self) -> Vec<u8> {
        self.snapshot.bytes().to_vec()
    }

    /// Returns the canonical checked metadata schema descriptor.
    #[must_use]
    pub fn descriptor(&self) -> Vec<u8> {
        self.snapshot.descriptor().to_vec()
    }

    /// Returns the exact schema hash in hexadecimal.
    #[must_use]
    pub fn schema(&self) -> String {
        self.snapshot.schema().to_string()
    }

    /// Returns the exact image hash in hexadecimal.
    #[must_use]
    pub fn image(&self) -> String {
        self.snapshot.image().to_string()
    }

    /// Returns the signing-key identity in hexadecimal.
    #[must_use]
    pub fn signer(&self) -> String {
        self.snapshot.signer().to_string()
    }

    /// Returns the Ed25519 public key bytes.
    #[must_use]
    pub fn public_key(&self) -> Vec<u8> {
        self.snapshot.public_key().to_vec()
    }

    /// Returns the Ed25519 signature bytes.
    #[must_use]
    pub fn signature(&self) -> Vec<u8> {
        self.snapshot.signature().to_vec()
    }
}

#[wasm_bindgen]
impl WebTrustedHolImport {
    /// Returns the inert local import ID.
    ///
    /// # Errors
    ///
    /// Returns an error if the ID cannot be represented by the browser API.
    pub fn import_id(&self) -> Result<u32, JsValue> {
        u32::try_from(self.trusted.import().get()).map_err(js_error)
    }

    /// Returns the persistent trusted-import ID.
    ///
    /// # Errors
    ///
    /// Returns an error if the ID cannot be represented by the browser API.
    pub fn trusted_import_id(&self) -> Result<u32, JsValue> {
        u32::try_from(self.trusted.trusted_import().get()).map_err(js_error)
    }

    /// Returns the exact interpretation-qualified schema identity.
    #[must_use]
    pub fn schema(&self) -> String {
        self.trusted.database().schema().to_string()
    }

    /// Returns the exact snapshot image hash.
    #[must_use]
    pub fn image(&self) -> String {
        self.trusted.database().image().to_string()
    }

    /// Returns the authenticated signer identity.
    #[must_use]
    pub fn signer(&self) -> String {
        self.trusted.signer().to_string()
    }
}

#[wasm_bindgen]
impl WebKind {
    /// Returns `star` or `arrow`.
    #[must_use]
    pub fn tag(&self) -> String {
        match self.kind {
            KindView::Star => "star",
            KindView::Arrow { .. } => "arrow",
        }
        .to_owned()
    }

    /// Returns the domain ID of an arrow kind.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error if this is `star` or the ID exceeds `u32`.
    pub fn domain(&self) -> Result<u32, JsValue> {
        match self.kind {
            KindView::Arrow { domain, .. } => u32::try_from(domain.get()).map_err(js_error),
            KindView::Star => Err(JsValue::from_str("star has no domain")),
        }
    }

    /// Returns the codomain ID of an arrow kind.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error if this is `star` or the ID exceeds `u32`.
    pub fn codomain(&self) -> Result<u32, JsValue> {
        match self.kind {
            KindView::Arrow { codomain, .. } => u32::try_from(codomain.get()).map_err(js_error),
            KindView::Star => Err(JsValue::from_str("star has no codomain")),
        }
    }
}

#[wasm_bindgen]
impl WebType {
    /// Returns `bool` or `arrow`.
    #[must_use]
    pub fn tag(&self) -> String {
        match self.ty {
            TypeView::Bool => "bool",
            TypeView::Arrow { .. } => "arrow",
        }
        .to_owned()
    }

    /// Returns an arrow type's domain ID.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for `bool` or an ID outside `u32`.
    pub fn domain(&self) -> Result<u32, JsValue> {
        match self.ty {
            TypeView::Arrow { domain, .. } => u32::try_from(domain.get()).map_err(js_error),
            TypeView::Bool => Err(JsValue::from_str("Bool has no domain")),
        }
    }

    /// Returns an arrow type's codomain ID.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for `bool` or an ID outside `u32`.
    pub fn codomain(&self) -> Result<u32, JsValue> {
        match self.ty {
            TypeView::Arrow { codomain, .. } => u32::try_from(codomain.get()).map_err(js_error),
            TypeView::Bool => Err(JsValue::from_str("Bool has no codomain")),
        }
    }
}

#[wasm_bindgen]
impl WebTerm {
    /// Returns the stable constructor tag.
    #[must_use]
    pub fn tag(&self) -> String {
        match self.term {
            TermView::Bool(_) => "bool",
            TermView::Free { .. } => "free",
            TermView::Bound { .. } => "bound",
            TermView::Application { .. } => "application",
            TermView::Lambda { .. } => "lambda",
            TermView::Equality { .. } => "equality",
        }
        .to_owned()
    }

    /// Returns a Boolean literal's value.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for another constructor.
    pub fn boolean(&self) -> Result<bool, JsValue> {
        match self.term {
            TermView::Bool(value) => Ok(value),
            _ => Err(JsValue::from_str("term is not a Boolean literal")),
        }
    }

    /// Returns a free term's symbol ID.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for another constructor or a symbol outside
    /// `u32`.
    pub fn symbol(&self) -> Result<u32, JsValue> {
        match self.term {
            TermView::Free { symbol } => u32::try_from(symbol).map_err(js_error),
            _ => Err(JsValue::from_str("term is not a free symbol")),
        }
    }

    /// Returns a bound occurrence's de Bruijn index.
    pub fn index(&self) -> Result<u32, JsValue> {
        match self.term {
            TermView::Bound { index } => Ok(index),
            _ => Err(JsValue::from_str("term is not a bound occurrence")),
        }
    }

    /// Returns an application's function term ID.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for another constructor or an ID outside
    /// `u32`.
    pub fn function(&self) -> Result<u32, JsValue> {
        match self.term {
            TermView::Application { function, .. } => {
                u32::try_from(function.get()).map_err(js_error)
            }
            _ => Err(JsValue::from_str("term is not an application")),
        }
    }

    /// Returns an application's argument term ID.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for another constructor or an ID outside
    /// `u32`.
    pub fn argument(&self) -> Result<u32, JsValue> {
        match self.term {
            TermView::Application { argument, .. } => {
                u32::try_from(argument.get()).map_err(js_error)
            }
            _ => Err(JsValue::from_str("term is not an application")),
        }
    }

    /// Returns a lambda's parameter type ID.
    pub fn parameter_type(&self) -> Result<u32, JsValue> {
        match self.term {
            TermView::Lambda { parameter_type, .. } => {
                u32::try_from(parameter_type.get()).map_err(js_error)
            }
            _ => Err(JsValue::from_str("term is not a lambda")),
        }
    }

    /// Returns a lambda's body term ID.
    pub fn body(&self) -> Result<u32, JsValue> {
        match self.term {
            TermView::Lambda { body, .. } => u32::try_from(body.get()).map_err(js_error),
            _ => Err(JsValue::from_str("term is not a lambda")),
        }
    }

    /// Returns an equality's left operand.
    pub fn left(&self) -> Result<u32, JsValue> {
        match self.term {
            TermView::Equality { left, .. } => u32::try_from(left.get()).map_err(js_error),
            _ => Err(JsValue::from_str("term is not an equality")),
        }
    }

    /// Returns an equality's right operand.
    pub fn right(&self) -> Result<u32, JsValue> {
        match self.term {
            TermView::Equality { right, .. } => u32::try_from(right.get()).map_err(js_error),
            _ => Err(JsValue::from_str("term is not an equality")),
        }
    }
}

#[wasm_bindgen]
impl WebOutcome {
    /// Returns `rows` or `changed`.
    #[must_use]
    pub fn kind(&self) -> String {
        match self.outcome {
            Outcome::Rows(_) => "rows",
            Outcome::Changed(_) => "changed",
        }
        .to_owned()
    }

    /// Returns the changed-row count for a non-row statement.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error if this outcome contains rows.
    pub fn changed(&self) -> Result<usize, JsValue> {
        match self.outcome {
            Outcome::Changed(count) => Ok(count),
            Outcome::Rows(_) => Err(JsValue::from_str("outcome contains rows")),
        }
    }

    /// Returns the number of result columns.
    #[must_use]
    pub fn column_count(&self) -> usize {
        self.rows().map_or(0, |result| result.columns.len())
    }

    /// Returns a column name by index.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for a non-row outcome or invalid index.
    pub fn column_name(&self, column: u32) -> Result<String, JsValue> {
        self.rows()?
            .columns
            .get(column as usize)
            .cloned()
            .ok_or_else(|| JsValue::from_str("column index out of bounds"))
    }

    /// Returns the number of result rows.
    #[must_use]
    pub fn row_count(&self) -> usize {
        self.rows().map_or(0, |result| result.rows.len())
    }

    /// Returns the SQLite storage class for one value.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for invalid row or column indices.
    pub fn value_kind(&self, row: u32, column: u32) -> Result<String, JsValue> {
        Ok(match self.value(row, column)? {
            Value::Null => "null",
            Value::Integer(_) => "integer",
            Value::Real(_) => "real",
            Value::Text(_) => "text",
            Value::Blob(_) => "blob",
        }
        .to_owned())
    }

    /// Returns an integer as an exact decimal string.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error if the selected value is not an integer.
    pub fn integer(&self, row: u32, column: u32) -> Result<String, JsValue> {
        match self.value(row, column)? {
            Value::Integer(value) => Ok(value.to_string()),
            _ => Err(JsValue::from_str("value is not an integer")),
        }
    }

    /// Returns a floating-point value.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error if the selected value is not real.
    pub fn real(&self, row: u32, column: u32) -> Result<f64, JsValue> {
        match self.value(row, column)? {
            Value::Real(value) => Ok(*value),
            _ => Err(JsValue::from_str("value is not real")),
        }
    }

    /// Returns a text value.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error if the selected value is not text.
    pub fn text(&self, row: u32, column: u32) -> Result<String, JsValue> {
        match self.value(row, column)? {
            Value::Text(value) => Ok(value.clone()),
            _ => Err(JsValue::from_str("value is not text")),
        }
    }

    /// Returns a blob value.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error if the selected value is not a blob.
    pub fn blob(&self, row: u32, column: u32) -> Result<Vec<u8>, JsValue> {
        match self.value(row, column)? {
            Value::Blob(value) => Ok(value.clone()),
            _ => Err(JsValue::from_str("value is not a blob")),
        }
    }
}

impl WebOutcome {
    fn rows(&self) -> Result<&QueryResult, JsValue> {
        match &self.outcome {
            Outcome::Rows(result) => Ok(result),
            Outcome::Changed(_) => Err(JsValue::from_str("outcome has no rows")),
        }
    }

    fn value(&self, row: u32, column: u32) -> Result<&Value, JsValue> {
        self.rows()?
            .rows
            .get(row as usize)
            .and_then(|row| row.get(column as usize))
            .ok_or_else(|| JsValue::from_str("value index out of bounds"))
    }
}

fn js_error(error: impl std::fmt::Display) -> JsValue {
    JsValue::from_str(&error.to_string())
}
