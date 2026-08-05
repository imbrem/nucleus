use std::collections::HashMap;

use covalence_lib_hash::O256;
use wasm_bindgen::prelude::*;

use super::{
    AllowAll, ConnectionEntry, ConnectionId, HolRecipe, HolRecipeResult, Kernel, KernelEntry,
    KernelId, LocalConnection, Outcome, PinnedSignedHolArtifact, ProducedSignedHol, QueryResult,
    ReceivedHolSnapshot, Repl, SIGNED_HOL_PHASES, SignedHolArtifact, SignedHolRoundTripResult,
    Value, authenticate_pinned_signed_hol_artifact, produce_signed_hol_artifact,
    run_managed_signed_hol_round_trip, trust_and_receive_pinned_signed_hol_artifact,
};

/// Main-thread directory for independently owned browser kernel endpoints.
///
/// It owns no logical connection and grants no trust. JavaScript keeps the
/// actual Worker handles; this object keeps the same raw-SQLite directory model
/// used by the terminal adapter.
#[wasm_bindgen]
pub struct WebReplDirectory {
    repl: Repl<()>,
}

/// Inspectable browser kernel-directory row.
#[wasm_bindgen]
pub struct WebKernelEntry {
    entry: KernelEntry,
}

/// Inspectable browser connection-directory row.
#[wasm_bindgen]
pub struct WebConnectionEntry {
    entry: ConnectionEntry,
}

/// Browser adapter for the shared REPL connection directory.
#[wasm_bindgen]
pub struct WebKernel {
    kernel: Kernel,
    repl: Repl<LocalConnection>,
    pinned_artifacts: HashMap<u32, PinnedSignedHolArtifact>,
    next_pinned_artifact: u32,
}

/// Owned result of one statement executed by [`WebKernel`].
#[wasm_bindgen]
pub struct WebOutcome {
    outcome: Outcome,
}

/// Transport-neutral HOL recipe result exposed through Wasm.
#[wasm_bindgen]
pub struct WebHolOutcome {
    outcome: HolRecipeResult,
}

/// Complete signed HOL producer-to-receiver demonstration exposed through Wasm.
#[wasm_bindgen]
pub struct WebSignedHolOutcome {
    outcome: SignedHolRoundTripResult,
    receiver_connection: u32,
}

/// Producer-local proof presentation and its transportable signed artifact.
#[wasm_bindgen]
pub struct WebProducedSignedHol {
    produced: ProducedSignedHol,
}

/// Inert receiver-local coordinates established after a scoped imported-theorem read.
///
/// These integers are presentation data, never theorem authority. The receiving
/// connection remains owned by its caller and can reauthenticate, remount, and
/// reread the imported theorem after this value is dropped.
#[wasm_bindgen]
pub struct WebReceivedHolSnapshot {
    received: ReceivedHolSnapshot,
}

#[wasm_bindgen]
impl WebKernel {
    /// Creates a browser REPL with its own raw `SQLite` state database.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error if the state database cannot be opened.
    #[wasm_bindgen(constructor)]
    pub fn new() -> Result<WebKernel, JsValue> {
        let kernel = Kernel::ephemeral();
        let repl = Repl::new(kernel.verifying_key().as_bytes()).map_err(js_error)?;
        Ok(Self {
            kernel,
            repl,
            pinned_artifacts: HashMap::new(),
            next_pinned_artifact: 0,
        })
    }

    /// Returns this kernel's public-key identity.
    #[must_use]
    pub fn signer_id(&self) -> String {
        self.kernel.key_id().to_string()
    }

    /// Returns this kernel's exact Ed25519 public key.
    #[must_use]
    pub fn public_key(&self) -> Vec<u8> {
        self.kernel.verifying_key().as_bytes().to_vec()
    }

    /// Opens a writable in-memory SQL connection and returns its local ID.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error when the connection or directory row cannot
    /// be opened.
    pub fn open_connection(&mut self) -> Result<u32, JsValue> {
        let connection = LocalConnection::Sql(self.kernel.open_sql().map_err(js_error)?);
        let id = self
            .repl
            .insert(connection.protocol(), connection)
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Opens an in-memory HOL connection and returns its local ID.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error when the connection or directory row cannot
    /// be opened.
    pub fn open_hol_connection(&mut self) -> Result<u32, JsValue> {
        let connection = LocalConnection::Hol(self.kernel.open_hol(AllowAll).map_err(js_error)?);
        let id = self
            .repl
            .insert(connection.protocol(), connection)
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Closes a connection.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for an unknown ID or state update failure.
    pub fn close_connection(&mut self, connection: u32) -> Result<(), JsValue> {
        self.repl
            .remove(ConnectionId::from_u32(connection))
            .map(drop)
            .map_err(js_error)
    }

    /// Runs one parameterless SQL statement.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error when the statement fails.
    pub fn run(&mut self, connection: u32, sql: &str) -> Result<WebOutcome, JsValue> {
        self.sql_mut(connection)?
            .run(sql, &[])
            .map(|outcome| WebOutcome { outcome })
            .map_err(js_error)
    }

    /// Parses and runs one shared HOL demo recipe.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for a non-HOL connection, invalid recipe, or
    /// rejected Nucleus operation.
    pub fn run_hol(&mut self, connection: u32, recipe: &str) -> Result<WebHolOutcome, JsValue> {
        let recipe = recipe.parse::<HolRecipe>().map_err(js_error)?;
        recipe
            .execute(self.hol_mut(connection)?)
            .map(|outcome| WebHolOutcome { outcome })
            .map_err(js_error)
    }

    /// Runs the shared signed HOL snapshot round trip on one HOL connection.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for a non-HOL connection or the first proof,
    /// authentication, validation, trust, import, or reader boundary rejected.
    pub fn run_signed_hol_round_trip(
        &mut self,
        connection: u32,
    ) -> Result<WebSignedHolOutcome, JsValue> {
        let (outcome, receiver_id) = run_managed_signed_hol_round_trip(
            &self.kernel,
            &mut self.repl,
            ConnectionId::from_u32(connection),
        )
        .map_err(js_error)?;
        Ok(WebSignedHolOutcome {
            outcome,
            receiver_connection: u32::try_from(receiver_id.get()).map_err(js_error)?,
        })
    }

    /// Proves, persists, exports, and signs one HOL artifact in this kernel.
    ///
    /// The returned fields are an above-TCB structured carrier, not a stable
    /// wire encoding. A different [`WebKernel`] must authenticate and validate
    /// every field with [`WebKernel::authenticate_pinned_signed_hol_artifact`].
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for a non-HOL connection or the first proof,
    /// export, or signing boundary rejected.
    pub fn produce_signed_hol_artifact(
        &mut self,
        connection: u32,
    ) -> Result<WebProducedSignedHol, JsValue> {
        let produced = {
            let Self { kernel, repl, .. } = self;
            let source = repl
                .get_mut(ConnectionId::from_u32(connection))
                .map_err(js_error)?
                .hol_mut()
                .map_err(js_error)?;
            produce_signed_hol_artifact(kernel, source).map_err(js_error)?
        };
        Ok(WebProducedSignedHol { produced })
    }

    /// Returns the exact persistent HOL image hash without changing kernel state.
    ///
    /// This debugging surface intentionally excludes connection-local temp trust.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for a non-HOL connection or failed validated export.
    pub fn hol_image_hash(&mut self, connection: u32) -> Result<String, JsValue> {
        let Self { kernel, repl, .. } = self;
        let source = repl
            .get_mut(ConnectionId::from_u32(connection))
            .map_err(js_error)?
            .hol_mut()
            .map_err(js_error)?;
        kernel
            .export_hol(source)
            .map(|snapshot| snapshot.image().hash().to_string())
            .map_err(js_error)
    }

    /// Authenticates and detached-validates an artifact against an expected endpoint key.
    ///
    /// All arguments are untrusted transport fields. Hash parsing and fixed
    /// widths do not confer authority. The independently supplied endpoint key
    /// is compared exactly before this method returns an opaque pending ID. No
    /// HOL connection is read or mutated by this step.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for malformed fields or a rejected size,
    /// authentication, endpoint pin, or detached-validation boundary.
    #[expect(
        clippy::too_many_arguments,
        reason = "the deliberately unencoded transport exposes every signed field"
    )]
    pub fn authenticate_pinned_signed_hol_artifact(
        &mut self,
        expected_kernel: u32,
        expected_signer: &str,
        expected_public_key: &[u8],
        namespace: &str,
        image: &[u8],
        schema: &str,
        image_hash: &str,
        signer: &str,
        public_key: &[u8],
        signature: &[u8],
    ) -> Result<u32, JsValue> {
        if image.len() > super::MAX_IMAGE_BYTES {
            return Err(JsValue::from_str(&format!(
                "image-size-checked: image is {} bytes; the limit is {} bytes",
                image.len(),
                super::MAX_IMAGE_BYTES,
            )));
        }
        let namespace = namespace.parse::<i64>().map_err(js_error)?;
        let artifact = SignedHolArtifact::from_untrusted_parts(
            namespace,
            image.to_vec(),
            schema,
            image_hash,
            signer,
            public_key.to_vec(),
            signature.to_vec(),
        )
        .map_err(js_error)?;
        let expected = super::ExpectedKernelIdentity::from_untrusted_parts(
            KernelId::from_u32(expected_kernel),
            expected_signer,
            expected_public_key,
        )
        .map_err(js_error)?;
        let pinned =
            authenticate_pinned_signed_hol_artifact(&expected, &artifact).map_err(js_error)?;
        let id = self.next_pinned_artifact;
        self.next_pinned_artifact = self
            .next_pinned_artifact
            .checked_add(1)
            .ok_or_else(|| JsValue::from_str("pinned artifact IDs are exhausted"))?;
        self.pinned_artifacts.insert(id, pinned);
        Ok(id)
    }

    /// Explicitly trusts and imports one previously authenticated pinned artifact.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for an unknown pending ID, non-HOL target, or
    /// rejected trust, import, immutable mount, or reader boundary.
    pub fn trust_pinned_signed_hol_artifact(
        &mut self,
        connection: u32,
        pinned: u32,
    ) -> Result<WebReceivedHolSnapshot, JsValue> {
        let pinned = self
            .pinned_artifacts
            .remove(&pinned)
            .ok_or_else(|| JsValue::from_str("unknown pinned HOL artifact"))?;
        let received =
            trust_and_receive_pinned_signed_hol_artifact(self.hol_mut(connection)?, pinned)
                .map_err(js_error)?;
        Ok(WebReceivedHolSnapshot { received })
    }

    /// Discards one authenticated artifact without granting any trust.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for an unknown pending ID.
    pub fn abandon_pinned_signed_hol_artifact(&mut self, pinned: u32) -> Result<(), JsValue> {
        self.pinned_artifacts
            .remove(&pinned)
            .map(drop)
            .ok_or_else(|| JsValue::from_str("unknown pinned HOL artifact"))
    }

    /// Stores a complete resident database image and returns its address.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error on a resident hash collision.
    pub fn put_image(&mut self, connection: u32, bytes: &[u8]) -> Result<String, JsValue> {
        self.sql_mut(connection)?
            .put_image(bytes)
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
        self.sql_mut(connection)?
            .attach_immutable_image(hash, schema)
            .map_err(js_error)
    }

    /// Returns the maximum accepted database image size in bytes.
    #[must_use]
    #[expect(
        clippy::cast_precision_loss,
        reason = "the image bound is far below 2^53, so the conversion is exact"
    )]
    pub fn max_image_bytes() -> f64 {
        super::MAX_IMAGE_BYTES as f64
    }

    /// Serializes the writable in-memory `main` database.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error when `SQLite` cannot serialize the database.
    pub fn serialize_main(&mut self, connection: u32) -> Result<Vec<u8>, JsValue> {
        self.sql_mut(connection)?
            .serialize_main()
            .map(|bytes| bytes.to_vec())
            .map_err(js_error)
    }
}

#[wasm_bindgen]
impl WebReplDirectory {
    /// Opens an empty coordinator directory.
    #[wasm_bindgen(constructor)]
    pub fn new() -> Result<Self, JsValue> {
        Repl::empty().map(|repl| Self { repl }).map_err(js_error)
    }

    /// Registers a keyed Worker endpoint without trusting it.
    pub fn register_kernel(
        &self,
        transport: &str,
        endpoint: Option<String>,
        public_key: &[u8],
    ) -> Result<u32, JsValue> {
        let id = self
            .repl
            .register_kernel(transport, endpoint.as_deref(), public_key)
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Removes a Worker endpoint after all of its connections are closed.
    pub fn unregister_kernel(&self, kernel: u32) -> Result<(), JsValue> {
        self.repl
            .unregister_kernel(KernelId::from_u32(kernel))
            .map_err(js_error)
    }

    /// Records an endpoint-owned runtime connection.
    pub fn insert_connection(
        &mut self,
        kernel: u32,
        protocol: &str,
        remote_connection_id: &str,
    ) -> Result<u32, JsValue> {
        let id = self
            .repl
            .insert_at(
                KernelId::from_u32(kernel),
                protocol,
                Some(remote_connection_id),
                (),
            )
            .map_err(js_error)?;
        u32::try_from(id.get()).map_err(js_error)
    }

    /// Removes one endpoint-owned runtime connection row.
    pub fn remove_connection(&mut self, connection: u32) -> Result<(), JsValue> {
        self.repl
            .remove(ConnectionId::from_u32(connection))
            .map(drop)
            .map_err(js_error)
    }

    /// Selects an existing managed connection in the coordinator directory.
    pub fn select_connection(&mut self, connection: u32) -> Result<(), JsValue> {
        self.repl
            .select(ConnectionId::from_u32(connection))
            .map_err(js_error)
    }

    /// Returns the selected managed connection, if any.
    pub fn active_connection(&self) -> Result<Option<u32>, JsValue> {
        self.repl
            .active()
            .map_err(js_error)?
            .map(|id| u32::try_from(id.get()).map_err(js_error))
            .transpose()
    }

    /// Returns the number of registered endpoints.
    pub fn kernel_count(&self) -> Result<usize, JsValue> {
        self.repl.kernels().map(|rows| rows.len()).map_err(js_error)
    }

    /// Returns one endpoint row in directory order.
    pub fn kernel(&self, index: u32) -> Result<WebKernelEntry, JsValue> {
        self.repl
            .kernels()
            .map_err(js_error)?
            .into_iter()
            .nth(index as usize)
            .map(|entry| WebKernelEntry { entry })
            .ok_or_else(|| JsValue::from_str("kernel index out of bounds"))
    }

    /// Returns the number of managed connection rows.
    pub fn connection_count(&self) -> Result<usize, JsValue> {
        self.repl
            .connections()
            .map(|rows| rows.len())
            .map_err(js_error)
    }

    /// Returns one connection row in directory order.
    pub fn connection(&self, index: u32) -> Result<WebConnectionEntry, JsValue> {
        self.repl
            .connections()
            .map_err(js_error)?
            .into_iter()
            .nth(index as usize)
            .map(|entry| WebConnectionEntry { entry })
            .ok_or_else(|| JsValue::from_str("connection index out of bounds"))
    }
}

#[wasm_bindgen]
impl WebKernelEntry {
    /// Returns the directory-local opaque ID.
    pub fn id(&self) -> String {
        self.entry.id.to_string()
    }

    /// Returns the adapter-defined transport.
    pub fn transport(&self) -> String {
        self.entry.transport.clone()
    }

    /// Returns the optional adapter-defined endpoint locator.
    pub fn endpoint(&self) -> Option<String> {
        self.entry.endpoint.clone()
    }

    /// Returns the exact registered public key.
    pub fn public_key(&self) -> Vec<u8> {
        self.entry.public_key.clone()
    }
}

#[wasm_bindgen]
impl WebConnectionEntry {
    /// Returns the directory-local opaque ID.
    pub fn id(&self) -> String {
        self.entry.id.to_string()
    }

    /// Returns the owning endpoint's opaque ID.
    pub fn kernel_id(&self) -> String {
        self.entry.kernel.to_string()
    }

    /// Returns the recorded protocol label.
    pub fn protocol(&self) -> String {
        self.entry.protocol.clone()
    }

    /// Returns the optional endpoint-local coordinate.
    pub fn remote_connection_id(&self) -> Option<String> {
        self.entry.remote_connection_id.clone()
    }
}

impl WebKernel {
    fn connection_mut(&mut self, id: u32) -> Result<&mut LocalConnection, JsValue> {
        self.repl
            .get_mut(ConnectionId::from_u32(id))
            .map_err(js_error)
    }

    fn sql_mut(
        &mut self,
        id: u32,
    ) -> Result<&mut covalence_nucleus::Connection<covalence_nucleus::Sql>, JsValue> {
        self.connection_mut(id)?.sql_mut().map_err(js_error)
    }

    fn hol_mut(
        &mut self,
        id: u32,
    ) -> Result<&mut covalence_nucleus::Connection<covalence_nucleus::Hol<AllowAll>>, JsValue> {
        self.connection_mut(id)?.hol_mut().map_err(js_error)
    }
}

#[wasm_bindgen]
impl WebHolOutcome {
    /// Returns `hol-theorem`.
    #[must_use]
    pub fn kind(&self) -> String {
        self.outcome.kind().to_owned()
    }

    /// Returns the recipe constructor name.
    #[must_use]
    pub fn recipe(&self) -> String {
        self.outcome.recipe().to_owned()
    }

    /// Returns the database-local context ID as an exact decimal string.
    #[must_use]
    pub fn context_id(&self) -> String {
        self.outcome.context_id().to_string()
    }

    /// Returns the database-local conclusion ID as an exact decimal string.
    #[must_use]
    pub fn conclusion_id(&self) -> String {
        self.outcome.conclusion_id().to_string()
    }

    /// Returns the recipe's stable human-readable proposition.
    #[must_use]
    pub fn statement(&self) -> String {
        self.outcome.statement().to_owned()
    }
}

#[wasm_bindgen]
impl WebProducedSignedHol {
    /// Returns `signed-hol-artifact`.
    #[must_use]
    pub fn kind(&self) -> String {
        "signed-hol-artifact".to_owned()
    }

    /// Returns the number of completed producer boundary stages.
    #[must_use]
    pub fn phase_count(&self) -> usize {
        3
    }

    /// Returns one completed producer boundary stage by index.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error when `index` is out of bounds.
    pub fn phase(&self, index: u32) -> Result<String, JsValue> {
        SIGNED_HOL_PHASES
            .get(index as usize)
            .filter(|_| index < 3)
            .map(|phase| (*phase).to_owned())
            .ok_or_else(|| JsValue::from_str("phase index out of bounds"))
    }

    /// Returns the stable proposition persisted by the producer.
    #[must_use]
    pub fn statement(&self) -> String {
        self.produced.proof().statement().to_owned()
    }

    /// Returns the producer-local conclusion as an exact decimal string.
    #[must_use]
    pub fn conclusion_id(&self) -> String {
        self.produced.proof().conclusion_id().to_string()
    }

    /// Returns the source namespace as an exact decimal string.
    #[must_use]
    pub fn namespace_id(&self) -> String {
        self.produced.artifact().namespace_id().to_string()
    }

    /// Copies the exact signed SQLite bytes into JavaScript-owned memory.
    #[must_use]
    pub fn image(&self) -> Vec<u8> {
        self.produced.artifact().image().to_vec()
    }

    /// Returns the signed interpretation-qualified schema hash.
    #[must_use]
    pub fn schema(&self) -> String {
        self.produced.artifact().schema().to_string()
    }

    /// Returns the hash of the exact image bytes.
    #[must_use]
    pub fn image_hash(&self) -> String {
        self.produced.artifact().image_hash().to_string()
    }

    /// Returns the producer's key identity.
    #[must_use]
    pub fn signer(&self) -> String {
        self.produced.artifact().signer().to_string()
    }

    /// Copies the producer's Ed25519 public key into JavaScript-owned memory.
    #[must_use]
    pub fn public_key(&self) -> Vec<u8> {
        self.produced.artifact().public_key().to_vec()
    }

    /// Copies the schema-qualified image signature into JavaScript-owned memory.
    #[must_use]
    pub fn signature(&self) -> Vec<u8> {
        self.produced.artifact().signature().to_vec()
    }
}

#[wasm_bindgen]
impl WebReceivedHolSnapshot {
    /// Returns `received-hol-snapshot`.
    #[must_use]
    pub fn kind(&self) -> String {
        "received-hol-snapshot".to_owned()
    }

    /// Returns the number of completed receiver boundary stages.
    #[must_use]
    pub fn phase_count(&self) -> usize {
        SIGNED_HOL_PHASES.len() - 3
    }

    /// Returns one completed receiver boundary stage by index.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error when `index` is out of bounds.
    pub fn phase(&self, index: u32) -> Result<String, JsValue> {
        SIGNED_HOL_PHASES
            .get(index as usize + 3)
            .map(|phase| (*phase).to_owned())
            .ok_or_else(|| JsValue::from_str("phase index out of bounds"))
    }

    /// Returns the receiver's inert import-directory ID.
    #[must_use]
    pub fn import_id(&self) -> String {
        self.received.import_id().to_string()
    }

    /// Returns the receiver's imported namespace alias ID.
    #[must_use]
    pub fn namespace_id(&self) -> String {
        self.received.namespace_id().to_string()
    }

    /// Returns the imported empty-context source coordinate.
    #[must_use]
    pub fn context_id(&self) -> String {
        self.received.context_id().to_string()
    }

    /// Returns the imported conclusion source coordinate.
    #[must_use]
    pub fn conclusion_id(&self) -> String {
        self.received.conclusion_id().to_string()
    }
}

#[wasm_bindgen]
impl WebSignedHolOutcome {
    /// Returns `signed-hol-round-trip`.
    #[must_use]
    pub fn kind(&self) -> String {
        self.outcome.kind().to_owned()
    }

    /// Returns the managed receiver HOL connection ID.
    #[must_use]
    pub fn receiver_connection(&self) -> u32 {
        self.receiver_connection
    }

    /// Returns the number of completed boundary stages.
    #[must_use]
    pub fn phase_count(&self) -> usize {
        self.outcome.phases().len()
    }

    /// Returns one completed boundary stage by index.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error when `index` is out of bounds.
    pub fn phase(&self, index: u32) -> Result<String, JsValue> {
        self.outcome
            .phases()
            .get(index as usize)
            .map(|phase| (*phase).to_owned())
            .ok_or_else(|| JsValue::from_str("phase index out of bounds"))
    }

    /// Returns the stable proposition proved and read from the imported image.
    #[must_use]
    pub fn statement(&self) -> String {
        self.outcome.proof().statement().to_owned()
    }

    /// Returns the producer-local conclusion as an exact decimal string.
    #[must_use]
    pub fn conclusion_id(&self) -> String {
        self.outcome.proof().conclusion_id().to_string()
    }

    /// Returns the exported namespace ID as an exact decimal string.
    #[must_use]
    pub fn namespace_id(&self) -> String {
        self.outcome.namespace_id().to_string()
    }

    /// Returns the exact signed SQLite bytes.
    #[must_use]
    pub fn image(&self) -> Vec<u8> {
        self.outcome.image().to_vec()
    }

    /// Returns the signed schema hash.
    #[must_use]
    pub fn schema(&self) -> String {
        self.outcome.schema().to_string()
    }

    /// Returns the exact image hash.
    #[must_use]
    pub fn image_hash(&self) -> String {
        self.outcome.image_hash().to_string()
    }

    /// Returns the signing key identity.
    #[must_use]
    pub fn signer(&self) -> String {
        self.outcome.signer().to_string()
    }

    /// Returns the producer's Ed25519 public key.
    #[must_use]
    pub fn public_key(&self) -> Vec<u8> {
        self.outcome.public_key().to_vec()
    }

    /// Returns the schema-qualified snapshot signature.
    #[must_use]
    pub fn signature(&self) -> Vec<u8> {
        self.outcome.signature().to_vec()
    }

    /// Returns the demo-local downloadable attestation sidecar.
    #[must_use]
    pub fn attestation_text(&self) -> String {
        self.outcome.attestation_text()
    }

    /// Returns the receiver import ID as an exact decimal string.
    #[must_use]
    pub fn import_id(&self) -> String {
        self.outcome.import_id().to_string()
    }

    /// Returns the receiver namespace alias ID as an exact decimal string.
    #[must_use]
    pub fn imported_namespace_id(&self) -> String {
        self.outcome.imported_namespace_id().to_string()
    }

    /// Returns the imported context source coordinate as an exact decimal string.
    #[must_use]
    pub fn imported_context_id(&self) -> String {
        self.outcome.imported_context_id().to_string()
    }

    /// Returns the imported conclusion source coordinate as an exact decimal string.
    #[must_use]
    pub fn imported_conclusion_id(&self) -> String {
        self.outcome.imported_conclusion_id().to_string()
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

    /// Returns the `SQLite` storage class for one value.
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
