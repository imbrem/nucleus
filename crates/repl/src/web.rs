use covalence_lib_hash::O256;
use wasm_bindgen::prelude::*;

use super::{
    AllowAll, ConnectionId, HolRecipe, HolRecipeResult, Kernel, LocalConnection, Outcome,
    ProducedSignedHol, QueryResult, ReceivedHolSnapshot, Repl, SIGNED_HOL_PHASES,
    SignedHolArtifact, SignedHolRoundTripResult, Value, produce_signed_hol_artifact,
    receive_signed_hol_artifact,
};

/// Browser adapter for the shared REPL connection directory.
#[wasm_bindgen]
pub struct WebKernel {
    kernel: Kernel,
    repl: Repl<LocalConnection>,
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

/// Receiver-local coordinates established from an untrusted signed artifact.
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
        Ok(Self { kernel, repl })
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
        let produced = {
            let Self { kernel, repl } = self;
            let source = repl
                .get_mut(ConnectionId::from_u32(connection))
                .map_err(js_error)?
                .hol_mut()
                .map_err(js_error)?;
            produce_signed_hol_artifact(kernel, source).map_err(js_error)?
        };
        let receiver = LocalConnection::Hol(self.kernel.open_hol(AllowAll).map_err(js_error)?);
        let receiver_id = self
            .repl
            .insert(receiver.protocol(), receiver)
            .map_err(js_error)?;
        let received = receive_signed_hol_artifact(
            self.repl
                .get_mut(receiver_id)
                .map_err(js_error)?
                .hol_mut()
                .map_err(js_error)?,
            produced.artifact(),
        )
        .map_err(js_error)?;
        Ok(WebSignedHolOutcome {
            outcome: SignedHolRoundTripResult::from_parts(produced, received),
            receiver_connection: u32::try_from(receiver_id.get()).map_err(js_error)?,
        })
    }

    /// Proves, persists, exports, and signs one HOL artifact in this kernel.
    ///
    /// The returned fields are an above-TCB structured carrier, not a stable
    /// wire encoding. A different [`WebKernel`] must authenticate and validate
    /// every field with [`WebKernel::receive_signed_hol_artifact`].
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
            let Self { kernel, repl } = self;
            let source = repl
                .get_mut(ConnectionId::from_u32(connection))
                .map_err(js_error)?
                .hol_mut()
                .map_err(js_error)?;
            produce_signed_hol_artifact(kernel, source).map_err(js_error)?
        };
        Ok(WebProducedSignedHol { produced })
    }

    /// Authenticates, detached-validates, trusts, imports, and reads an artifact.
    ///
    /// All arguments are untrusted transport fields. Hash parsing and fixed
    /// widths do not confer authority; the receiver establishes authority from
    /// the signature over the exact schema-qualified image before changing its
    /// connection-local trust state.
    ///
    /// # Errors
    ///
    /// Returns a JavaScript error for malformed fields, a non-HOL connection,
    /// or the first authentication, validation, trust, import, or reader
    /// boundary rejected.
    #[expect(
        clippy::too_many_arguments,
        reason = "the deliberately unencoded transport exposes every signed field"
    )]
    pub fn receive_signed_hol_artifact(
        &mut self,
        connection: u32,
        namespace: &str,
        image: &[u8],
        schema: &str,
        image_hash: &str,
        signer: &str,
        public_key: &[u8],
        signature: &[u8],
    ) -> Result<WebReceivedHolSnapshot, JsValue> {
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
        let received =
            receive_signed_hol_artifact(self.hol_mut(connection)?, &artifact).map_err(js_error)?;
        Ok(WebReceivedHolSnapshot { received })
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
        7
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
