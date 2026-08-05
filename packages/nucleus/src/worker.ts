import init, {
  WebKernel,
  type WebHolOutcome,
  type WebManagedTrustedHolState,
  type WebOutcome,
  type WebRemoteProducedHolComponent,
  type WebReceivedHolSnapshot,
  type WebReceivedSignedHolArtifact,
  type WebReplayedHolProofRecipe,
  type WebRetainedReceivedHolSnapshot,
  type WebSignedHolOutcome,
  type WebSignedInfinityAssumption,
  type WebSignedNatLikeMissingZero,
} from "../generated/nucleus.js";
import {
  SignedKernelTransportError,
  runNativeHttpHashSelectedArtifact,
} from "./signed-http.js";

type Request =
  | { id: number; operation: "open" }
  | { id: number; operation: "openHol" }
  | { id: number; operation: "close"; connection: number }
  | { id: number; operation: "run"; connection: number; sql: string }
  | { id: number; operation: "runHol"; connection: number; recipe: string }
  | { id: number; operation: "runSignedHolRoundTrip"; connection: number }
  | { id: number; operation: "assumeDedekindInfinity" }
  | { id: number; operation: "proveNatLikeMissingZero" }
  | { id: number; operation: "replayHolProofRecipe"; recipe: Uint8Array }
  | {
      id: number;
      operation: "receiveSignedHolArtifact";
      expectedPublicKey: Uint8Array;
      image: Uint8Array;
      sidecar: Uint8Array;
    }
  | {
      id: number;
      operation: "runNativeHttpHashSelectedHol";
      endpoint: string;
      expectedPublicKey: Uint8Array;
      component: string;
      timeoutMs: number;
    }
  | {
      id: number;
      operation: "rereadNativeHttpHashSelectedHol";
      connection: number;
    }
  | {
      id: number;
      operation: "openRetainedTrustedHolState";
      connection: number;
    }
  | {
      id: number;
      operation: "putImage";
      connection: number;
      bytes: Uint8Array;
    }
  | {
      id: number;
      operation: "attachImage";
      connection: number;
      hash: string;
      schema: string;
    }
  | {
      id: number;
      operation: "loadUrl";
      connection: number;
      url: string;
      schema: string;
    }
  | { id: number; operation: "serializeMain"; connection: number };

type SqlValue =
  | { kind: "null" }
  | { kind: "integer"; value: string }
  | { kind: "real"; value: number }
  | { kind: "text"; value: string }
  | { kind: "blob"; value: Uint8Array };

const kernel = init().then(() => new WebKernel());
let nativeHashRunInFlight = false;

interface RetainedHashSelectedArtifact {
  component: string;
  expectedSigner: string;
  expectedPublicKey: Uint8Array;
  namespace: string;
  image: Uint8Array;
  schema: string;
  imageHash: string;
  signer: string;
  publicKey: Uint8Array;
  signature: Uint8Array;
}

const retainedTrustedArtifacts = new Map<number, number>();

globalThis.addEventListener(
  "message",
  async ({ data }: MessageEvent<Request>) => {
    try {
      const value = await execute(data);
      const transfer = transferables(value);
      globalThis.postMessage({ id: data.id, ok: true, value }, { transfer });
    } catch (error) {
      globalThis.postMessage({
        id: data.id,
        ok: false,
        error: error instanceof Error ? error.message : String(error),
        outcomeUnknown:
          error instanceof SignedKernelTransportError && error.outcomeUnknown,
      });
    }
  },
);

async function execute(request: Request): Promise<unknown> {
  const connection = await kernel;
  switch (request.operation) {
    case "open":
      return connection.open_connection();
    case "openHol":
      return connection.open_hol_connection();
    case "close":
      // Keep the reread receipt until WebKernel has acknowledged connection
      // removal. A rejected close therefore leaves both available for retry.
      connection.close_connection(request.connection);
      retainedTrustedArtifacts.delete(request.connection);
      return undefined;
    case "run":
      return readOutcome(connection.run(request.connection, request.sql));
    case "runHol":
      return readHolOutcome(
        connection.run_hol(request.connection, request.recipe),
      );
    case "runSignedHolRoundTrip":
      return readSignedHolOutcome(
        connection.run_signed_hol_round_trip(request.connection),
      );
    case "assumeDedekindInfinity":
      return readSignedInfinityAssumption(
        connection,
        connection.assume_dedekind_infinity(),
      );
    case "proveNatLikeMissingZero":
      return readSignedNatLikeMissingZero(
        connection,
        connection.prove_natlike_missing_zero(),
      );
    case "replayHolProofRecipe":
      return readReplayedHolProofRecipe(
        connection,
        connection.replay_hol_proof_recipe(request.recipe),
      );
    case "receiveSignedHolArtifact":
      return readReceivedSignedHolArtifact(
        connection,
        connection.receive_signed_hol_artifact(
          request.expectedPublicKey,
          request.image,
          request.sidecar,
        ),
      );
    case "runNativeHttpHashSelectedHol":
      if (nativeHashRunInFlight) {
        throw new Error("a native hash-selected HOL run is already in flight");
      }
      nativeHashRunInFlight = true;
      try {
        return await runNativeHttpHashSelectedHol(connection, request);
      } finally {
        nativeHashRunInFlight = false;
      }
    case "rereadNativeHttpHashSelectedHol":
      return rereadNativeHttpHashSelectedHol(connection, request.connection);
    case "openRetainedTrustedHolState":
      return openRetainedTrustedHolState(connection, request.connection);
    case "putImage":
      return connection.put_image(request.connection, request.bytes);
    case "attachImage":
      connection.attach_image(request.connection, request.hash, request.schema);
      return undefined;
    case "loadUrl": {
      const response = await fetch(request.url);
      if (!response.ok) {
        throw new Error(
          `could not download SQLite image: ${response.status} ${response.statusText}`,
        );
      }
      const bytes = await readBounded(response, WebKernel.max_image_bytes());
      const hash = connection.put_image(request.connection, bytes);
      connection.attach_image(request.connection, hash, request.schema);
      return hash;
    }
    case "serializeMain":
      return connection.serialize_main(request.connection);
  }
}

async function runNativeHttpHashSelectedHol(
  connection: WebKernel,
  request: Extract<Request, { operation: "runNativeHttpHashSelectedHol" }>,
): Promise<unknown> {
  const produced = await runNativeHttpHashSelectedArtifact(request);
  try {
    const artifact: RetainedHashSelectedArtifact = {
      component: request.component,
      expectedSigner: produced.signer(),
      expectedPublicKey: request.expectedPublicKey.slice(),
      namespace: produced.namespace_id(),
      image: produced.image(),
      schema: produced.schema(),
      imageHash: produced.image_hash(),
      signer: produced.signer(),
      publicKey: produced.public_key(),
      signature: produced.signature(),
    };
    const { receiverConnection, received } = importHashSelectedArtifact(
      connection,
      artifact,
    );
    try {
      return {
        kind: "native-http-hash-selected-hol",
        component: artifact.component,
        signer: artifact.signer,
        imageBytes: artifact.image.byteLength,
        ...received,
        persistentStateHash: connection.hol_image_hash(receiverConnection),
        receiverConnection,
      };
    } catch (error) {
      // Import is not externally usable until its presentation reaches the
      // caller. Roll back the receiver if even this final read-only step fails.
      try {
        connection.close_connection(receiverConnection);
      } catch (cleanupError) {
        throw new AggregateError(
          [error, cleanupError],
          "could not roll back an unpresented HOL receiver",
        );
      } finally {
        retainedTrustedArtifacts.delete(receiverConnection);
      }
      throw error;
    }
  } finally {
    produced.free();
  }
}

function importHashSelectedArtifact(
  connection: WebKernel,
  artifact: RetainedHashSelectedArtifact,
): {
  receiverConnection: number;
  received: ReturnType<typeof readReceivedHolSnapshot>;
} {
  const receiver = connection.open_hol_connection();
  try {
    const retained = receiveHashSelectedArtifact(
      connection,
      receiver,
      artifact,
    );
    const retainedId = retained.retained_id();
    const received = readReceivedHolSnapshot(retained);
    retainedTrustedArtifacts.set(receiver, retainedId);
    return { receiverConnection: receiver, received };
  } catch (error) {
    connection.close_connection(receiver);
    throw error;
  }
}

function rereadNativeHttpHashSelectedHol(
  connection: WebKernel,
  receiver: number,
) {
  const retained = retainedTrustedArtifacts.get(receiver);
  if (retained === undefined) {
    throw new Error("trusted HOL receiver was closed or cleaned up");
  }
  const before = connection.hol_image_hash(receiver);
  const received = readReceivedHolSnapshot(
    connection.reread_received_hol_artifact(receiver, retained),
  );
  const after = connection.hol_image_hash(receiver);
  if (after !== before) {
    throw new Error("read-only HOL reread changed persistent receiver state");
  }
  return { ...received, persistentStateHash: after };
}

function openRetainedTrustedHolState(connection: WebKernel, receiver: number) {
  const retained = retainedTrustedArtifacts.get(receiver);
  if (retained === undefined) {
    throw new Error("trusted HOL receiver was closed or cleaned up");
  }
  return readManagedTrustedHolState(
    connection.open_retained_trusted_hol_state(receiver, retained),
  );
}

function readManagedTrustedHolState(state: WebManagedTrustedHolState) {
  try {
    return {
      connection: state.connection(),
      sourceNamespace: state.source_namespace_id(),
      context: state.context_id(),
      conclusion: state.conclusion_id(),
    };
  } finally {
    state.free();
  }
}

function receiveHashSelectedArtifact(
  connection: WebKernel,
  receiver: number,
  artifact: RetainedHashSelectedArtifact,
): WebRetainedReceivedHolSnapshot {
  const pinned = connection.authenticate_pinned_signed_hol_artifact(
    0xffff_fffe,
    artifact.expectedSigner,
    artifact.expectedPublicKey,
    artifact.namespace,
    artifact.image,
    artifact.schema,
    artifact.imageHash,
    artifact.signer,
    artifact.publicKey,
    artifact.signature,
  );
  return connection.trust_pinned_signed_hol_artifact_retained(receiver, pinned);
}

function readReceivedHolSnapshot(
  snapshot: WebReceivedHolSnapshot | WebRetainedReceivedHolSnapshot,
) {
  try {
    return {
      importId: snapshot.import_id(),
      namespace: snapshot.namespace_id(),
      context: snapshot.context_id(),
      conclusion: snapshot.conclusion_id(),
    };
  } finally {
    snapshot.free();
  }
}

function readSignedInfinityAssumption(
  connection: WebKernel,
  assumption: WebSignedInfinityAssumption,
) {
  return readRetainedSignedArtifact(connection, assumption, () => ({
    kind: assumption.kind(),
    authority: "signed-assumption",
    assumption: "dedekind-infinity",
    falsehood: "all-bool-identity",
    namespace: assumption.namespace_id(),
    image: assumption.image(),
    schema: assumption.schema(),
    imageHash: assumption.image_hash(),
    signer: assumption.signer(),
    publicKey: assumption.public_key(),
    signature: assumption.signature(),
    context: assumption.context_id(),
    conclusion: assumption.conclusion_id(),
    attestation: assumption.attestation_text(),
  }));
}

function readSignedNatLikeMissingZero(
  connection: WebKernel,
  theorem: WebSignedNatLikeMissingZero,
) {
  return readRetainedSignedArtifact(connection, theorem, () => ({
    kind: theorem.kind(),
    theoremOracle: theorem.theorem_oracle(),
    namespace: theorem.namespace_id(),
    image: theorem.image(),
    schema: theorem.schema(),
    imageHash: theorem.image_hash(),
    signer: theorem.signer(),
    publicKey: theorem.public_key(),
    signature: theorem.signature(),
    context: theorem.context_id(),
    conclusion: theorem.conclusion_id(),
    attestation: theorem.attestation_text(),
  }));
}

function readReplayedHolProofRecipe(
  connection: WebKernel,
  result: WebReplayedHolProofRecipe,
) {
  return readRetainedSignedArtifact(connection, result, () => ({
    kind: result.kind(),
    sourceNamespace: result.source_namespace_id(),
    image: result.image(),
    schema: result.schema(),
    imageHash: result.image_hash(),
    signer: result.signer(),
    publicKey: result.public_key(),
    signature: result.signature(),
    attestation: result.attestation_text(),
    importId: result.import_id(),
    namespace: result.imported_namespace_id(),
    importedNamespace: result.imported_namespace_id(),
    context: result.context_id(),
    conclusion: result.conclusion_id(),
    persistentStateHash: connection.hol_image_hash(
      result.receiver_connection(),
    ),
  }));
}

function readReceivedSignedHolArtifact(
  connection: WebKernel,
  artifact: WebReceivedSignedHolArtifact,
) {
  return readRetainedSignedArtifact(connection, artifact, () => ({
    kind: artifact.kind(),
    importId: artifact.import_id(),
    namespace: artifact.namespace_id(),
    context: artifact.context_id(),
    conclusion: artifact.conclusion_id(),
    attestation: artifact.attestation(),
    persistentStateHash: connection.hol_image_hash(
      artifact.receiver_connection(),
    ),
  }));
}

interface RetainedSignedArtifact {
  receiver_connection(): number;
  retained_id(): number;
  free(): void;
}

function readRetainedSignedArtifact<T extends object>(
  connection: WebKernel,
  artifact: RetainedSignedArtifact,
  read: () => T,
): T & { receiverConnection: number } {
  let receiver: number | undefined;
  try {
    const receivedConnection = artifact.receiver_connection();
    receiver = receivedConnection;
    const retained = artifact.retained_id();
    const result = {
      ...read(),
      receiverConnection: receivedConnection,
    };
    retainedTrustedArtifacts.set(receivedConnection, retained);
    return result;
  } catch (error) {
    if (receiver !== undefined) {
      try {
        connection.close_connection(receiver);
      } catch (cleanupError) {
        throw new AggregateError(
          [error, cleanupError],
          "signed artifact presentation and receiver cleanup both failed",
        );
      }
    }
    throw error;
  } finally {
    artifact.free();
  }
}

function transferables(value: unknown): ArrayBuffer[] {
  if (value instanceof Uint8Array) return [value.buffer as ArrayBuffer];
  if (
    typeof value === "object" &&
    value !== null &&
    "kind" in value &&
    (value.kind === "signed-hol-round-trip" ||
      value.kind === "signed-assumption" ||
      value.kind === "signed-natlike-missing-zero" ||
      value.kind === "signed-hol-proof-recipe")
  ) {
    const outcome = value as unknown as {
      image: Uint8Array;
      publicKey: Uint8Array;
      signature: Uint8Array;
    };
    return [
      outcome.image.buffer as ArrayBuffer,
      outcome.publicKey.buffer as ArrayBuffer,
      outcome.signature.buffer as ArrayBuffer,
    ];
  }
  return [];
}

/** Buffers a complete bounded response, refusing oversized downloads. */
async function readBounded(
  response: Response,
  limit: number,
): Promise<Uint8Array> {
  const length = response.headers.get("content-length");
  if (length !== null && Number(length) > limit) {
    throw new Error(
      `SQLite image is ${length} bytes; the limit is ${limit} bytes`,
    );
  }
  if (response.body === null) {
    const bytes = new Uint8Array(await response.arrayBuffer());
    if (bytes.byteLength > limit) {
      throw new Error(`SQLite image exceeds the ${limit}-byte limit`);
    }
    return bytes;
  }
  const reader = response.body.getReader();
  const chunks: Uint8Array[] = [];
  let total = 0;
  for (;;) {
    const { done, value } = await reader.read();
    if (done) break;
    total += value.byteLength;
    if (total > limit) {
      await reader.cancel();
      throw new Error(`SQLite image exceeds the ${limit}-byte limit`);
    }
    chunks.push(value);
  }
  const bytes = new Uint8Array(total);
  let offset = 0;
  for (const chunk of chunks) {
    bytes.set(chunk, offset);
    offset += chunk.byteLength;
  }
  return bytes;
}

function readHolOutcome(outcome: WebHolOutcome): unknown {
  try {
    return {
      kind: outcome.kind(),
      recipe: outcome.recipe(),
      context: outcome.context_id(),
      conclusion: outcome.conclusion_id(),
      statement: outcome.statement(),
    };
  } finally {
    outcome.free();
  }
}

function readSignedHolOutcome(outcome: WebSignedHolOutcome): unknown {
  try {
    const phases = Array.from({ length: outcome.phase_count() }, (_, index) =>
      outcome.phase(index),
    );
    return {
      kind: outcome.kind(),
      phases,
      statement: outcome.statement(),
      conclusion: outcome.conclusion_id(),
      namespace: outcome.namespace_id(),
      image: outcome.image(),
      schema: outcome.schema(),
      imageHash: outcome.image_hash(),
      signer: outcome.signer(),
      publicKey: outcome.public_key(),
      signature: outcome.signature(),
      attestation: outcome.attestation_text(),
      importId: outcome.import_id(),
      importedNamespace: outcome.imported_namespace_id(),
      importedContext: outcome.imported_context_id(),
      importedConclusion: outcome.imported_conclusion_id(),
      receiverConnection: outcome.receiver_connection(),
    };
  } finally {
    outcome.free();
  }
}

function readOutcome(outcome: WebOutcome): unknown {
  try {
    if (outcome.kind() === "changed") {
      return { kind: "changed", changed: outcome.changed() };
    }

    const columns = Array.from(
      { length: outcome.column_count() },
      (_, column) => outcome.column_name(column),
    );
    const rows = Array.from({ length: outcome.row_count() }, (_, row) =>
      columns.map((_, column) => readValue(outcome, row, column)),
    );
    return { kind: "rows", columns, rows };
  } finally {
    outcome.free();
  }
}

function readValue(outcome: WebOutcome, row: number, column: number): SqlValue {
  switch (outcome.value_kind(row, column)) {
    case "null":
      return { kind: "null" };
    case "integer":
      return { kind: "integer", value: outcome.integer(row, column) };
    case "real":
      return { kind: "real", value: outcome.real(row, column) };
    case "text":
      return { kind: "text", value: outcome.text(row, column) };
    case "blob":
      return { kind: "blob", value: outcome.blob(row, column) };
    default:
      throw new Error("kernel returned an unknown SQL value kind");
  }
}
