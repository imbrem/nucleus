import init, {
  WebKernel,
  type WebHolOutcome,
  type WebOutcome,
  type WebProducedSignedHol,
  type WebReceivedHolSnapshot,
  type WebSignedHolOutcome,
} from "../generated/nucleus.js";

import type { SignedHolArtifact } from "./index.js";

type Request =
  | { id: number; operation: "identity" }
  | { id: number; operation: "open" }
  | { id: number; operation: "openHol" }
  | { id: number; operation: "close"; connection: number }
  | { id: number; operation: "run"; connection: number; sql: string }
  | { id: number; operation: "runHol"; connection: number; recipe: string }
  | { id: number; operation: "runSignedHolRoundTrip"; connection: number }
  | { id: number; operation: "maxImageBytes" }
  | { id: number; operation: "produceSignedHolArtifact"; connection: number }
  | {
      id: number;
      operation: "receiveSignedHolArtifact";
      connection: number;
      artifact: SignedHolArtifact;
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
      });
    }
  },
);

async function execute(request: Request): Promise<unknown> {
  const connection = await kernel;
  switch (request.operation) {
    case "identity":
      return {
        signer: connection.signer_id(),
        publicKey: connection.public_key(),
      };
    case "open":
      return connection.open_connection();
    case "openHol":
      return connection.open_hol_connection();
    case "close":
      connection.close_connection(request.connection);
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
    case "maxImageBytes":
      return WebKernel.max_image_bytes();
    case "produceSignedHolArtifact":
      return readProducedSignedHol(
        connection.produce_signed_hol_artifact(request.connection),
      );
    case "receiveSignedHolArtifact": {
      const artifact = request.artifact;
      return readReceivedHolSnapshot(
        connection.receive_signed_hol_artifact(
          request.connection,
          artifact.namespace,
          artifact.image,
          artifact.schema,
          artifact.imageHash,
          artifact.signer,
          artifact.publicKey,
          artifact.signature,
        ),
      );
    }
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

function transferables(value: unknown): ArrayBuffer[] {
  if (value instanceof Uint8Array) return [value.buffer as ArrayBuffer];
  if (
    typeof value === "object" &&
    value !== null &&
    "signer" in value &&
    "publicKey" in value
  ) {
    return [
      (value as { publicKey: Uint8Array }).publicKey.buffer as ArrayBuffer,
    ];
  }
  if (
    typeof value === "object" &&
    value !== null &&
    "kind" in value &&
    value.kind === "signed-hol-round-trip"
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
  if (
    typeof value === "object" &&
    value !== null &&
    "kind" in value &&
    value.kind === "signed-hol-artifact"
  ) {
    const outcome = value as unknown as {
      artifact: SignedHolArtifact;
    };
    return [
      outcome.artifact.image.buffer as ArrayBuffer,
      outcome.artifact.publicKey.buffer as ArrayBuffer,
      outcome.artifact.signature.buffer as ArrayBuffer,
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

function readProducedSignedHol(outcome: WebProducedSignedHol): unknown {
  try {
    const phases = Array.from({ length: outcome.phase_count() }, (_, index) =>
      outcome.phase(index),
    );
    return {
      kind: outcome.kind(),
      phases,
      statement: outcome.statement(),
      conclusion: outcome.conclusion_id(),
      artifact: {
        namespace: outcome.namespace_id(),
        image: outcome.image(),
        schema: outcome.schema(),
        imageHash: outcome.image_hash(),
        signer: outcome.signer(),
        publicKey: outcome.public_key(),
        signature: outcome.signature(),
      },
    };
  } finally {
    outcome.free();
  }
}

function readReceivedHolSnapshot(outcome: WebReceivedHolSnapshot): unknown {
  try {
    const phases = Array.from({ length: outcome.phase_count() }, (_, index) =>
      outcome.phase(index),
    );
    return {
      kind: outcome.kind(),
      phases,
      importId: outcome.import_id(),
      namespace: outcome.namespace_id(),
      context: outcome.context_id(),
      conclusion: outcome.conclusion_id(),
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
