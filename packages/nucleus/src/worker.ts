import init, { WebKernel, type WebOutcome } from "../generated/nucleus.js";

type Request =
  | { id: number; operation: "open" }
  | { id: number; operation: "openHol" }
  | { id: number; operation: "close"; connection: number }
  | { id: number; operation: "run"; connection: number; sql: string }
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
  | { id: number; operation: "serializeMain"; connection: number }
  | { id: number; operation: "holStar"; connection: number }
  | {
      id: number;
      operation: "holArrow";
      connection: number;
      domain: number;
      codomain: number;
    }
  | { id: number; operation: "holKind"; connection: number; kind: number }
  | { id: number; operation: "holRank"; connection: number; kind: number };

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
      const transfer =
        value instanceof Uint8Array ? [value.buffer as ArrayBuffer] : [];
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
    case "open":
      return connection.open_connection();
    case "openHol":
      return connection.open_hol_connection();
    case "close":
      connection.close_connection(request.connection);
      return undefined;
    case "run":
      return readOutcome(connection.run(request.connection, request.sql));
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
      const bytes = new Uint8Array(await response.arrayBuffer());
      const hash = connection.put_image(request.connection, bytes);
      connection.attach_image(request.connection, hash, request.schema);
      return hash;
    }
    case "serializeMain":
      return connection.serialize_main(request.connection);
    case "holStar":
      return connection.hol_star(request.connection);
    case "holArrow":
      return connection.hol_arrow(
        request.connection,
        request.domain,
        request.codomain,
      );
    case "holKind": {
      const kind = connection.hol_kind(request.connection, request.kind);
      try {
        return kind.tag() === "star"
          ? { kind: "star" }
          : {
              kind: "arrow",
              domain: kind.domain(),
              codomain: kind.codomain(),
            };
      } finally {
        kind.free();
      }
    }
    case "holRank":
      return connection.hol_rank(request.connection, request.kind);
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
