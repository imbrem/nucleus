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
  | { id: number; operation: "holRank"; connection: number; kind: number }
  | { id: number; operation: "holBoolType"; connection: number }
  | {
      id: number;
      operation: "holArrowType";
      connection: number;
      domain: number;
      codomain: number;
    }
  | { id: number; operation: "holType"; connection: number; type: number }
  | {
      id: number;
      operation: "holBoolTerm";
      connection: number;
      value: boolean;
    }
  | {
      id: number;
      operation: "holFreeTerm";
      connection: number;
      symbol: number;
      type: number;
    }
  | {
      id: number;
      operation: "holBoundTerm";
      connection: number;
      index: number;
      type: number;
    }
  | {
      id: number;
      operation: "holApplication";
      connection: number;
      function: number;
      argument: number;
    }
  | {
      id: number;
      operation: "holLambda";
      connection: number;
      parameterType: number;
      body: number;
    }
  | { id: number; operation: "holTerm"; connection: number; term: number }
  | { id: number; operation: "holTermType"; connection: number; term: number }
  | {
      id: number;
      operation: "holTermFreeVariables";
      connection: number;
      term: number;
    }
  | {
      id: number;
      operation: "holTermIsLocallyClosed";
      connection: number;
      term: number;
    }
  | {
      id: number;
      operation: "holTermUnboundVariables";
      connection: number;
      term: number;
    }
  | {
      id: number;
      operation: "holDefineContext";
      connection: number;
      members: number[];
    }
  | {
      id: number;
      operation: "holContextMembers";
      connection: number;
      context: number;
    }
  | {
      id: number;
      operation: "holProveHypothesis";
      connection: number;
      context: number;
      term: number;
    }
  | {
      id: number;
      operation: "holProveTruth";
      connection: number;
      context: number;
    }
  | {
      id: number;
      operation: "holProved";
      connection: number;
      context: number;
      term: number;
    };

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
    case "holBoolType":
      return connection.hol_bool_type(request.connection);
    case "holArrowType":
      return connection.hol_arrow_type(
        request.connection,
        request.domain,
        request.codomain,
      );
    case "holType": {
      const type = connection.hol_type(request.connection, request.type);
      try {
        return type.tag() === "bool"
          ? { kind: "bool" }
          : {
              kind: "arrow",
              domain: type.domain(),
              codomain: type.codomain(),
            };
      } finally {
        type.free();
      }
    }
    case "holBoolTerm":
      return connection.hol_bool_term(request.connection, request.value);
    case "holFreeTerm":
      return connection.hol_free_term(
        request.connection,
        request.symbol,
        request.type,
      );
    case "holBoundTerm":
      return connection.hol_bound_term(
        request.connection,
        request.index,
        request.type,
      );
    case "holApplication":
      return connection.hol_application(
        request.connection,
        request.function,
        request.argument,
      );
    case "holLambda":
      return connection.hol_lambda(
        request.connection,
        request.parameterType,
        request.body,
      );
    case "holTerm": {
      const term = connection.hol_term(request.connection, request.term);
      try {
        switch (term.tag()) {
          case "bool":
            return { kind: "bool", value: term.boolean() };
          case "free":
            return { kind: "free", symbol: term.symbol() };
          case "bound":
            return { kind: "bound", index: term.index() };
          case "application":
            return {
              kind: "application",
              function: term.function(),
              argument: term.argument(),
            };
          case "lambda":
            return {
              kind: "lambda",
              parameterType: term.parameter_type(),
              body: term.body(),
            };
          default:
            throw new Error("kernel returned an unknown HOL term tag");
        }
      } finally {
        term.free();
      }
    }
    case "holTermType":
      return connection.hol_term_type(request.connection, request.term);
    case "holTermFreeVariables":
      return Array.from(
        connection.hol_term_free_variables(request.connection, request.term),
      );
    case "holTermIsLocallyClosed":
      return connection.hol_term_is_locally_closed(
        request.connection,
        request.term,
      );
    case "holTermUnboundVariables": {
      const flattened = Array.from(
        connection.hol_term_unbound_variables(request.connection, request.term),
      );
      const variables = [];
      for (let index = 0; index < flattened.length; index += 2) {
        variables.push({ index: flattened[index], type: flattened[index + 1] });
      }
      return variables;
    }
    case "holDefineContext":
      return connection.hol_define_context(
        request.connection,
        new Uint32Array(request.members),
      );
    case "holContextMembers":
      return Array.from(
        connection.hol_context_members(request.connection, request.context),
      );
    case "holProveHypothesis":
      return connection.hol_prove_hypothesis(
        request.connection,
        request.context,
        request.term,
      );
    case "holProveTruth":
      return connection.hol_prove_truth(request.connection, request.context);
    case "holProved":
      return connection.hol_proved(
        request.connection,
        request.context,
        request.term,
      );
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
