import init, { WebKernel, type WebOutcome } from "../generated/nucleus.js";
import type { HolSchemaSpecV1 } from "./index.js";

type Request =
  | { id: number; operation: "open" }
  | {
      id: number;
      operation: "openHol";
      descriptor?: Uint8Array;
      schema?: HolSchemaSpecV1;
    }
  | { id: number; operation: "compileHolSchema"; schema: HolSchemaSpecV1 }
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
  | {
      id: number;
      operation: "holEquality";
      connection: number;
      left: number;
      right: number;
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
      operation: "holProveReflexivity";
      connection: number;
      context: number;
      term: number;
    }
  | {
      id: number;
      operation: "holProveBeta";
      connection: number;
      context: number;
      abstraction: number;
      argument: number;
    }
  | {
      id: number;
      operation: "holEqualityModusPonens";
      connection: number;
      context: number;
      equality: number;
      premise: number;
    }
  | {
      id: number;
      operation: "holProveContextImplication";
      connection: number;
      antecedent: number;
      consequent: number;
      witnesses: number[];
    }
  | {
      id: number;
      operation: "holWeaken";
      connection: number;
      antecedent: number;
      consequent: number;
      conclusion: number;
    }
  | {
      id: number;
      operation: "holContextImplicationProved";
      connection: number;
      antecedent: number;
      consequent: number;
    }
  | {
      id: number;
      operation: "holProved";
      connection: number;
      context: number;
      term: number;
    }
  | {
      id: number;
      operation: "holNamespaceCreate";
      connection: number;
      parent: number | null;
      name: string | null;
    }
  | {
      id: number;
      operation: "holNamespace";
      connection: number;
      namespace: number;
    }
  | {
      id: number;
      operation: "holExportBind";
      connection: number;
      namespace: number;
      exportId: number;
      sort: "kind" | "type" | "term" | "context";
      local: number;
      name?: string;
    }
  | {
      id: number;
      operation: "holNamespaceExport";
      connection: number;
      namespace: number;
      exportId: number;
    }
  | {
      id: number;
      operation: "holExportResolve";
      connection: number;
      namespace: number;
      name: string;
    }
  | { id: number; operation: "holExportSnapshot"; connection: number }
  | {
      id: number;
      operation: "holTrustImport";
      connection: number;
      schema: string;
      image: string;
      signer: string;
      publicKey: Uint8Array;
      signature: Uint8Array;
    }
  | {
      id: number;
      operation: "holTrustedImport";
      connection: number;
      trustedImportId: number;
    }
  | {
      id: number;
      operation: "holImportNamespace";
      connection: number;
      importId: number;
      sourceNamespace: number;
      parent: number | null;
      name: string | null;
    }
  | {
      id: number;
      operation: "holInspectTrustedExport";
      connection: number;
      trustedImportId: number;
      namespace: number;
      exportId: number;
      snapshot: {
        bytes: Uint8Array;
        descriptor: Uint8Array;
        schema: string;
        image: string;
        signer: string;
        publicKey: Uint8Array;
        signature: Uint8Array;
      };
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

function transferables(value: unknown): Transferable[] {
  if (value instanceof Uint8Array) return [value.buffer as ArrayBuffer];
  if (
    typeof value === "object" &&
    value !== null &&
    "bytes" in value &&
    "descriptor" in value &&
    "publicKey" in value &&
    "signature" in value
  ) {
    const snapshot = value as {
      bytes: Uint8Array;
      descriptor: Uint8Array;
      publicKey: Uint8Array;
      signature: Uint8Array;
    };
    return [
      snapshot.bytes.buffer as ArrayBuffer,
      snapshot.descriptor.buffer as ArrayBuffer,
      snapshot.publicKey.buffer as ArrayBuffer,
      snapshot.signature.buffer as ArrayBuffer,
    ];
  }
  return [];
}

async function execute(request: Request): Promise<unknown> {
  const connection = await kernel;
  switch (request.operation) {
    case "open":
      return connection.open_connection();
    case "openHol":
      if (request.descriptor !== undefined)
        return connection.open_hol_connection_with_descriptor(
          request.descriptor,
        );
      if (request.schema !== undefined)
        return connection.open_hol_connection_with_schema_json(
          JSON.stringify(request.schema),
        );
      return connection.open_hol_connection();
    case "compileHolSchema":
      return connection.compile_hol_schema_json(JSON.stringify(request.schema));
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
    case "holEquality":
      return connection.hol_equality(
        request.connection,
        request.left,
        request.right,
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
          case "equality":
            return {
              kind: "equality",
              left: term.left(),
              right: term.right(),
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
    case "holProveReflexivity":
      return connection.hol_prove_reflexivity(
        request.connection,
        request.context,
        request.term,
      );
    case "holProveBeta":
      return connection.hol_prove_beta(
        request.connection,
        request.context,
        request.abstraction,
        request.argument,
      );
    case "holEqualityModusPonens":
      return connection.hol_equality_modus_ponens(
        request.connection,
        request.context,
        request.equality,
        request.premise,
      );
    case "holProveContextImplication":
      connection.hol_prove_context_implication(
        request.connection,
        request.antecedent,
        request.consequent,
        new Uint32Array(request.witnesses),
      );
      return undefined;
    case "holWeaken":
      return connection.hol_weaken(
        request.connection,
        request.antecedent,
        request.consequent,
        request.conclusion,
      );
    case "holContextImplicationProved":
      return connection.hol_context_implication_proved(
        request.connection,
        request.antecedent,
        request.consequent,
      );
    case "holProved":
      return connection.hol_proved(
        request.connection,
        request.context,
        request.term,
      );
    case "holNamespaceCreate":
      return connection.hol_namespace_create(
        request.connection,
        request.parent ?? undefined,
        request.name ?? undefined,
      );
    case "holNamespace": {
      const namespace = connection.hol_namespace(
        request.connection,
        request.namespace,
      );
      try {
        return {
          parent: namespace.parent() ?? null,
          name: namespace.name() ?? null,
        };
      } finally {
        namespace.free();
      }
    }
    case "holExportBind":
      connection.hol_export_bind(
        request.connection,
        request.namespace,
        request.exportId,
        request.sort,
        request.local,
        request.name,
      );
      return undefined;
    case "holNamespaceExport": {
      const value = connection.hol_export(
        request.connection,
        request.namespace,
        request.exportId,
      );
      try {
        return {
          sort: value.sort(),
          local: value.local(),
          name: value.name() ?? null,
        };
      } finally {
        value.free();
      }
    }
    case "holExportResolve":
      return (
        connection.hol_export_resolve(
          request.connection,
          request.namespace,
          request.name,
        ) ?? null
      );
    case "holExportSnapshot": {
      const snapshot = connection.hol_export_snapshot(request.connection);
      try {
        return {
          bytes: snapshot.bytes(),
          descriptor: snapshot.descriptor(),
          schema: snapshot.schema(),
          image: snapshot.image(),
          signer: snapshot.signer(),
          publicKey: snapshot.public_key(),
          signature: snapshot.signature(),
        };
      } finally {
        snapshot.free();
      }
    }
    case "holTrustImport": {
      const trusted = connection.hol_trust_import(
        request.connection,
        request.schema,
        request.image,
        request.signer,
        request.publicKey,
        request.signature,
      );
      return readTrustedImport(trusted);
    }
    case "holTrustedImport": {
      const trusted = connection.hol_trusted_import(
        request.connection,
        request.trustedImportId,
      );
      return readTrustedImport(trusted);
    }
    case "holImportNamespace":
      return connection.hol_import_namespace(
        request.connection,
        request.parent,
        request.name,
        request.importId,
        request.sourceNamespace,
      );
    case "holInspectTrustedExport": {
      const snapshot = request.snapshot;
      const exported = connection.hol_inspect_trusted_export(
        request.connection,
        request.trustedImportId,
        snapshot.bytes,
        snapshot.descriptor,
        snapshot.schema,
        snapshot.image,
        snapshot.signer,
        snapshot.publicKey,
        snapshot.signature,
        request.namespace,
        request.exportId,
      );
      if (exported === undefined) return null;
      try {
        const sort = exported.sort();
        const provenance = {
          connectionId: exported.connection_id(),
          trustedImportId: exported.trusted_import_id(),
          importId: exported.import_id(),
          namespaceId: exported.namespace_id(),
          exportId: exported.export_id(),
        };
        const sourceId = exported.source_id();
        if (sort !== "term") return { ...provenance, sort, sourceId };
        const tag = exported.term_tag();
        switch (tag) {
          case "bool":
            return {
              ...provenance,
              sort,
              sourceId,
              term: { kind: tag, value: exported.boolean() },
            };
          case "free":
            return {
              ...provenance,
              sort,
              sourceId,
              term: {
                kind: tag,
                symbol: exported.source_lhs(),
                sourceType: exported.source_type(),
              },
            };
          case "bound":
            return {
              ...provenance,
              sort,
              sourceId,
              term: {
                kind: tag,
                index: exported.source_lhs(),
                sourceType: exported.source_type(),
              },
            };
          case "application":
            return {
              ...provenance,
              sort,
              sourceId,
              term: {
                kind: tag,
                sourceFunction: exported.source_lhs(),
                sourceArgument: exported.source_rhs(),
                sourceType: exported.source_type(),
              },
            };
          case "lambda":
            return {
              ...provenance,
              sort,
              sourceId,
              term: {
                kind: tag,
                sourceParameterType: exported.source_lhs(),
                sourceBody: exported.source_rhs(),
                sourceType: exported.source_type(),
              },
            };
          case "equality":
            return {
              ...provenance,
              sort,
              sourceId,
              term: {
                kind: tag,
                sourceLeft: exported.source_lhs(),
                sourceRight: exported.source_rhs(),
                sourceType: exported.source_type(),
              },
            };
          default:
            throw new Error("kernel returned an unknown imported HOL term tag");
        }
      } finally {
        exported.free();
      }
    }
  }
}

function readTrustedImport(trusted: {
  import_id(): number;
  trusted_import_id(): number;
  schema(): string;
  image(): string;
  signer(): string;
  free(): void;
}): unknown {
  try {
    return {
      importId: trusted.import_id(),
      trustedImportId: trusted.trusted_import_id(),
      schema: trusted.schema(),
      image: trusted.image(),
      signer: trusted.signer(),
    };
  } finally {
    trusted.free();
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
