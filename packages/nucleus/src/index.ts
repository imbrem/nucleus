import init, { smoke, WebKernel, WebOutcome } from "../generated/nucleus.js";

export { init, smoke, WebKernel, WebOutcome };

export type SqlValue =
  | { kind: "null" }
  | { kind: "integer"; value: string }
  | { kind: "real"; value: number }
  | { kind: "text"; value: string }
  | { kind: "blob"; value: Uint8Array };

export type SqlOutcome =
  | { kind: "changed"; changed: number }
  | { kind: "rows"; columns: string[]; rows: SqlValue[][] };

export type HolKind =
  | { kind: "star" }
  | { kind: "arrow"; domain: number; codomain: number };

export type HolType =
  | { kind: "bool" }
  | { kind: "arrow"; domain: number; codomain: number };

export type HolTerm =
  | { kind: "bool"; value: boolean }
  | { kind: "free"; symbol: number }
  | { kind: "bound"; index: number }
  | { kind: "application"; function: number; argument: number }
  | { kind: "lambda"; parameterType: number; body: number }
  | { kind: "equality"; left: number; right: number };

export interface HolUnboundVariable {
  index: number;
  type: number;
}

export type HolExportSort = "kind" | "type" | "term" | "context";

export interface HolNamespace {
  parent: number | null;
  name: string | null;
}

export interface HolNamespaceExport {
  sort: HolExportSort;
  local: number;
  name: string | null;
}

export interface SignedHolAttestation {
  schema: string;
  image: string;
  signer: string;
  publicKey: Uint8Array;
  signature: Uint8Array;
}

export interface ResidentHolSnapshot extends SignedHolAttestation {
  descriptor: Uint8Array;
}

export interface BrowserKernelInfo {
  id: number;
  transport: string;
  endpoint: string | null;
  publicKey: Uint8Array;
}

export interface SignedHolSnapshot extends ResidentHolSnapshot {
  bytes: Uint8Array;
}

export type HolMetadataTable =
  | "node"
  | "context"
  | "context_member"
  | "judgement"
  | "context_implication"
  | "context_union"
  | "namespace"
  | "namespace_export"
  | "import"
  | "trusted_import";

export type HolMetadataStorage = "integer" | "real" | "text" | "blob" | "any";

export interface HolMetadataColumn {
  table: HolMetadataTable;
  name: string;
  storage: HolMetadataStorage;
}

export interface HolMetadataIndex {
  table: HolMetadataTable;
  name: string;
  columns: string[];
  unique?: boolean;
}

export interface HolSchemaSpecV1 {
  version: 1;
  columns?: HolMetadataColumn[];
  indexes?: HolMetadataIndex[];
}

export type HolSchemaSource =
  | { kind: "descriptor"; descriptor: Uint8Array }
  | { kind: "schema"; schema: HolSchemaSpecV1 };

export interface TrustedHolImport {
  importId: number;
  trustedImportId: number;
  schema: string;
  image: string;
  signer: string;
}

export type ImportedHolTerm =
  | { kind: "bool"; value: boolean }
  | { kind: "free"; symbol: number; sourceType: number }
  | { kind: "bound"; index: number; sourceType: number }
  | {
      kind: "application";
      sourceFunction: number;
      sourceArgument: number;
      sourceType: number;
    }
  | {
      kind: "lambda";
      sourceParameterType: number;
      sourceBody: number;
      sourceType: number;
    }
  | {
      kind: "equality";
      sourceLeft: number;
      sourceRight: number;
      sourceType: number;
    };

export interface ImportedHolProvenance {
  connectionId: number;
  trustedImportId: number;
  importId: number;
  namespaceId: number;
  exportId: number;
}

export type ImportedHolNamespaceExport =
  | (ImportedHolProvenance & {
      sort: "kind" | "type" | "context";
      sourceId: number;
    })
  | (ImportedHolProvenance & {
      sort: "term";
      sourceId: number;
      term: ImportedHolTerm;
    });

export interface BrowserSqlConnection {
  run(sql: string): Promise<SqlOutcome>;
  putImage(bytes: Uint8Array): Promise<string>;
  attachImage(hash: string, schema: string): Promise<void>;
  loadUrl(url: string, schema: string): Promise<string>;
  serializeMain(): Promise<Uint8Array>;
  close(): Promise<void>;
}

export interface BrowserHolConnection {
  star(): Promise<number>;
  arrow(domain: number, codomain: number): Promise<number>;
  kind(id: number): Promise<HolKind>;
  rank(id: number): Promise<number>;
  boolType(): Promise<number>;
  arrowType(domain: number, codomain: number): Promise<number>;
  type(id: number): Promise<HolType>;
  boolTerm(value: boolean): Promise<number>;
  freeTerm(symbol: number, type: number): Promise<number>;
  boundTerm(index: number, type: number): Promise<number>;
  application(function_: number, argument: number): Promise<number>;
  lambda(parameterType: number, body: number): Promise<number>;
  equality(left: number, right: number): Promise<number>;
  term(id: number): Promise<HolTerm>;
  termType(id: number): Promise<number>;
  termFreeVariables(id: number): Promise<number[]>;
  termIsLocallyClosed(id: number): Promise<boolean>;
  termUnboundVariables(id: number): Promise<HolUnboundVariable[]>;
  defineContext(members: number[]): Promise<number>;
  contextMembers(id: number): Promise<number[]>;
  proveHypothesis(context: number, term: number): Promise<number>;
  proveTruth(context: number): Promise<number>;
  proveReflexivity(context: number, term: number): Promise<number>;
  proveBeta(
    context: number,
    abstraction: number,
    argument: number,
  ): Promise<number>;
  equalityModusPonens(
    context: number,
    equality: number,
    premise: number,
  ): Promise<number>;
  proveContextImplication(
    antecedent: number,
    consequent: number,
    witnesses: number[],
  ): Promise<void>;
  weaken(
    antecedent: number,
    consequent: number,
    conclusion: number,
  ): Promise<number>;
  contextImplicationProved(
    antecedent: number,
    consequent: number,
  ): Promise<boolean>;
  proved(context: number, term: number): Promise<boolean>;
  createNamespace(parent: number | null, name: string | null): Promise<number>;
  namespace(id: number): Promise<HolNamespace>;
  bindExport(
    namespace: number,
    exportId: number,
    sort: HolExportSort,
    local: number,
    name?: string,
  ): Promise<void>;
  namespaceExport(
    namespace: number,
    exportId: number,
  ): Promise<HolNamespaceExport>;
  resolveExportName(namespace: number, name: string): Promise<number | null>;
  exportSnapshot(): Promise<SignedHolSnapshot>;
  trustImport(attestation: SignedHolAttestation): Promise<TrustedHolImport>;
  trustedImport(id: number): Promise<TrustedHolImport>;
  importNamespace(
    importId: number,
    sourceNamespace: number,
    parent?: number | null,
    name?: string | null,
  ): Promise<number>;
  inspectTrustedExport(
    trustedImportId: number,
    namespace: number,
    exportId: number,
    snapshot: SignedHolSnapshot,
  ): Promise<ImportedHolNamespaceExport | null>;
  inspectResidentTrustedExport(
    trustedImportId: number,
    namespace: number,
    exportId: number,
    image: string,
  ): Promise<ImportedHolNamespaceExport | null>;
  close(): Promise<void>;
}

export interface BrowserRepl {
  open(): Promise<BrowserSqlConnection>;
  openAt(kernel: number): Promise<BrowserSqlConnection>;
  openHol(source?: HolSchemaSource): Promise<BrowserHolConnection>;
  openHolAt(
    kernel: number,
    source?: HolSchemaSource,
  ): Promise<BrowserHolConnection>;
  createKernel(): Promise<BrowserKernelInfo>;
  kernel(id: number): Promise<BrowserKernelInfo>;
  kernels(): Promise<BrowserKernelInfo[]>;
  compileHolSchema(schema: HolSchemaSpecV1): Promise<Uint8Array>;
  putHolSnapshot(snapshot: SignedHolSnapshot): Promise<string>;
  close(): void;
}

type RequestBody =
  | { operation: "open" }
  | { operation: "openAt"; kernel: number }
  | { operation: "openHol"; source?: HolSchemaSource }
  | { operation: "openHolAt"; kernel: number; source?: HolSchemaSource }
  | { operation: "createKernel" }
  | { operation: "kernel"; kernel: number }
  | { operation: "kernels" }
  | { operation: "compileHolSchema"; schema: HolSchemaSpecV1 }
  | { operation: "holPutSnapshot"; snapshot: SignedHolSnapshot }
  | { operation: "close"; connection: number }
  | { operation: "run"; connection: number; sql: string }
  | { operation: "putImage"; connection: number; bytes: Uint8Array }
  | {
      operation: "attachImage";
      connection: number;
      hash: string;
      schema: string;
    }
  | {
      operation: "loadUrl";
      connection: number;
      url: string;
      schema: string;
    }
  | { operation: "serializeMain"; connection: number }
  | { operation: "holStar"; connection: number }
  | {
      operation: "holArrow";
      connection: number;
      domain: number;
      codomain: number;
    }
  | { operation: "holKind"; connection: number; kind: number }
  | { operation: "holRank"; connection: number; kind: number }
  | { operation: "holBoolType"; connection: number }
  | {
      operation: "holArrowType";
      connection: number;
      domain: number;
      codomain: number;
    }
  | { operation: "holType"; connection: number; type: number }
  | { operation: "holBoolTerm"; connection: number; value: boolean }
  | {
      operation: "holFreeTerm";
      connection: number;
      symbol: number;
      type: number;
    }
  | {
      operation: "holBoundTerm";
      connection: number;
      index: number;
      type: number;
    }
  | {
      operation: "holApplication";
      connection: number;
      function: number;
      argument: number;
    }
  | {
      operation: "holLambda";
      connection: number;
      parameterType: number;
      body: number;
    }
  | {
      operation: "holEquality";
      connection: number;
      left: number;
      right: number;
    }
  | { operation: "holTerm"; connection: number; term: number }
  | { operation: "holTermType"; connection: number; term: number }
  | { operation: "holTermFreeVariables"; connection: number; term: number }
  | { operation: "holTermIsLocallyClosed"; connection: number; term: number }
  | { operation: "holTermUnboundVariables"; connection: number; term: number }
  | { operation: "holDefineContext"; connection: number; members: number[] }
  | { operation: "holContextMembers"; connection: number; context: number }
  | {
      operation: "holProveHypothesis";
      connection: number;
      context: number;
      term: number;
    }
  | { operation: "holProveTruth"; connection: number; context: number }
  | {
      operation: "holProveReflexivity";
      connection: number;
      context: number;
      term: number;
    }
  | {
      operation: "holProveBeta";
      connection: number;
      context: number;
      abstraction: number;
      argument: number;
    }
  | {
      operation: "holEqualityModusPonens";
      connection: number;
      context: number;
      equality: number;
      premise: number;
    }
  | {
      operation: "holProveContextImplication";
      connection: number;
      antecedent: number;
      consequent: number;
      witnesses: number[];
    }
  | {
      operation: "holWeaken";
      connection: number;
      antecedent: number;
      consequent: number;
      conclusion: number;
    }
  | {
      operation: "holContextImplicationProved";
      connection: number;
      antecedent: number;
      consequent: number;
    }
  | {
      operation: "holProved";
      connection: number;
      context: number;
      term: number;
    }
  | {
      operation: "holNamespaceCreate";
      connection: number;
      parent: number | null;
      name: string | null;
    }
  | { operation: "holNamespace"; connection: number; namespace: number }
  | {
      operation: "holExportBind";
      connection: number;
      namespace: number;
      exportId: number;
      sort: HolExportSort;
      local: number;
      name?: string;
    }
  | {
      operation: "holNamespaceExport";
      connection: number;
      namespace: number;
      exportId: number;
    }
  | {
      operation: "holExportResolve";
      connection: number;
      namespace: number;
      name: string;
    }
  | { operation: "holExportSnapshot"; connection: number }
  | {
      operation: "holTrustImport";
      connection: number;
      schema: string;
      image: string;
      signer: string;
      publicKey: Uint8Array;
      signature: Uint8Array;
    }
  | {
      operation: "holTrustedImport";
      connection: number;
      trustedImportId: number;
    }
  | {
      operation: "holImportNamespace";
      connection: number;
      importId: number;
      sourceNamespace: number;
      parent: number | null;
      name: string | null;
    }
  | {
      operation: "holInspectTrustedExport";
      connection: number;
      trustedImportId: number;
      namespace: number;
      exportId: number;
      snapshot: SignedHolSnapshot;
    }
  | {
      operation: "holInspectResidentTrustedExport";
      connection: number;
      trustedImportId: number;
      namespace: number;
      exportId: number;
      image: string;
    };

type WorkerResponse =
  | { id: number; ok: true; value: unknown }
  | { id: number; ok: false; error: string };

class WorkerRepl implements BrowserRepl {
  readonly #worker = new Worker(new URL("./worker.js", import.meta.url), {
    type: "module",
  });
  readonly #pending = new Map<
    number,
    { resolve: (value: unknown) => void; reject: (reason: Error) => void }
  >();
  #nextId = 0;
  #closed = false;

  constructor() {
    this.#worker.addEventListener(
      "message",
      ({ data }: MessageEvent<WorkerResponse>) => {
        const pending = this.#pending.get(data.id);
        if (pending === undefined) return;
        this.#pending.delete(data.id);
        if (data.ok) pending.resolve(data.value);
        else pending.reject(new Error(data.error));
      },
    );
    this.#worker.addEventListener("error", (event) => {
      this.#fail(new Error(event.message || "browser REPL worker failed"));
    });
  }

  async open(): Promise<BrowserSqlConnection> {
    const id = await this.request<number>({ operation: "open" });
    return new WorkerConnection(this, id);
  }

  async openAt(kernel: number): Promise<BrowserSqlConnection> {
    const id = await this.request<number>({ operation: "openAt", kernel });
    return new WorkerConnection(this, id);
  }

  async openHol(source?: HolSchemaSource): Promise<BrowserHolConnection> {
    return this.openHolAt(0, source);
  }

  async openHolAt(
    kernel: number,
    source?: HolSchemaSource,
  ): Promise<BrowserHolConnection> {
    if (
      source !== undefined &&
      !(
        (source.kind === "descriptor" &&
          source.descriptor instanceof Uint8Array &&
          !("schema" in source)) ||
        (source.kind === "schema" &&
          typeof source.schema === "object" &&
          source.schema !== null &&
          !("descriptor" in source))
      )
    ) {
      throw new TypeError("invalid or ambiguous HOL schema source");
    }
    const transferred =
      source?.kind === "descriptor" ? source.descriptor.slice() : undefined;
    const requestSource =
      source?.kind === "descriptor"
        ? { kind: "descriptor" as const, descriptor: transferred! }
        : source;
    const id = await this.request<number>(
      { operation: "openHolAt", kernel, source: requestSource },
      transferred === undefined ? [] : [transferred.buffer],
    );
    return new WorkerHolConnection(this, id);
  }

  async createKernel(): Promise<BrowserKernelInfo> {
    const id = await this.request<number>({ operation: "createKernel" });
    return this.kernel(id);
  }

  kernel(id: number): Promise<BrowserKernelInfo> {
    return this.request({ operation: "kernel", kernel: id });
  }

  kernels(): Promise<BrowserKernelInfo[]> {
    return this.request({ operation: "kernels" });
  }

  compileHolSchema(schema: HolSchemaSpecV1): Promise<Uint8Array> {
    return this.request({ operation: "compileHolSchema", schema });
  }

  putHolSnapshot(snapshot: SignedHolSnapshot): Promise<string> {
    const transferred = {
      ...snapshot,
      bytes: snapshot.bytes.slice(),
      descriptor: snapshot.descriptor.slice(),
      publicKey: snapshot.publicKey.slice(),
      signature: snapshot.signature.slice(),
    };
    return this.request(
      { operation: "holPutSnapshot", snapshot: transferred },
      [
        transferred.bytes.buffer,
        transferred.descriptor.buffer,
        transferred.publicKey.buffer,
        transferred.signature.buffer,
      ],
    );
  }

  close(): void {
    if (this.#closed) return;
    this.#closed = true;
    this.#worker.terminate();
    this.#fail(new Error("browser REPL is closed"));
  }

  request<T>(body: RequestBody, transfer: Transferable[] = []): Promise<T> {
    if (this.#closed)
      return Promise.reject(new Error("browser REPL is closed"));
    const id = this.#nextId++;
    return new Promise<T>((resolve, reject) => {
      this.#pending.set(id, {
        resolve: (value) => resolve(value as T),
        reject,
      });
      this.#worker.postMessage({ id, ...body }, transfer);
    });
  }

  #fail(error: Error): void {
    for (const pending of this.#pending.values()) pending.reject(error);
    this.#pending.clear();
  }
}

class WorkerConnection implements BrowserSqlConnection {
  #closed = false;

  constructor(
    private readonly repl: WorkerRepl,
    private readonly connection: number,
  ) {}

  run(sql: string): Promise<SqlOutcome> {
    return this.#request({
      operation: "run",
      connection: this.connection,
      sql,
    });
  }

  putImage(bytes: Uint8Array): Promise<string> {
    const copy = bytes.slice();
    return this.#request(
      { operation: "putImage", connection: this.connection, bytes: copy },
      [copy.buffer],
    );
  }

  attachImage(hash: string, schema: string): Promise<void> {
    return this.#request({
      operation: "attachImage",
      connection: this.connection,
      hash,
      schema,
    });
  }

  loadUrl(url: string, schema: string): Promise<string> {
    return this.#request({
      operation: "loadUrl",
      connection: this.connection,
      url,
      schema,
    });
  }

  serializeMain(): Promise<Uint8Array> {
    return this.#request({
      operation: "serializeMain",
      connection: this.connection,
    });
  }

  async close(): Promise<void> {
    if (this.#closed) return;
    this.#closed = true;
    await this.repl.request({
      operation: "close",
      connection: this.connection,
    });
  }

  #request<T>(body: RequestBody, transfer: Transferable[] = []): Promise<T> {
    if (this.#closed)
      return Promise.reject(new Error("SQL connection is closed"));
    return this.repl.request(body, transfer);
  }
}

class WorkerHolConnection implements BrowserHolConnection {
  #closed = false;

  constructor(
    private readonly repl: WorkerRepl,
    private readonly connection: number,
  ) {}

  star(): Promise<number> {
    return this.#request({ operation: "holStar", connection: this.connection });
  }

  arrow(domain: number, codomain: number): Promise<number> {
    return this.#request({
      operation: "holArrow",
      connection: this.connection,
      domain,
      codomain,
    });
  }

  kind(id: number): Promise<HolKind> {
    return this.#request({
      operation: "holKind",
      connection: this.connection,
      kind: id,
    });
  }

  rank(id: number): Promise<number> {
    return this.#request({
      operation: "holRank",
      connection: this.connection,
      kind: id,
    });
  }

  boolType(): Promise<number> {
    return this.#request({
      operation: "holBoolType",
      connection: this.connection,
    });
  }

  arrowType(domain: number, codomain: number): Promise<number> {
    return this.#request({
      operation: "holArrowType",
      connection: this.connection,
      domain,
      codomain,
    });
  }

  type(id: number): Promise<HolType> {
    return this.#request({
      operation: "holType",
      connection: this.connection,
      type: id,
    });
  }

  boolTerm(value: boolean): Promise<number> {
    return this.#request({
      operation: "holBoolTerm",
      connection: this.connection,
      value,
    });
  }

  freeTerm(symbol: number, type: number): Promise<number> {
    return this.#request({
      operation: "holFreeTerm",
      connection: this.connection,
      symbol,
      type,
    });
  }

  boundTerm(index: number, type: number): Promise<number> {
    return this.#request({
      operation: "holBoundTerm",
      connection: this.connection,
      index,
      type,
    });
  }

  application(function_: number, argument: number): Promise<number> {
    return this.#request({
      operation: "holApplication",
      connection: this.connection,
      function: function_,
      argument,
    });
  }

  lambda(parameterType: number, body: number): Promise<number> {
    return this.#request({
      operation: "holLambda",
      connection: this.connection,
      parameterType,
      body,
    });
  }

  equality(left: number, right: number): Promise<number> {
    return this.#request({
      operation: "holEquality",
      connection: this.connection,
      left,
      right,
    });
  }

  term(id: number): Promise<HolTerm> {
    return this.#request({
      operation: "holTerm",
      connection: this.connection,
      term: id,
    });
  }

  termType(id: number): Promise<number> {
    return this.#request({
      operation: "holTermType",
      connection: this.connection,
      term: id,
    });
  }

  termFreeVariables(id: number): Promise<number[]> {
    return this.#request({
      operation: "holTermFreeVariables",
      connection: this.connection,
      term: id,
    });
  }

  termIsLocallyClosed(id: number): Promise<boolean> {
    return this.#request({
      operation: "holTermIsLocallyClosed",
      connection: this.connection,
      term: id,
    });
  }

  termUnboundVariables(id: number): Promise<HolUnboundVariable[]> {
    return this.#request({
      operation: "holTermUnboundVariables",
      connection: this.connection,
      term: id,
    });
  }

  defineContext(members: number[]): Promise<number> {
    return this.#request({
      operation: "holDefineContext",
      connection: this.connection,
      members,
    });
  }

  contextMembers(id: number): Promise<number[]> {
    return this.#request({
      operation: "holContextMembers",
      connection: this.connection,
      context: id,
    });
  }

  proveHypothesis(context: number, term: number): Promise<number> {
    return this.#request({
      operation: "holProveHypothesis",
      connection: this.connection,
      context,
      term,
    });
  }

  proveTruth(context: number): Promise<number> {
    return this.#request({
      operation: "holProveTruth",
      connection: this.connection,
      context,
    });
  }

  proveReflexivity(context: number, term: number): Promise<number> {
    return this.#request({
      operation: "holProveReflexivity",
      connection: this.connection,
      context,
      term,
    });
  }

  proveBeta(
    context: number,
    abstraction: number,
    argument: number,
  ): Promise<number> {
    return this.#request({
      operation: "holProveBeta",
      connection: this.connection,
      context,
      abstraction,
      argument,
    });
  }

  equalityModusPonens(
    context: number,
    equality: number,
    premise: number,
  ): Promise<number> {
    return this.#request({
      operation: "holEqualityModusPonens",
      connection: this.connection,
      context,
      equality,
      premise,
    });
  }

  proveContextImplication(
    antecedent: number,
    consequent: number,
    witnesses: number[],
  ): Promise<void> {
    return this.#request({
      operation: "holProveContextImplication",
      connection: this.connection,
      antecedent,
      consequent,
      witnesses,
    });
  }

  weaken(
    antecedent: number,
    consequent: number,
    conclusion: number,
  ): Promise<number> {
    return this.#request({
      operation: "holWeaken",
      connection: this.connection,
      antecedent,
      consequent,
      conclusion,
    });
  }

  contextImplicationProved(
    antecedent: number,
    consequent: number,
  ): Promise<boolean> {
    return this.#request({
      operation: "holContextImplicationProved",
      connection: this.connection,
      antecedent,
      consequent,
    });
  }

  proved(context: number, term: number): Promise<boolean> {
    return this.#request({
      operation: "holProved",
      connection: this.connection,
      context,
      term,
    });
  }

  createNamespace(parent: number | null, name: string | null): Promise<number> {
    return this.#request({
      operation: "holNamespaceCreate",
      connection: this.connection,
      parent,
      name,
    });
  }

  namespace(id: number): Promise<HolNamespace> {
    return this.#request({
      operation: "holNamespace",
      connection: this.connection,
      namespace: id,
    });
  }

  bindExport(
    namespace: number,
    exportId: number,
    sort: HolExportSort,
    local: number,
    name?: string,
  ): Promise<void> {
    return this.#request({
      operation: "holExportBind",
      connection: this.connection,
      namespace,
      exportId,
      sort,
      local,
      name,
    });
  }

  namespaceExport(
    namespace: number,
    exportId: number,
  ): Promise<HolNamespaceExport> {
    return this.#request({
      operation: "holNamespaceExport",
      connection: this.connection,
      namespace,
      exportId,
    });
  }

  resolveExportName(namespace: number, name: string): Promise<number | null> {
    return this.#request({
      operation: "holExportResolve",
      connection: this.connection,
      namespace,
      name,
    });
  }

  exportSnapshot(): Promise<SignedHolSnapshot> {
    return this.#request({
      operation: "holExportSnapshot",
      connection: this.connection,
    });
  }

  trustImport(attestation: SignedHolAttestation): Promise<TrustedHolImport> {
    const publicKey = attestation.publicKey.slice();
    const signature = attestation.signature.slice();
    return this.#request(
      {
        operation: "holTrustImport",
        connection: this.connection,
        schema: attestation.schema,
        image: attestation.image,
        signer: attestation.signer,
        publicKey,
        signature,
      },
      [publicKey.buffer, signature.buffer],
    );
  }

  trustedImport(id: number): Promise<TrustedHolImport> {
    return this.#request({
      operation: "holTrustedImport",
      connection: this.connection,
      trustedImportId: id,
    });
  }

  importNamespace(
    importId: number,
    sourceNamespace: number,
    parent: number | null = null,
    name: string | null = null,
  ): Promise<number> {
    return this.#request({
      operation: "holImportNamespace",
      connection: this.connection,
      importId,
      sourceNamespace,
      parent,
      name,
    });
  }

  inspectTrustedExport(
    trustedImportId: number,
    namespace: number,
    exportId: number,
    snapshot: SignedHolSnapshot,
  ): Promise<ImportedHolNamespaceExport | null> {
    const transferred = {
      ...snapshot,
      bytes: snapshot.bytes.slice(),
      descriptor: snapshot.descriptor.slice(),
      publicKey: snapshot.publicKey.slice(),
      signature: snapshot.signature.slice(),
    };
    return this.#request(
      {
        operation: "holInspectTrustedExport",
        connection: this.connection,
        trustedImportId,
        namespace,
        exportId,
        snapshot: transferred,
      },
      [
        transferred.bytes.buffer,
        transferred.descriptor.buffer,
        transferred.publicKey.buffer,
        transferred.signature.buffer,
      ],
    );
  }

  inspectResidentTrustedExport(
    trustedImportId: number,
    namespace: number,
    exportId: number,
    image: string,
  ): Promise<ImportedHolNamespaceExport | null> {
    return this.#request({
      operation: "holInspectResidentTrustedExport",
      connection: this.connection,
      trustedImportId,
      namespace,
      exportId,
      image,
    });
  }

  async close(): Promise<void> {
    if (this.#closed) return;
    this.#closed = true;
    await this.repl.request({
      operation: "close",
      connection: this.connection,
    });
  }

  #request<T>(body: RequestBody, transfer: Transferable[] = []): Promise<T> {
    if (this.#closed)
      return Promise.reject(new Error("HOL connection is closed"));
    return this.repl.request(body, transfer);
  }
}

/** Starts a browser REPL whose independently opened connections live in one Worker. */
export function createBrowserRepl(): BrowserRepl {
  return new WorkerRepl();
}
