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
  | { kind: "lambda"; parameterType: number; body: number };

export interface HolUnboundVariable {
  index: number;
  type: number;
}

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
  term(id: number): Promise<HolTerm>;
  termType(id: number): Promise<number>;
  termFreeVariables(id: number): Promise<number[]>;
  termIsLocallyClosed(id: number): Promise<boolean>;
  termUnboundVariables(id: number): Promise<HolUnboundVariable[]>;
  defineContext(members: number[]): Promise<number>;
  contextMembers(id: number): Promise<number[]>;
  proveHypothesis(context: number, term: number): Promise<number>;
  proveTruth(context: number): Promise<number>;
  proved(context: number, term: number): Promise<boolean>;
  close(): Promise<void>;
}

export interface BrowserRepl {
  open(): Promise<BrowserSqlConnection>;
  openHol(): Promise<BrowserHolConnection>;
  close(): void;
}

type RequestBody =
  | { operation: "open" }
  | { operation: "openHol" }
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
      operation: "holProved";
      connection: number;
      context: number;
      term: number;
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

  async openHol(): Promise<BrowserHolConnection> {
    const id = await this.request<number>({ operation: "openHol" });
    return new WorkerHolConnection(this, id);
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

  proved(context: number, term: number): Promise<boolean> {
    return this.#request({
      operation: "holProved",
      connection: this.connection,
      context,
      term,
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

  #request<T>(body: RequestBody): Promise<T> {
    if (this.#closed)
      return Promise.reject(new Error("HOL connection is closed"));
    return this.repl.request(body);
  }
}

/** Starts a browser REPL whose independently opened connections live in one Worker. */
export function createBrowserRepl(): BrowserRepl {
  return new WorkerRepl();
}
