import initWasm, {
  smoke,
  WebHolOutcome,
  WebKernel,
  WebOutcome,
  WebRemoteProducedHol,
  WebRemoteReceivedHol,
  WebSignedKernelSession,
} from "../generated/nucleus.js";

export { smoke, WebHolOutcome, WebKernel, WebOutcome, WebSignedKernelSession };

let initialization: ReturnType<typeof initWasm> | undefined;

/** Initializes the shared main-thread Wasm module exactly once. */
export function init(): ReturnType<typeof initWasm> {
  initialization ??= initWasm();
  return initialization;
}

export interface SignedByteTransport {
  exchange(bytes: Uint8Array): Promise<Uint8Array>;
}

export class SignedKernelSessionClient {
  #pending:
    | { bytes: Uint8Array; accept(response: Uint8Array): unknown }
    | undefined;

  constructor(
    readonly transport: SignedByteTransport,
    readonly publicKey: Uint8Array,
    private readonly session: WebSignedKernelSession,
  ) {}

  async openHol(): Promise<string> {
    return this.#command(this.session.open_hol_command(), (reply) =>
      this.session.accept_open_hol(reply),
    );
  }

  async produceHol(connection: string): Promise<WebRemoteProducedHol> {
    return this.#command(
      this.session.produce_signed_hol_command(connection),
      (reply) => this.session.accept_produced_hol(reply),
    );
  }

  async receiveExternalHol(
    connection: string,
    expectedKernelId: number,
    expectedPublicKey: Uint8Array,
    artifact: WebRemoteProducedHol,
  ): Promise<WebRemoteReceivedHol> {
    return this.#command(
      this.session.receive_signed_hol_command(
        connection,
        expectedKernelId,
        expectedPublicKey,
        artifact,
      ),
      (reply) => this.session.accept_received_hol(reply),
    );
  }

  async closeHol(connection: string): Promise<void> {
    await this.#command(this.session.close_hol_command(connection), (reply) =>
      this.session.accept_closed(reply),
    );
  }

  async closeSession(): Promise<void> {
    await this.#command(this.session.close_session_command(), (reply) =>
      this.session.accept_session_closed(reply),
    );
  }

  async retryPending(): Promise<unknown> {
    const pending = this.#pending;
    if (pending === undefined) throw new Error("no signed command is pending");
    const reply = await this.transport.exchange(pending.bytes);
    const result = pending.accept(reply);
    this.#pending = undefined;
    return result;
  }

  async #command<T>(
    bytes: Uint8Array,
    accept: (response: Uint8Array) => T,
  ): Promise<T> {
    if (this.#pending !== undefined) {
      throw new Error("an exact signed command is already pending");
    }
    const pending = { bytes: bytes.slice(), accept };
    this.#pending = pending;
    const reply = await this.transport.exchange(pending.bytes);
    const result = accept(reply);
    this.#pending = undefined;
    return result;
  }
}

export async function connectSignedKernel(
  transport: SignedByteTransport,
  publicKey: Uint8Array,
): Promise<SignedKernelSessionClient> {
  await init();
  const description = await transport.exchange(
    WebSignedKernelSession.describe_request(),
  );
  const session = WebSignedKernelSession.begin(publicKey, description);
  const accepted = await transport.exchange(session.session_request());
  session.accept_session(accepted);
  return new SignedKernelSessionClient(transport, publicKey.slice(), session);
}

export type SqlValue =
  | { kind: "null" }
  | { kind: "integer"; value: string }
  | { kind: "real"; value: number }
  | { kind: "text"; value: string }
  | { kind: "blob"; value: Uint8Array };

export type SqlOutcome =
  | { kind: "changed"; changed: number }
  | { kind: "rows"; columns: string[]; rows: SqlValue[][] };

export interface HolOutcome {
  kind: "hol-theorem";
  recipe: string;
  context: string;
  conclusion: string;
  statement: string;
}

export interface SignedHolOutcome {
  kind: "signed-hol-round-trip";
  phases: string[];
  statement: string;
  conclusion: string;
  namespace: string;
  image: Uint8Array;
  schema: string;
  imageHash: string;
  signer: string;
  publicKey: Uint8Array;
  signature: Uint8Array;
  attestation: string;
  importId: string;
  importedNamespace: string;
  importedContext: string;
  importedConclusion: string;
  /** Receiver retained by the same REPL for trust/import-state inspection. */
  receiver: BrowserHolConnection;
}

type SignedHolWireOutcome = Omit<SignedHolOutcome, "receiver"> & {
  receiverConnection: number;
};

export interface BrowserSqlConnection {
  readonly kind: "sql";
  run(sql: string): Promise<SqlOutcome>;
  putImage(bytes: Uint8Array): Promise<string>;
  attachImage(hash: string, schema: string): Promise<void>;
  loadUrl(url: string, schema: string): Promise<string>;
  serializeMain(): Promise<Uint8Array>;
  close(): Promise<void>;
}

export interface BrowserHolConnection {
  readonly kind: "hol";
  run(recipe: string): Promise<HolOutcome>;
  runSignedRoundTrip(): Promise<SignedHolOutcome>;
  close(): Promise<void>;
}

export type BrowserConnection = BrowserSqlConnection | BrowserHolConnection;

export interface BrowserRepl {
  /** Opens a SQL connection. Retained as the original concise API. */
  open(): Promise<BrowserSqlConnection>;
  openSql(): Promise<BrowserSqlConnection>;
  openHol(): Promise<BrowserHolConnection>;
  close(): void;
}

type RequestBody =
  | { operation: "open" }
  | { operation: "openHol" }
  | { operation: "close"; connection: number }
  | { operation: "run"; connection: number; sql: string }
  | { operation: "runHol"; connection: number; recipe: string }
  | { operation: "runSignedHolRoundTrip"; connection: number }
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
  | { operation: "serializeMain"; connection: number };

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
    return this.openSql();
  }

  async openSql(): Promise<BrowserSqlConnection> {
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
  readonly kind = "sql" as const;
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
  readonly kind = "hol" as const;
  #closed = false;

  constructor(
    private readonly repl: WorkerRepl,
    private readonly connection: number,
  ) {}

  run(recipe: string): Promise<HolOutcome> {
    return this.#request({
      operation: "runHol",
      connection: this.connection,
      recipe,
    });
  }

  async runSignedRoundTrip(): Promise<SignedHolOutcome> {
    const wire = await this.#request<SignedHolWireOutcome>({
      operation: "runSignedHolRoundTrip",
      connection: this.connection,
    });
    const { receiverConnection, ...outcome } = wire;
    return {
      ...outcome,
      receiver: new WorkerHolConnection(this.repl, receiverConnection),
    };
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
