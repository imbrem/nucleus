import init, {
  smoke,
  WebHolOutcome,
  WebKernel,
  WebOutcome,
  WebReplDirectory,
} from "../generated/nucleus.js";

export { init, smoke, WebHolOutcome, WebKernel, WebOutcome, WebReplDirectory };

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

/** Unencoded fields transported between independently keyed kernels. */
export interface SignedHolArtifact {
  namespace: string;
  image: Uint8Array;
  schema: string;
  imageHash: string;
  signer: string;
  publicKey: Uint8Array;
  signature: Uint8Array;
}

export interface ProducedSignedHol {
  kind: "signed-hol-artifact";
  phases: string[];
  statement: string;
  conclusion: string;
  artifact: SignedHolArtifact;
}

export interface ReceivedHolSnapshot {
  kind: "received-hol-snapshot";
  phases: string[];
  importId: string;
  namespace: string;
  context: string;
  conclusion: string;
}

/** Artifact authenticated against one independently selected endpoint key. */
export interface PinnedSignedHolArtifact {
  readonly expectedKernelId: KernelId;
  readonly signer: string;
  trustAndReceive(): Promise<ReceivedHolSnapshot>;
  abandon(): Promise<void>;
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
  produceSignedArtifact(): Promise<ProducedSignedHol>;
  stateImageHash(): Promise<string>;
  close(): Promise<void>;
}

export type BrowserConnection = BrowserSqlConnection | BrowserHolConnection;

declare const kernelIdBrand: unique symbol;
declare const managedConnectionIdBrand: unique symbol;

/** Directory-local opaque kernel endpoint ID. */
export type KernelId = number & { readonly [kernelIdBrand]: true };

/** Directory-local opaque connection ID. */
export type ManagedConnectionId = number & {
  readonly [managedConnectionIdBrand]: true;
};

export interface BrowserKernelEntry {
  id: KernelId;
  transport: string;
  endpoint?: string;
  publicKey: Uint8Array;
}

export interface BrowserConnectionEntry {
  id: ManagedConnectionId;
  kernelId: KernelId;
  protocol: string;
  remoteConnectionId?: string;
}

export interface ManagedBrowserSqlConnection extends BrowserSqlConnection {
  readonly id: ManagedConnectionId;
  readonly kernelId: KernelId;
}

export interface ManagedBrowserHolConnection extends BrowserHolConnection {
  readonly id: ManagedConnectionId;
  readonly kernelId: KernelId;
  authenticateSignedArtifact(
    expectedKernel: KernelId,
    artifact: SignedHolArtifact,
  ): Promise<PinnedSignedHolArtifact>;
}

/** One independently keyed Worker endpoint owned by a top-level directory. */
export interface BrowserKernelEndpoint {
  readonly id: KernelId;
  readonly signer: string;
  readonly publicKey: Uint8Array;
  openSql(): Promise<ManagedBrowserSqlConnection>;
  openHol(): Promise<ManagedBrowserHolConnection>;
  close(): Promise<void>;
}

/** Above-TCB coordinator for multiple independently keyed browser Workers. */
export interface BrowserReplDirectory {
  spawnWorker(endpoint?: string): Promise<BrowserKernelEndpoint>;
  kernels(): Promise<BrowserKernelEntry[]>;
  connections(): Promise<BrowserConnectionEntry[]>;
  select(connection: ManagedConnectionId): Promise<void>;
  active(): Promise<ManagedConnectionId | undefined>;
  close(): Promise<void>;
}

export interface BrowserRepl {
  /** Opens a SQL connection. Retained as the original concise API. */
  open(): Promise<BrowserSqlConnection>;
  openSql(): Promise<BrowserSqlConnection>;
  openHol(): Promise<BrowserHolConnection>;
  close(): void;
}

type RequestBody =
  | { operation: "identity" }
  | { operation: "open" }
  | { operation: "openHol" }
  | { operation: "close"; connection: number }
  | { operation: "run"; connection: number; sql: string }
  | { operation: "runHol"; connection: number; recipe: string }
  | { operation: "runSignedHolRoundTrip"; connection: number }
  | { operation: "maxImageBytes" }
  | { operation: "produceSignedHolArtifact"; connection: number }
  | { operation: "holImageHash"; connection: number }
  | {
      operation: "authenticatePinnedSignedHolArtifact";
      expectedKernel: number;
      expectedSigner: string;
      expectedPublicKey: Uint8Array;
      artifact: SignedHolArtifact;
    }
  | {
      operation: "trustPinnedSignedHolArtifact";
      connection: number;
      pinned: number;
    }
  | { operation: "abandonPinnedSignedHolArtifact"; pinned: number }
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

  async open(): Promise<WorkerConnection> {
    return this.openSql();
  }

  identity(): Promise<{ signer: string; publicKey: Uint8Array }> {
    return this.request({ operation: "identity" });
  }

  async openSql(): Promise<WorkerConnection> {
    const id = await this.request<number>({ operation: "open" });
    return new WorkerConnection(this, id);
  }

  async openHol(): Promise<WorkerHolConnection> {
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

class WorkerDirectory implements BrowserReplDirectory {
  readonly #state = init().then(() => new WebReplDirectory());
  readonly #kernels = new Map<KernelId, DirectoryKernelEndpoint>();
  #closed = false;

  async spawnWorker(endpoint?: string): Promise<BrowserKernelEndpoint> {
    if (this.#closed) throw new Error("browser REPL directory is closed");
    const worker = new WorkerRepl();
    try {
      const identity = await worker.identity();
      const state = await this.#state;
      const id = state.register_kernel(
        "worker",
        endpoint,
        identity.publicKey,
      ) as KernelId;
      const kernel = new DirectoryKernelEndpoint(
        this,
        worker,
        id,
        identity.signer,
        identity.publicKey,
      );
      this.#kernels.set(id, kernel);
      return kernel;
    } catch (error) {
      worker.close();
      throw error;
    }
  }

  async kernels(): Promise<BrowserKernelEntry[]> {
    const state = await this.#state;
    const rows: BrowserKernelEntry[] = [];
    for (let index = 0; index < state.kernel_count(); index++) {
      const row = state.kernel(index);
      try {
        rows.push({
          id: Number(row.id()) as KernelId,
          transport: row.transport(),
          endpoint: row.endpoint(),
          publicKey: row.public_key(),
        });
      } finally {
        row.free();
      }
    }
    return rows;
  }

  async connections(): Promise<BrowserConnectionEntry[]> {
    const state = await this.#state;
    const rows: BrowserConnectionEntry[] = [];
    for (let index = 0; index < state.connection_count(); index++) {
      const row = state.connection(index);
      try {
        rows.push({
          id: Number(row.id()) as ManagedConnectionId,
          kernelId: Number(row.kernel_id()) as KernelId,
          protocol: row.protocol(),
          remoteConnectionId: row.remote_connection_id(),
        });
      } finally {
        row.free();
      }
    }
    return rows;
  }

  async select(connection: ManagedConnectionId): Promise<void> {
    (await this.#state).select_connection(connection);
  }

  async active(): Promise<ManagedConnectionId | undefined> {
    return (await this.#state).active_connection() as
      | ManagedConnectionId
      | undefined;
  }

  async close(): Promise<void> {
    if (this.#closed) return;
    const kernels = [...this.#kernels.values()];
    for (const kernel of kernels) await kernel.closeAll();
    this.#closed = true;
    (await this.#state).free();
  }

  async insertConnection(
    kernelId: KernelId,
    protocol: string,
    remoteConnectionId: number,
  ): Promise<ManagedConnectionId> {
    const state = await this.#state;
    return state.insert_connection(
      kernelId,
      protocol,
      String(remoteConnectionId),
    ) as ManagedConnectionId;
  }

  async removeConnection(id: ManagedConnectionId): Promise<void> {
    (await this.#state).remove_connection(id);
  }

  async unregisterKernel(id: KernelId): Promise<void> {
    (await this.#state).unregister_kernel(id);
    this.#kernels.delete(id);
  }

  async expectedIdentity(id: KernelId): Promise<{
    kernelId: KernelId;
    publicKey: Uint8Array;
    signer: string;
  }> {
    const kernel = this.#kernels.get(id);
    if (kernel === undefined) throw new Error(`unknown kernel ${id}`);
    const rows = await this.kernels();
    const row = rows.find((entry) => entry.id === id);
    if (row === undefined) throw new Error(`unknown kernel ${id}`);
    return {
      kernelId: id,
      publicKey: row.publicKey,
      signer: kernel.signer,
    };
  }
}

class DirectoryKernelEndpoint implements BrowserKernelEndpoint {
  readonly #connections = new Set<DirectoryConnection>();
  #closed = false;

  constructor(
    private readonly directory: WorkerDirectory,
    private readonly worker: WorkerRepl,
    readonly id: KernelId,
    readonly signer: string,
    readonly publicKey: Uint8Array,
  ) {}

  async openSql(): Promise<ManagedBrowserSqlConnection> {
    this.#requireOpen();
    const remote = await this.worker.openSql();
    try {
      const id = await this.directory.insertConnection(
        this.id,
        "nucleus/sql",
        remote.connectionId,
      );
      const connection = new DirectorySqlConnection(this, remote, id);
      this.#connections.add(connection);
      return connection;
    } catch (error) {
      await remote.close();
      throw error;
    }
  }

  async openHol(): Promise<ManagedBrowserHolConnection> {
    this.#requireOpen();
    const remote = await this.worker.openHol();
    return this.adoptHol(remote);
  }

  async adoptHol(
    remote: WorkerHolConnection,
  ): Promise<ManagedBrowserHolConnection> {
    try {
      const id = await this.directory.insertConnection(
        this.id,
        "nucleus/hol",
        remote.connectionId,
      );
      const connection = new DirectoryHolConnection(this, remote, id);
      this.#connections.add(connection);
      return connection;
    } catch (error) {
      await remote.close();
      throw error;
    }
  }

  async close(): Promise<void> {
    this.#requireOpen();
    if (this.#connections.size !== 0) {
      throw new Error("kernel still has open connections");
    }
    await this.directory.unregisterKernel(this.id);
    this.#closed = true;
    this.worker.close();
  }

  async closedConnection(connection: DirectoryConnection): Promise<void> {
    this.#connections.delete(connection);
    await this.directory.removeConnection(connection.id);
  }

  expectedIdentity(id: KernelId): Promise<{
    kernelId: KernelId;
    publicKey: Uint8Array;
    signer: string;
  }> {
    return this.directory.expectedIdentity(id);
  }

  async closeAll(): Promise<void> {
    if (this.#closed) return;
    for (const connection of [...this.#connections]) await connection.close();
    await this.close();
  }

  #requireOpen(): void {
    if (this.#closed) throw new Error("kernel endpoint is closed");
  }
}

class WorkerConnection implements BrowserSqlConnection {
  readonly kind = "sql" as const;
  #closed = false;

  constructor(
    private readonly repl: WorkerRepl,
    readonly connectionId: number,
  ) {}

  run(sql: string): Promise<SqlOutcome> {
    return this.#request({
      operation: "run",
      connection: this.connectionId,
      sql,
    });
  }

  putImage(bytes: Uint8Array): Promise<string> {
    const copy = bytes.slice();
    return this.#request(
      { operation: "putImage", connection: this.connectionId, bytes: copy },
      [copy.buffer],
    );
  }

  attachImage(hash: string, schema: string): Promise<void> {
    return this.#request({
      operation: "attachImage",
      connection: this.connectionId,
      hash,
      schema,
    });
  }

  loadUrl(url: string, schema: string): Promise<string> {
    return this.#request({
      operation: "loadUrl",
      connection: this.connectionId,
      url,
      schema,
    });
  }

  serializeMain(): Promise<Uint8Array> {
    return this.#request({
      operation: "serializeMain",
      connection: this.connectionId,
    });
  }

  async close(): Promise<void> {
    if (this.#closed) return;
    this.#closed = true;
    await this.repl.request({
      operation: "close",
      connection: this.connectionId,
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
    readonly connectionId: number,
  ) {}

  run(recipe: string): Promise<HolOutcome> {
    return this.#request({
      operation: "runHol",
      connection: this.connectionId,
      recipe,
    });
  }

  async runSignedRoundTrip(): Promise<SignedHolOutcome> {
    const wire = await this.#request<SignedHolWireOutcome>({
      operation: "runSignedHolRoundTrip",
      connection: this.connectionId,
    });
    const { receiverConnection, ...outcome } = wire;
    return {
      ...outcome,
      receiver: new WorkerHolConnection(this.repl, receiverConnection),
    };
  }

  produceSignedArtifact(): Promise<ProducedSignedHol> {
    return this.#request({
      operation: "produceSignedHolArtifact",
      connection: this.connectionId,
    });
  }

  stateImageHash(): Promise<string> {
    return this.#request({
      operation: "holImageHash",
      connection: this.connectionId,
    });
  }

  async authenticateSignedArtifact(
    expected: { kernelId: KernelId; publicKey: Uint8Array; signer: string },
    artifact: SignedHolArtifact,
  ): Promise<PinnedSignedHolArtifact> {
    const limit = await this.repl.request<number>({
      operation: "maxImageBytes",
    });
    if (artifact.image.byteLength > limit) {
      throw new Error(
        `image-size-checked: image is ${artifact.image.byteLength} bytes; the limit is ${limit} bytes`,
      );
    }
    // Transfer fresh copies so crossing into the receiver Worker never detaches
    // the caller's artifact. The Worker-to-page producer path transfers its
    // buffers without copying, so ownership remains explicit in both directions.
    const transported: SignedHolArtifact = {
      ...artifact,
      image: artifact.image.slice(),
      publicKey: artifact.publicKey.slice(),
      signature: artifact.signature.slice(),
    };
    const expectedPublicKey = expected.publicKey.slice();
    const pinned = await this.#request<number>(
      {
        operation: "authenticatePinnedSignedHolArtifact",
        expectedKernel: expected.kernelId,
        expectedSigner: expected.signer,
        expectedPublicKey,
        artifact: transported,
      },
      [
        expectedPublicKey.buffer,
        transported.image.buffer,
        transported.publicKey.buffer,
        transported.signature.buffer,
      ],
    );
    return new WorkerPinnedSignedHolArtifact(
      this,
      pinned,
      expected.kernelId,
      expected.signer,
    );
  }

  trustPinned(pinned: number): Promise<ReceivedHolSnapshot> {
    return this.#request({
      operation: "trustPinnedSignedHolArtifact",
      connection: this.connectionId,
      pinned,
    });
  }

  abandonPinned(pinned: number): Promise<void> {
    return this.#request({
      operation: "abandonPinnedSignedHolArtifact",
      pinned,
    });
  }

  async close(): Promise<void> {
    if (this.#closed) return;
    this.#closed = true;
    await this.repl.request({
      operation: "close",
      connection: this.connectionId,
    });
  }

  #request<T>(body: RequestBody, transfer: Transferable[] = []): Promise<T> {
    if (this.#closed)
      return Promise.reject(new Error("HOL connection is closed"));
    return this.repl.request(body, transfer);
  }
}

class WorkerPinnedSignedHolArtifact implements PinnedSignedHolArtifact {
  #open = true;

  constructor(
    private readonly connection: WorkerHolConnection,
    private readonly pinned: number,
    readonly expectedKernelId: KernelId,
    readonly signer: string,
  ) {}

  async trustAndReceive(): Promise<ReceivedHolSnapshot> {
    if (!this.#open) throw new Error("pinned HOL artifact is closed");
    this.#open = false;
    return this.connection.trustPinned(this.pinned);
  }

  async abandon(): Promise<void> {
    if (!this.#open) return;
    this.#open = false;
    await this.connection.abandonPinned(this.pinned);
  }
}

type DirectoryConnection = DirectorySqlConnection | DirectoryHolConnection;

class DirectorySqlConnection implements ManagedBrowserSqlConnection {
  readonly kind = "sql" as const;
  readonly kernelId: KernelId;
  #closed = false;

  constructor(
    private readonly kernel: DirectoryKernelEndpoint,
    private readonly remote: WorkerConnection,
    readonly id: ManagedConnectionId,
  ) {
    this.kernelId = kernel.id;
  }

  run(sql: string): Promise<SqlOutcome> {
    return this.remote.run(sql);
  }

  putImage(bytes: Uint8Array): Promise<string> {
    return this.remote.putImage(bytes);
  }

  attachImage(hash: string, schema: string): Promise<void> {
    return this.remote.attachImage(hash, schema);
  }

  loadUrl(url: string, schema: string): Promise<string> {
    return this.remote.loadUrl(url, schema);
  }

  serializeMain(): Promise<Uint8Array> {
    return this.remote.serializeMain();
  }

  async close(): Promise<void> {
    if (this.#closed) return;
    await this.remote.close();
    this.#closed = true;
    await this.kernel.closedConnection(this);
  }
}

class DirectoryHolConnection implements ManagedBrowserHolConnection {
  readonly kind = "hol" as const;
  readonly kernelId: KernelId;
  #closed = false;

  constructor(
    private readonly kernel: DirectoryKernelEndpoint,
    private readonly remote: WorkerHolConnection,
    readonly id: ManagedConnectionId,
  ) {
    this.kernelId = kernel.id;
  }

  run(recipe: string): Promise<HolOutcome> {
    return this.remote.run(recipe);
  }

  async runSignedRoundTrip(): Promise<SignedHolOutcome> {
    // The legacy convenience still creates its receiver in the same Worker,
    // but the coordinator adopts that connection so lifecycle inspection stays
    // complete. Inter-kernel transfer uses the explicit produce/receive pair.
    const outcome = await this.remote.runSignedRoundTrip();
    const receiver = await this.kernel.adoptHol(
      outcome.receiver as WorkerHolConnection,
    );
    return { ...outcome, receiver };
  }

  produceSignedArtifact(): Promise<ProducedSignedHol> {
    return this.remote.produceSignedArtifact();
  }

  stateImageHash(): Promise<string> {
    return this.remote.stateImageHash();
  }

  async authenticateSignedArtifact(
    expectedKernel: KernelId,
    artifact: SignedHolArtifact,
  ): Promise<PinnedSignedHolArtifact> {
    const expected = await this.kernel.expectedIdentity(expectedKernel);
    return this.remote.authenticateSignedArtifact(expected, artifact);
  }

  async close(): Promise<void> {
    if (this.#closed) return;
    await this.remote.close();
    this.#closed = true;
    await this.kernel.closedConnection(this);
  }
}

/** Starts a browser REPL whose independently opened connections live in one Worker. */
export function createBrowserRepl(): BrowserRepl {
  return new WorkerRepl();
}

/** Starts an empty coordinator which can own multiple keyed Worker kernels. */
export function createBrowserReplDirectory(): BrowserReplDirectory {
  return new WorkerDirectory();
}
