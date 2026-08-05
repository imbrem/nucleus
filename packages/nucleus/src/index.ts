import init, {
  smoke,
  WebHolOutcome,
  WebKernel,
  WebOutcome,
  WebRemoteHolComponentReply,
  WebRemoteProducedHol,
  WebRemoteProducedHolComponent,
  WebReplDirectory,
  WebSignedKernelSession,
} from "../generated/nucleus.js";

export {
  init,
  smoke,
  WebHolOutcome,
  WebKernel,
  WebOutcome,
  WebRemoteHolComponentReply,
  WebRemoteProducedHol,
  WebRemoteProducedHolComponent,
  WebReplDirectory,
  WebSignedKernelSession,
};

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
  connectNativeHttpHolComponent(
    options: NativeHttpHolComponentOptions,
  ): Promise<ManagedNativeHttpHolComponentEndpoint>;
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

export interface NativeHttpHolOptions {
  /** Exact endpoint URL selected independently of every signed HTTP response. */
  endpoint: string;
  /** Exact 32-byte public key obtained out of band from the native process. */
  expectedPublicKey: Uint8Array;
  /** Per-request deadline. Defaults to ten seconds. */
  timeoutMs?: number;
}

export interface NativeHttpHolComponentOptions extends NativeHttpHolOptions {
  /** Exact locally allowlisted component digest obtained out of band. */
  expectedComponent: string;
}

export interface RemoteProducedHolComponent {
  kind: "signed-hol-component-artifact";
  component: string;
  artifact: SignedHolArtifact;
}

/** Caller-owned authenticated native session for one allowlisted component. */
export interface ManagedNativeHttpHolComponentEndpoint {
  readonly id: KernelId;
  readonly signer: string;
  readonly publicKey: Uint8Array;
  readonly component: string;
  readonly sessionId: string;
  run(): Promise<RemoteProducedHolComponent>;
  retryPendingRun(): Promise<RemoteProducedHolComponent>;
  lifecycle(): Promise<string[]>;
  shutdown(): Promise<void>;
  retryPendingShutdown(): Promise<void>;
  forget(): Promise<void>;
}

export interface NativeHttpHolOutcome {
  kind: "native-http-signed-hol-round-trip";
  statement: string;
  signer: string;
  remoteConnection: string;
  imageBytes: number;
  importId: string;
  namespace: string;
  context: string;
  conclusion: string;
}

export interface ManagedNativeHttpHolOutcome extends NativeHttpHolOutcome {
  /** Live registered endpoint in the caller-owned directory. */
  kernelId: KernelId;
  /** Historical local ID whose row was removed after authenticated remote close. */
  closedConnectionId: ManagedConnectionId;
  /** Live closed session row retained for caller inspection and explicit GC. */
  sessionId: string;
  /** Convenience copy read from the caller-owned raw SQLite event table. */
  sessionLifecycle: string[];
}

/**
 * A transport failure after a stateful request may have reached the endpoint.
 * This adapter performs no explicit retry. Fetch, Chromium, or another network
 * layer may nevertheless retransmit a replayable POST. Signed command safety
 * therefore relies on #290 rejecting non-exact replays and returning a cached
 * signed reply for an exact pending command without redispatch.
 *
 * OpenSession is deliberately different: it has no cached-reply recovery. An
 * ambiguous or invalid acceptance poisons that session attempt, which callers
 * must abandon before beginning a fresh handshake.
 */
export class SignedKernelTransportError extends Error {
  readonly outcomeUnknown: boolean;

  constructor(message: string, outcomeUnknown: boolean, cause?: unknown) {
    super(message, { cause });
    this.name = "SignedKernelTransportError";
    this.outcomeUnknown = outcomeUnknown;
  }
}

/** A bounded endpoint-signed failure whose command outcome is known. */
export class SignedKernelOperationError extends Error {
  readonly outcomeUnknown = false;

  constructor(message: string) {
    super(message);
    this.name = "SignedKernelOperationError";
  }
}

/**
 * Drives a native signed kernel over bounded, explicitly pinned HTTP fetches.
 * It stops on ambiguity and never makes the low-level retry decision itself.
 */
export async function runNativeHttpSignedHol(
  options: NativeHttpHolOptions,
): Promise<NativeHttpHolOutcome> {
  await init();
  const directory = new WebReplDirectory();
  try {
    const managed = await runManagedNativeHttpSignedHol(directory, options);
    directory.forget_remote_session(managed.sessionId);
    directory.unregister_kernel(managed.kernelId);
    const {
      kernelId: _kernelId,
      closedConnectionId: _closedConnectionId,
      sessionId: _sessionId,
      sessionLifecycle: _sessionLifecycle,
      ...outcome
    } = managed;
    return outcome;
  } finally {
    directory.free();
  }
}

/**
 * Runs the signed native HTTP demo through a caller-owned REPL directory.
 * The successful return leaves the endpoint and closed session rows live for
 * independent inspection. The caller explicitly forgets the session and then
 * unregisters the endpoint when its debugging evidence is no longer needed.
 */
export async function runManagedNativeHttpSignedHol(
  directory: WebReplDirectory,
  options: NativeHttpHolOptions,
): Promise<ManagedNativeHttpHolOutcome> {
  await init();
  const timeoutMs = options.timeoutMs ?? 10_000;
  if (
    !Number.isSafeInteger(timeoutMs) ||
    timeoutMs <= 0 ||
    options.expectedPublicKey.byteLength !== 32
  ) {
    throw new Error(
      "HTTP timeout must be positive and endpoint key must be 32 bytes",
    );
  }

  const kernelId = directory.register_kernel(
    "native-http",
    options.endpoint,
    options.expectedPublicKey,
  ) as KernelId;
  let session: WebSignedKernelSession | undefined;
  let sessionId: string | undefined;
  let sessionState:
    | "opening"
    | "established"
    | "command-unknown"
    | "closing"
    | "closing-unknown"
    | "closed"
    | "failed"
    | undefined;
  let managedConnection: ManagedConnectionId | undefined;
  let local: WebKernel | undefined;
  let localConnection: number | undefined;
  try {
    const description = await signedFetch(
      options.endpoint,
      WebSignedKernelSession.describe_request(),
      timeoutMs,
      false,
    );
    session = WebSignedKernelSession.begin(
      options.expectedPublicKey,
      description,
    );
    sessionId = directory.begin_remote_session(kernelId);
    sessionState = "opening";
    const handshake = session.session_request();
    try {
      const accepted = await signedFetch(
        options.endpoint,
        handshake,
        timeoutMs,
        true,
      );
      acceptStatefulReply(() => session?.accept_session(accepted));
    } catch (error) {
      directory.transition_remote_session(sessionId, "opening-unknown");
      directory.transition_remote_session(sessionId, "failed");
      sessionState = "failed";
      throw error;
    }
    directory.transition_remote_session(sessionId, "established");
    sessionState = "established";

    local = new WebKernel();
    localConnection = local.open_hol_connection();
    const remoteConnection = await managedHttpCommand(
      directory,
      sessionId,
      options.endpoint,
      session.open_hol_command(),
      timeoutMs,
      (reply) => session?.accept_open_hol(reply) ?? "",
    ).catch((error) => {
      sessionState = "command-unknown";
      throw error;
    });
    managedConnection = directory.insert_connection(
      kernelId,
      "nucleus/hol",
      remoteConnection,
    ) as ManagedConnectionId;
    const produced = await managedHttpCommand(
      directory,
      sessionId,
      options.endpoint,
      session.produce_signed_hol_command(remoteConnection),
      timeoutMs,
      (reply) => session?.accept_produced_hol(reply),
    ).catch((error) => {
      sessionState = "command-unknown";
      throw error;
    });
    if (produced === undefined) throw new Error("signed session was lost");
    try {
      const image = produced.image();
      const publicKey = produced.public_key();
      const signature = produced.signature();
      const pinned = local.authenticate_pinned_signed_hol_artifact(
        kernelId,
        session.expected_signer(),
        options.expectedPublicKey,
        produced.namespace_id(),
        image,
        produced.schema(),
        produced.image_hash(),
        produced.signer(),
        publicKey,
        signature,
      );
      const received = local.trust_pinned_signed_hol_artifact(
        localConnection,
        pinned,
      );
      try {
        await managedHttpCommand(
          directory,
          sessionId,
          options.endpoint,
          session.close_hol_command(remoteConnection),
          timeoutMs,
          (reply) => session?.accept_closed(reply),
        ).catch((error) => {
          sessionState = "command-unknown";
          throw error;
        });
        directory.remove_connection(managedConnection);
        const closedConnectionId = managedConnection;
        managedConnection = undefined;

        const shutdown = session.shutdown_command();
        directory.transition_remote_session(sessionId, "closing");
        sessionState = "closing";
        try {
          const goodbye = await signedFetch(
            options.endpoint,
            shutdown,
            timeoutMs,
            true,
          );
          acceptStatefulReply(() => session?.accept_goodbye(goodbye));
        } catch (error) {
          directory.transition_remote_session(sessionId, "closing-unknown");
          sessionState = "closing-unknown";
          throw error;
        }
        directory.transition_remote_session(sessionId, "closed");
        sessionState = "closed";
        const sessionLifecycle = readSessionLifecycle(directory, sessionId);
        return {
          kind: "native-http-signed-hol-round-trip",
          statement: produced.statement(),
          signer: produced.signer(),
          remoteConnection,
          imageBytes: image.byteLength,
          importId: received.import_id(),
          namespace: received.namespace_id(),
          context: received.context_id(),
          conclusion: received.conclusion_id(),
          kernelId,
          closedConnectionId,
          sessionId,
          sessionLifecycle,
        };
      } finally {
        received.free();
      }
    } finally {
      produced.free();
    }
  } catch (error) {
    if (
      sessionId !== undefined &&
      sessionState !== "failed" &&
      sessionState !== "closed"
    ) {
      directory.transition_remote_session(sessionId, "failed");
    }
    throw error;
  } finally {
    if (local !== undefined && localConnection !== undefined) {
      local.close_connection(localConnection);
    }
    session?.free();
  }
}

async function managedHttpCommand<T>(
  directory: WebReplDirectory,
  sessionId: string,
  endpoint: string,
  command: Uint8Array,
  timeoutMs: number,
  accept: (reply: Uint8Array) => T,
): Promise<T> {
  try {
    const reply = await signedFetch(endpoint, command, timeoutMs, true);
    return acceptStatefulReply(() => accept(reply));
  } catch (error) {
    directory.transition_remote_session(sessionId, "command-unknown");
    throw error;
  }
}

function readSessionLifecycle(
  directory: WebReplDirectory,
  sessionId: string,
): string[] {
  const result = directory.inspect_state(
    `SELECT state FROM repl_lifecycle_event WHERE resource = 'session' AND resource_id = ${sessionId} ORDER BY event_id`,
  );
  try {
    return Array.from({ length: result.row_count() }, (_, row) =>
      result.text(row, 0),
    );
  } finally {
    result.free();
  }
}

function acceptStatefulReply<T>(accept: () => T): T {
  try {
    return accept();
  } catch (error) {
    throw new SignedKernelTransportError(
      `native signed-kernel reply could not be accepted: ${String(error)}`,
      true,
      error,
    );
  }
}

async function signedFetch(
  endpoint: string,
  body: Uint8Array,
  timeoutMs: number,
  outcomeUnknown: boolean,
): Promise<Uint8Array> {
  const controller = new AbortController();
  const timeout = setTimeout(() => controller.abort(), timeoutMs);
  try {
    const response = await fetch(endpoint, {
      method: "POST",
      mode: "cors",
      body: new Uint8Array(body).buffer as ArrayBuffer,
      redirect: "error",
      credentials: "omit",
      cache: "no-store",
      referrerPolicy: "no-referrer",
      signal: controller.signal,
      headers: { "content-type": "application/octet-stream" },
    });
    if (!response.ok) {
      throw new Error(`native kernel HTTP status ${response.status}`);
    }
    return await readBoundedResponse(
      response,
      WebSignedKernelSession.max_message_bytes(),
    );
  } catch (error) {
    throw new SignedKernelTransportError(
      `native signed-kernel request failed: ${String(error)}`,
      outcomeUnknown,
      error,
    );
  } finally {
    clearTimeout(timeout);
  }
}

function validateNativeHttpOptions(options: NativeHttpHolComponentOptions): void {
  const timeoutMs = options.timeoutMs ?? 10_000;
  if (!Number.isSafeInteger(timeoutMs) || timeoutMs <= 0) {
    throw new Error("HTTP timeout must be a positive safe integer");
  }
  if (options.expectedPublicKey.byteLength !== 32) {
    throw new Error("endpoint key must be exactly 32 bytes");
  }
  if (!/^[0-9a-f]{64}$/.test(options.expectedComponent)) {
    throw new Error("component must be a canonical lowercase O256");
  }
  const endpoint = new URL(options.endpoint);
  if (
    (endpoint.protocol !== "http:" && endpoint.protocol !== "https:") ||
    endpoint.username !== "" ||
    endpoint.password !== "" ||
    endpoint.hash !== ""
  ) {
    throw new Error("native endpoint must be an exact HTTP(S) URL");
  }
}

async function readBoundedResponse(
  response: Response,
  limit: number,
): Promise<Uint8Array> {
  const length = response.headers.get("content-length");
  if (length !== null) {
    const parsed = Number(length);
    if (!Number.isSafeInteger(parsed) || parsed < 0 || parsed > limit) {
      throw new Error(`signed response length exceeds ${limit} bytes`);
    }
  }
  if (response.body === null) {
    throw new Error("signed response has no bounded body stream");
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
      throw new Error(`signed response exceeds ${limit} bytes`);
    }
    chunks.push(value);
  }
  if (length !== null && total !== Number(length)) {
    throw new Error("signed response body is truncated");
  }
  const bytes = new Uint8Array(total);
  let offset = 0;
  for (const chunk of chunks) {
    bytes.set(chunk, offset);
    offset += chunk.byteLength;
  }
  return bytes;
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
  readonly #nativeEndpoints = new Map<
    KernelId,
    NativeHttpHolComponentEndpoint
  >();
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

  async connectNativeHttpHolComponent(
    options: NativeHttpHolComponentOptions,
  ): Promise<ManagedNativeHttpHolComponentEndpoint> {
    if (this.#closed) throw new Error("browser REPL directory is closed");
    validateNativeHttpOptions(options);
    const timeoutMs = options.timeoutMs ?? 10_000;
    const description = await signedFetch(
      options.endpoint,
      WebSignedKernelSession.describe_request(),
      timeoutMs,
      false,
    );
    const session = WebSignedKernelSession.begin(
      options.expectedPublicKey,
      description,
    );
    const state = await this.#state;
    const id = state.register_kernel(
      "native-http-hol-component",
      options.endpoint,
      options.expectedPublicKey,
    ) as KernelId;
    const sessionId = state.begin_remote_session(id);
    const endpoint = new NativeHttpHolComponentEndpoint(
      this,
      session,
      id,
      session.expected_signer(),
      options.expectedPublicKey.slice(),
      options.expectedComponent,
      sessionId,
      options.endpoint,
      timeoutMs,
    );
    this.#nativeEndpoints.set(id, endpoint);
    try {
      await endpoint.establish();
      return endpoint;
    } catch (error) {
      await endpoint.markFailed();
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
    for (const endpoint of [...this.#nativeEndpoints.values()]) {
      await endpoint.closeAll();
    }
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
    this.#nativeEndpoints.delete(id);
  }

  async transitionRemoteSession(session: string, state: string): Promise<void> {
    (await this.#state).transition_remote_session(session, state);
  }

  async remoteSessionLifecycle(session: string): Promise<string[]> {
    return readSessionLifecycle(await this.#state, session);
  }

  async forgetRemoteSession(session: string): Promise<void> {
    (await this.#state).forget_remote_session(session);
  }

  async expectedIdentity(id: KernelId): Promise<{
    kernelId: KernelId;
    publicKey: Uint8Array;
    signer: string;
  }> {
    const kernel = this.#kernels.get(id);
    const native = this.#nativeEndpoints.get(id);
    if (kernel === undefined && native === undefined)
      throw new Error(`unknown kernel ${id}`);
    const rows = await this.kernels();
    const row = rows.find((entry) => entry.id === id);
    if (row === undefined) throw new Error(`unknown kernel ${id}`);
    const signer = kernel?.signer ?? native?.signer;
    if (signer === undefined) throw new Error(`unknown kernel ${id}`);
    return {
      kernelId: id,
      publicKey: row.publicKey,
      signer,
    };
  }
}

type NativeSessionState =
  | "opening"
  | "opening-unknown"
  | "established"
  | "command-unknown"
  | "closing"
  | "closing-unknown"
  | "closed"
  | "failed";

class NativeHttpHolComponentEndpoint
  implements ManagedNativeHttpHolComponentEndpoint
{
  #state: NativeSessionState = "opening";
  #forgotten = false;

  constructor(
    private readonly directory: WorkerDirectory,
    private readonly session: WebSignedKernelSession,
    readonly id: KernelId,
    readonly signer: string,
    readonly publicKey: Uint8Array,
    readonly component: string,
    readonly sessionId: string,
    private readonly url: string,
    private readonly timeoutMs: number,
  ) {}

  async establish(): Promise<void> {
    const request = this.session.session_request();
    try {
      const response = await signedFetch(
        this.url,
        request,
        this.timeoutMs,
        true,
      );
      acceptStatefulReply(() => this.session.accept_session(response));
    } catch (error) {
      await this.directory.transitionRemoteSession(
        this.sessionId,
        "opening-unknown",
      );
      this.#state = "opening-unknown";
      throw error;
    }
    await this.directory.transitionRemoteSession(
      this.sessionId,
      "established",
    );
    this.#state = "established";
  }

  run(): Promise<RemoteProducedHolComponent> {
    if (this.#state !== "established") {
      return Promise.reject(
        new Error(`native component session is ${this.#state}`),
      );
    }
    return this.sendRun(
      this.session.run_hol_proof_component_command(this.component),
      false,
    );
  }

  retryPendingRun(): Promise<RemoteProducedHolComponent> {
    if (this.#state !== "command-unknown") {
      return Promise.reject(new Error("no ambiguous component command exists"));
    }
    return this.sendRun(this.session.retry_pending_command(), true);
  }

  lifecycle(): Promise<string[]> {
    return this.directory.remoteSessionLifecycle(this.sessionId);
  }

  async shutdown(): Promise<void> {
    if (this.#state !== "established") {
      throw new Error(`native component session is ${this.#state}`);
    }
    const command = this.session.shutdown_command();
    await this.directory.transitionRemoteSession(this.sessionId, "closing");
    this.#state = "closing";
    await this.sendShutdown(command);
  }

  async retryPendingShutdown(): Promise<void> {
    if (this.#state !== "closing-unknown") {
      throw new Error("no ambiguous shutdown command exists");
    }
    await this.sendShutdown(this.session.retry_pending_command());
  }

  async forget(): Promise<void> {
    if (this.#forgotten) return;
    if (this.#state !== "closed" && this.#state !== "failed") {
      throw new Error("native component session must be closed or failed");
    }
    await this.directory.forgetRemoteSession(this.sessionId);
    await this.directory.unregisterKernel(this.id);
    this.#forgotten = true;
    this.session.free();
  }

  async closeAll(): Promise<void> {
    if (this.#forgotten) return;
    if (this.#state === "established") {
      try {
        await this.shutdown();
      } catch {
        await this.markFailed();
      }
    } else if (this.#state !== "closed" && this.#state !== "failed") {
      await this.markFailed();
    }
    await this.forget();
  }

  async markFailed(): Promise<void> {
    if (this.#state === "failed" || this.#state === "closed") return;
    await this.directory.transitionRemoteSession(this.sessionId, "failed");
    this.#state = "failed";
  }

  async sendRun(
    command: Uint8Array,
    recovering: boolean,
  ): Promise<RemoteProducedHolComponent> {
    let response: Uint8Array;
    try {
      response = await signedFetch(
        this.url,
        command,
        this.timeoutMs,
        true,
      );
    } catch (error) {
      if (this.#state !== "command-unknown") {
        await this.directory.transitionRemoteSession(
          this.sessionId,
          "command-unknown",
        );
      }
      this.#state = "command-unknown";
      throw error;
    }

    let reply: WebRemoteHolComponentReply;
    try {
      reply = this.session.accept_hol_proof_component_reply(response);
    } catch (error) {
      if (this.#state !== "command-unknown") {
        await this.directory.transitionRemoteSession(
          this.sessionId,
          "command-unknown",
        );
      }
      this.#state = "command-unknown";
      throw new SignedKernelTransportError(
        `native signed-kernel reply could not be accepted: ${String(error)}`,
        true,
        error,
      );
    }
    try {
      if (recovering) {
        await this.directory.transitionRemoteSession(
          this.sessionId,
          "established",
        );
        this.#state = "established";
      }
      const operationError = reply.operation_error();
      if (operationError !== undefined) {
        throw new SignedKernelOperationError(operationError);
      }
      const produced = reply.take_produced();
      try {
        if (produced.component() !== this.component) {
          throw new SignedKernelOperationError(
            "signed result identifies a different component",
          );
        }
        return {
          kind: "signed-hol-component-artifact",
          component: produced.component(),
          artifact: {
            namespace: produced.namespace_id(),
            image: produced.image(),
            schema: produced.schema(),
            imageHash: produced.image_hash(),
            signer: produced.signer(),
            publicKey: produced.public_key(),
            signature: produced.signature(),
          },
        };
      } finally {
        produced.free();
      }
    } finally {
      reply.free();
    }
  }

  async sendShutdown(command: Uint8Array): Promise<void> {
    try {
      const response = await signedFetch(
        this.url,
        command,
        this.timeoutMs,
        true,
      );
      acceptStatefulReply(() => this.session.accept_goodbye(response));
    } catch (error) {
      if (this.#state !== "closing-unknown") {
        await this.directory.transitionRemoteSession(
          this.sessionId,
          "closing-unknown",
        );
      }
      this.#state = "closing-unknown";
      throw error;
    }
    await this.directory.transitionRemoteSession(this.sessionId, "closed");
    this.#state = "closed";
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
