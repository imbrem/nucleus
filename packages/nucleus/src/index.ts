import initWasm, {
  smoke,
  WebHolOutcome,
  WebKernel,
  WebOutcome,
  WebRemoteProducedHol,
  WebRemoteProducedHolComponent,
  WebRemoteReceivedHol,
  WebSignedKernelSession,
  WebSignedKernelService,
} from "../generated/nucleus.js";
import {
  SignedKernelTransportError,
  acceptStatefulReply,
  runNativeHttpHashSelectedArtifact,
  signedFetch,
} from "./signed-http.js";

export { smoke, WebHolOutcome, WebKernel, WebOutcome, WebSignedKernelSession };
export { SignedKernelTransportError };

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

  async runHolProofComponent(
    component: string,
  ): Promise<WebRemoteProducedHolComponent> {
    return this.#command(
      this.session.run_hol_proof_component_command(component),
      (reply) => this.session.accept_hol_proof_component(reply, component),
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

  async receiveExternalComponentHol(
    connection: string,
    expectedKernelId: number,
    expectedPublicKey: Uint8Array,
    artifact: WebRemoteProducedHolComponent,
  ): Promise<WebRemoteReceivedHol> {
    return this.#command(
      this.session.receive_component_signed_hol_command(
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

  /** Retries only the exact signed bytes retained after an ambiguous exchange. */
  async retryPending(): Promise<unknown> {
    const pending = this.#pending;
    if (pending === undefined) throw new Error("no signed command is pending");
    const reply = await this.transport.exchange(pending.bytes);
    try {
      const result = pending.accept(reply);
      this.#pending = undefined;
      return result;
    } catch (error) {
      if (!this.session.has_pending_command()) this.#pending = undefined;
      throw error;
    }
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
    try {
      const result = accept(reply);
      this.#pending = undefined;
      return result;
    } catch (error) {
      if (!this.session.has_pending_command()) this.#pending = undefined;
      throw error;
    }
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

/** Caller-owned in-process endpoint driven through the same signed byte API. */
export class InProcessSignedKernel implements SignedByteTransport {
  readonly #service = new WebSignedKernelService();

  private constructor() {}

  static async create(): Promise<InProcessSignedKernel> {
    await init();
    return new InProcessSignedKernel();
  }

  publicKey(): Uint8Array {
    return this.#service.public_key();
  }

  async exchange(bytes: Uint8Array): Promise<Uint8Array> {
    if (bytes.byteLength > WebSignedKernelSession.max_message_bytes()) {
      throw new Error(
        "signed in-process message exceeds the shared codec bound",
      );
    }
    const reply = this.#service.handle(bytes);
    if (reply.byteLength > WebSignedKernelSession.max_message_bytes()) {
      throw new Error("signed in-process reply exceeds the shared codec bound");
    }
    return reply;
  }

  connect(): Promise<SignedKernelSessionClient> {
    return connectSignedKernel(this, this.publicKey());
  }

  close(): void {
    this.#service.free();
  }
}

export async function createInProcessSignedKernel(): Promise<InProcessSignedKernel> {
  return InProcessSignedKernel.create();
}

export interface NativeHttpHolOptions {
  endpoint: string;
  expectedPublicKey: Uint8Array;
  timeoutMs?: number;
}

export interface NativeHttpHashSelectedHolOptions extends NativeHttpHolOptions {
  /** Canonical O256 of a component provisioned locally before server startup. */
  component: string;
}

export interface ManagedNativeHttpHolOutcome {
  kind: "native-http-signed-hol-round-trip";
  statement: string;
  signer: string;
  remoteConnection: string;
  imageBytes: number;
  importId: string;
  namespace: string;
  context: string;
  conclusion: string;
  /** Revalidates the retained artifact until `cleanup()` releases it. */
  rereadImportedTheorem(): Promise<WebRemoteReceivedHol>;
  cleanup(): Promise<void>;
}

export interface ManagedNativeHttpHashSelectedHolOutcome {
  kind: "native-http-hash-selected-hol";
  component: string;
  signer: string;
  imageBytes: number;
  importId: string;
  namespace: string;
  context: string;
  conclusion: string;
  /** Reauthenticates the exact retained artifact through the caller's receiver. */
  rereadImportedTheorem(): Promise<WebRemoteReceivedHol>;
  cleanup(): Promise<void>;
}

/**
 * Drives a pinned native producer and caller-owned signed receiver.
 *
 * This convenience flow abandons its session after any ambiguous failure.
 * Callers which need recovery must use `SignedKernelSessionClient` and its
 * exact-byte `retryPending()` operation instead.
 */
export async function runManagedNativeHttpSignedHol(
  receiver: SignedKernelSessionClient,
  receiverConnection: string,
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
  let produced: WebRemoteProducedHol | undefined;
  let cleaned = false;
  try {
    const accepted = await signedFetch(
      options.endpoint,
      session.session_request(),
      timeoutMs,
      true,
    );
    acceptStatefulReply(() => session.accept_session(accepted));
    const openReply = await signedFetch(
      options.endpoint,
      session.open_hol_command(),
      timeoutMs,
      true,
    );
    const remoteConnection = acceptStatefulReply(() =>
      session.accept_open_hol(openReply),
    );
    const producedReply = await signedFetch(
      options.endpoint,
      session.produce_signed_hol_command(remoteConnection),
      timeoutMs,
      true,
    );
    produced = acceptStatefulReply(() =>
      session.accept_produced_hol(producedReply),
    );
    const received = await receiver.receiveExternalHol(
      receiverConnection,
      0xffff_fffe,
      options.expectedPublicKey,
      produced,
    );
    const closeReply = await signedFetch(
      options.endpoint,
      session.close_hol_command(remoteConnection),
      timeoutMs,
      true,
    );
    acceptStatefulReply(() => session.accept_closed(closeReply));
    const sessionClosed = await signedFetch(
      options.endpoint,
      session.close_session_command(),
      timeoutMs,
      true,
    );
    acceptStatefulReply(() => session.accept_session_closed(sessionClosed));
    const artifact = produced;
    return {
      kind: "native-http-signed-hol-round-trip",
      statement: artifact.statement(),
      signer: artifact.signer(),
      remoteConnection,
      imageBytes: artifact.image().byteLength,
      importId: received.import_id(),
      namespace: received.namespace_id(),
      context: received.context_id(),
      conclusion: received.conclusion_id(),
      rereadImportedTheorem: () => {
        if (cleaned) {
          return Promise.reject(
            new Error("managed artifact was released by cleanup"),
          );
        }
        return receiver.receiveExternalHol(
          receiverConnection,
          0xffff_fffe,
          options.expectedPublicKey,
          artifact,
        );
      },
      async cleanup(): Promise<void> {
        if (cleaned) return;
        artifact.free();
        session.free();
        cleaned = true;
      },
    };
  } catch (error) {
    produced?.free();
    session.free();
    throw error;
  }
}

/**
 * Runs one server-provisioned component by digest and imports its signed result.
 *
 * Component bytes never enter this API or its signed/HTTP messages. The native
 * endpoint must prevalidate and precompile its exact allowlist before starting.
 * The current same-process Wasmtime/JIT prototype is tracked by nucleus#320.
 *
 * This convenience flow abandons its remote session after any ambiguous remote
 * failure, which occurs before the caller-owned receiver is mutated. If the
 * receiver exchange itself is ambiguous, `receiver.retryPending()` retains the
 * exact signed command for explicit recovery; this helper never retries it
 * automatically.
 */
export async function runManagedNativeHttpHashSelectedHol(
  receiver: SignedKernelSessionClient,
  receiverConnection: string,
  options: NativeHttpHashSelectedHolOptions,
): Promise<ManagedNativeHttpHashSelectedHolOutcome> {
  await init();
  const timeoutMs = options.timeoutMs ?? 10_000;
  const produced = await runNativeHttpHashSelectedArtifact({
    ...options,
    timeoutMs,
  });
  let cleaned = false;
  try {
    const received = await receiver.receiveExternalComponentHol(
      receiverConnection,
      0xffff_fffe,
      options.expectedPublicKey,
      produced,
    );
    const artifact = produced;
    return {
      kind: "native-http-hash-selected-hol",
      component: artifact.component(),
      signer: artifact.signer(),
      imageBytes: artifact.image().byteLength,
      importId: received.import_id(),
      namespace: received.namespace_id(),
      context: received.context_id(),
      conclusion: received.conclusion_id(),
      rereadImportedTheorem: () => {
        if (cleaned) {
          return Promise.reject(
            new Error("managed artifact was released by cleanup"),
          );
        }
        return receiver.receiveExternalComponentHol(
          receiverConnection,
          0xffff_fffe,
          options.expectedPublicKey,
          artifact,
        );
      },
      async cleanup(): Promise<void> {
        if (cleaned) return;
        artifact.free();
        cleaned = true;
      },
    };
  } catch (error) {
    produced.free();
    throw error;
  }
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

export interface BrowserReceivedHolSnapshot {
  importId: string;
  namespace: string;
  context: string;
  conclusion: string;
  /** Exact hash of persistent receiver state after this read. */
  persistentStateHash: string;
}

/** Authenticated assumption bytes plus an explicitly trusted inert receiver. */
export interface BrowserSignedInfinityAssumption {
  kind: "signed-assumption";
  authority: "signed-assumption";
  assumption: "dedekind-infinity";
  falsehood: "all-bool-identity";
  namespace: string;
  image: Uint8Array;
  schema: string;
  imageHash: string;
  signer: string;
  publicKey: Uint8Array;
  signature: Uint8Array;
  context: string;
  conclusion: string;
  attestation: string;
  receiver: BrowserHolConnection;
  openTrustedState(): Promise<BrowserManagedTrustedHolState>;
  cleanup(): Promise<void>;
}

type BrowserSignedInfinityAssumptionWire = Omit<
  BrowserSignedInfinityAssumption,
  "receiver" | "openTrustedState" | "cleanup"
> & { receiverConnection: number };

/** Exact signed `missing zero` bytes plus an explicitly trusted receiver. */
export interface BrowserSignedNatLikeMissingZero {
  kind: "signed-natlike-missing-zero";
  theoremOracle: "(APP missing zero)";
  namespace: string;
  image: Uint8Array;
  schema: string;
  imageHash: string;
  signer: string;
  publicKey: Uint8Array;
  signature: Uint8Array;
  context: string;
  conclusion: string;
  attestation: string;
  receiver: BrowserHolConnection;
  openTrustedState(): Promise<BrowserManagedTrustedHolState>;
  cleanup(): Promise<void>;
}

type BrowserSignedNatLikeMissingZeroWire = Omit<
  BrowserSignedNatLikeMissingZero,
  "receiver" | "openTrustedState" | "cleanup"
> & { receiverConnection: number };

/** Checked canonical recipe bytes plus their signed, retained kernel state. */
export interface BrowserReplayedHolProofRecipe
  extends BrowserReceivedHolSnapshot {
  kind: "signed-hol-proof-recipe";
  sourceNamespace: string;
  image: Uint8Array;
  schema: string;
  imageHash: string;
  signer: string;
  publicKey: Uint8Array;
  signature: Uint8Array;
  attestation: string;
  importedNamespace: string;
  persistentStateHash: string;
  receiver: BrowserHolConnection;
  openTrustedState(): Promise<BrowserManagedTrustedHolState>;
  cleanup(): Promise<void>;
}

type BrowserReplayedHolProofRecipeWire = Omit<
  BrowserReplayedHolProofRecipe,
  "receiver" | "openTrustedState" | "cleanup"
> & { receiverConnection: number };

/** Exact downloaded files plus a public key selected independently of them. */
export interface BrowserSignedHolArtifactInput {
  expectedPublicKey: Uint8Array;
  image: Uint8Array;
  sidecar: Uint8Array;
}

/** Authenticated, explicitly trusted import retained by the browser kernel. */
export interface BrowserReceivedSignedHolArtifact
  extends BrowserReceivedHolSnapshot {
  kind: "received-signed-hol-artifact";
  /** Bounded sidecar bytes decoded and returned verbatim, never as authority. */
  attestation: string;
  receiver: BrowserHolConnection;
  openTrustedState(): Promise<BrowserManagedTrustedHolState>;
  cleanup(): Promise<void>;
}

type BrowserReceivedSignedHolArtifactWire = Omit<
  BrowserReceivedSignedHolArtifact,
  "receiver" | "openTrustedState" | "cleanup"
> & { receiverConnection: number };

export interface BrowserNativeHttpHashSelectedHolOutcome
  extends BrowserReceivedHolSnapshot {
  kind: "native-http-hash-selected-hol";
  component: string;
  signer: string;
  imageBytes: number;
  /** Normal HOL connection retained in this BrowserRepl's Worker directory. */
  receiver: BrowserHolConnection;
  /** Reauthenticates the Worker-retained artifact and rereads the theorem. */
  rereadImportedTheorem(): Promise<BrowserReceivedHolSnapshot>;
  /** Reopens the signed database as independent writable trusted HOL state. */
  openTrustedState(): Promise<BrowserManagedTrustedHolState>;
  /** Releases the retained artifact and removes the receiver directory row. */
  cleanup(): Promise<void>;
}

type BrowserNativeHttpHashSelectedHolWire = Omit<
  BrowserNativeHttpHashSelectedHolOutcome,
  "receiver" | "rereadImportedTheorem" | "openTrustedState" | "cleanup"
> & { receiverConnection: number };

export interface BrowserManagedTrustedHolState {
  connection: BrowserHolConnection;
  sourceNamespace: string;
  context: string;
  conclusion: string;
}

type BrowserManagedTrustedHolStateWire = Omit<
  BrowserManagedTrustedHolState,
  "connection"
> & { connection: number };

export type BrowserConnection = BrowserSqlConnection | BrowserHolConnection;

export interface BrowserRepl {
  /** Opens a SQL connection. Retained as the original concise API. */
  open(): Promise<BrowserSqlConnection>;
  openSql(): Promise<BrowserSqlConnection>;
  openHol(): Promise<BrowserHolConnection>;
  assumeDedekindInfinity(): Promise<BrowserSignedInfinityAssumption>;
  proveNatLikeMissingZero(): Promise<BrowserSignedNatLikeMissingZero>;
  replayHolProofRecipe(
    recipe: Uint8Array,
  ): Promise<BrowserReplayedHolProofRecipe>;
  receiveSignedHolArtifact(
    input: BrowserSignedHolArtifactInput,
  ): Promise<BrowserReceivedSignedHolArtifact>;
  runNativeHttpHashSelectedHol(
    options: NativeHttpHashSelectedHolOptions,
  ): Promise<BrowserNativeHttpHashSelectedHolOutcome>;
  close(): void;
}

type RequestBody =
  | { operation: "open" }
  | { operation: "openHol" }
  | { operation: "close"; connection: number }
  | { operation: "run"; connection: number; sql: string }
  | { operation: "runHol"; connection: number; recipe: string }
  | { operation: "runSignedHolRoundTrip"; connection: number }
  | { operation: "assumeDedekindInfinity" }
  | { operation: "proveNatLikeMissingZero" }
  | { operation: "replayHolProofRecipe"; recipe: Uint8Array }
  | {
      operation: "receiveSignedHolArtifact";
      expectedPublicKey: Uint8Array;
      image: Uint8Array;
      sidecar: Uint8Array;
    }
  | {
      operation: "runNativeHttpHashSelectedHol";
      endpoint: string;
      expectedPublicKey: Uint8Array;
      component: string;
      timeoutMs: number;
    }
  | { operation: "rereadNativeHttpHashSelectedHol"; connection: number }
  | { operation: "openRetainedTrustedHolState"; connection: number }
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
  | { id: number; ok: false; error: string; outcomeUnknown: boolean };

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
  #nativeHashRunInFlight = false;

  constructor() {
    this.#worker.addEventListener(
      "message",
      ({ data }: MessageEvent<WorkerResponse>) => {
        const pending = this.#pending.get(data.id);
        if (pending === undefined) return;
        this.#pending.delete(data.id);
        if (data.ok) pending.resolve(data.value);
        else
          pending.reject(
            data.outcomeUnknown
              ? new SignedKernelTransportError(data.error, true)
              : new Error(data.error),
          );
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

  async assumeDedekindInfinity(): Promise<BrowserSignedInfinityAssumption> {
    const wire = await this.request<BrowserSignedInfinityAssumptionWire>({
      operation: "assumeDedekindInfinity",
    });
    return this.#retainSignedInfinityAssumption(wire);
  }

  async proveNatLikeMissingZero(): Promise<BrowserSignedNatLikeMissingZero> {
    const wire = await this.request<BrowserSignedNatLikeMissingZeroWire>({
      operation: "proveNatLikeMissingZero",
    });
    return this.#retainSignedNatLikeMissingZero(wire);
  }

  async replayHolProofRecipe(
    input: Uint8Array,
  ): Promise<BrowserReplayedHolProofRecipe> {
    const recipe = input.slice();
    const wire = await this.request<BrowserReplayedHolProofRecipeWire>(
      { operation: "replayHolProofRecipe", recipe },
      [recipe.buffer],
    );
    return this.#retainReplayedHolProofRecipe(wire);
  }

  async receiveSignedHolArtifact(
    input: BrowserSignedHolArtifactInput,
  ): Promise<BrowserReceivedSignedHolArtifact> {
    const expectedPublicKey = input.expectedPublicKey.slice();
    const image = input.image.slice();
    const sidecar = input.sidecar.slice();
    const wire = await this.request<BrowserReceivedSignedHolArtifactWire>(
      {
        operation: "receiveSignedHolArtifact",
        expectedPublicKey,
        image,
        sidecar,
      },
      [expectedPublicKey.buffer, image.buffer, sidecar.buffer],
    );
    return this.#retainReceivedSignedHolArtifact(wire);
  }

  runNativeHttpHashSelectedHol(
    options: NativeHttpHashSelectedHolOptions,
  ): Promise<BrowserNativeHttpHashSelectedHolOutcome> {
    if (this.#nativeHashRunInFlight) {
      return Promise.reject(
        new Error("a native hash-selected HOL run is already in flight"),
      );
    }
    const timeoutMs = options.timeoutMs ?? 10_000;
    const expectedPublicKey = options.expectedPublicKey.slice();
    this.#nativeHashRunInFlight = true;
    return this.request<BrowserNativeHttpHashSelectedHolWire>(
      {
        operation: "runNativeHttpHashSelectedHol",
        endpoint: options.endpoint,
        expectedPublicKey,
        component: options.component,
        timeoutMs,
      },
      [expectedPublicKey.buffer],
    )
      .then((wire) => this.#retainNativeHashSelectedOutcome(wire))
      .finally(() => {
        this.#nativeHashRunInFlight = false;
      });
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

  #retainNativeHashSelectedOutcome(
    wire: BrowserNativeHttpHashSelectedHolWire,
  ): BrowserNativeHttpHashSelectedHolOutcome {
    const { receiverConnection, ...presentation } = wire;
    const receiver = new WorkerHolConnection(this, receiverConnection);
    let cleaned = false;
    let cleanupInFlight: Promise<void> | undefined;
    return {
      ...presentation,
      receiver,
      rereadImportedTheorem: () => {
        if (cleaned)
          return Promise.reject(new Error("managed receiver was cleaned up"));
        return this.request<BrowserReceivedHolSnapshot>({
          operation: "rereadNativeHttpHashSelectedHol",
          connection: receiverConnection,
        });
      },
      openTrustedState: async () => {
        if (cleaned) throw new Error("managed receiver was cleaned up");
        const state = await this.request<BrowserManagedTrustedHolStateWire>({
          operation: "openRetainedTrustedHolState",
          connection: receiverConnection,
        });
        return {
          ...state,
          connection: new WorkerHolConnection(this, state.connection),
        };
      },
      cleanup: async () => {
        if (cleaned) return;
        cleanupInFlight ??= receiver
          .close()
          .then(() => {
            cleaned = true;
          })
          .finally(() => {
            cleanupInFlight = undefined;
          });
        await cleanupInFlight;
      },
    };
  }

  #retainSignedInfinityAssumption(
    wire: BrowserSignedInfinityAssumptionWire,
  ): BrowserSignedInfinityAssumption {
    const { receiverConnection, ...presentation } = wire;
    const receiver = new WorkerHolConnection(this, receiverConnection);
    let cleaned = false;
    let cleanupInFlight: Promise<void> | undefined;
    return {
      ...presentation,
      receiver,
      openTrustedState: async () => {
        if (cleaned)
          throw new Error("signed-assumption receiver was cleaned up");
        const state = await this.request<BrowserManagedTrustedHolStateWire>({
          operation: "openRetainedTrustedHolState",
          connection: receiverConnection,
        });
        return {
          ...state,
          connection: new WorkerHolConnection(this, state.connection),
        };
      },
      cleanup: async () => {
        if (cleaned) return;
        cleanupInFlight ??= receiver
          .close()
          .then(() => {
            cleaned = true;
          })
          .finally(() => {
            cleanupInFlight = undefined;
          });
        await cleanupInFlight;
      },
    };
  }

  #retainSignedNatLikeMissingZero(
    wire: BrowserSignedNatLikeMissingZeroWire,
  ): BrowserSignedNatLikeMissingZero {
    const { receiverConnection, ...presentation } = wire;
    const receiver = new WorkerHolConnection(this, receiverConnection);
    let cleaned = false;
    let cleanupInFlight: Promise<void> | undefined;
    return {
      ...presentation,
      receiver,
      openTrustedState: async () => {
        if (cleaned)
          throw new Error("signed missing-zero receiver was cleaned up");
        const state = await this.request<BrowserManagedTrustedHolStateWire>({
          operation: "openRetainedTrustedHolState",
          connection: receiverConnection,
        });
        return {
          ...state,
          connection: new WorkerHolConnection(this, state.connection),
        };
      },
      cleanup: async () => {
        if (cleaned) return;
        cleanupInFlight ??= receiver
          .close()
          .then(() => {
            cleaned = true;
          })
          .finally(() => {
            cleanupInFlight = undefined;
          });
        await cleanupInFlight;
      },
    };
  }

  #retainReplayedHolProofRecipe(
    wire: BrowserReplayedHolProofRecipeWire,
  ): BrowserReplayedHolProofRecipe {
    const { receiverConnection, ...presentation } = wire;
    const receiver = new WorkerHolConnection(this, receiverConnection);
    let cleaned = false;
    let cleanupInFlight: Promise<void> | undefined;
    return {
      ...presentation,
      receiver,
      openTrustedState: async () => {
        if (cleaned) throw new Error("recipe receiver was cleaned up");
        const state = await this.request<BrowserManagedTrustedHolStateWire>({
          operation: "openRetainedTrustedHolState",
          connection: receiverConnection,
        });
        return {
          ...state,
          connection: new WorkerHolConnection(this, state.connection),
        };
      },
      cleanup: async () => {
        if (cleaned) return;
        cleanupInFlight ??= receiver
          .close()
          .then(() => {
            cleaned = true;
          })
          .finally(() => {
            cleanupInFlight = undefined;
          });
        await cleanupInFlight;
      },
    };
  }

  #retainReceivedSignedHolArtifact(
    wire: BrowserReceivedSignedHolArtifactWire,
  ): BrowserReceivedSignedHolArtifact {
    const { receiverConnection, ...presentation } = wire;
    const receiver = new WorkerHolConnection(this, receiverConnection);
    let cleaned = false;
    let cleanupInFlight: Promise<void> | undefined;
    return {
      ...presentation,
      receiver,
      openTrustedState: async () => {
        if (cleaned) throw new Error("signed artifact receiver was cleaned up");
        const state = await this.request<BrowserManagedTrustedHolStateWire>({
          operation: "openRetainedTrustedHolState",
          connection: receiverConnection,
        });
        return {
          ...state,
          connection: new WorkerHolConnection(this, state.connection),
        };
      },
      cleanup: async () => {
        if (cleaned) return;
        cleanupInFlight ??= receiver
          .close()
          .then(() => {
            cleaned = true;
          })
          .finally(() => {
            cleanupInFlight = undefined;
          });
        await cleanupInFlight;
      },
    };
  }
}

class WorkerConnection implements BrowserSqlConnection {
  readonly kind = "sql" as const;
  #closed = false;
  #closing: Promise<void> | undefined;

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
    this.#closing ??= this.repl
      .request({ operation: "close", connection: this.connection })
      .then(() => {
        this.#closed = true;
      })
      .finally(() => {
        this.#closing = undefined;
      });
    await this.#closing;
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
  #closing: Promise<void> | undefined;

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
    this.#closing ??= this.repl
      .request({ operation: "close", connection: this.connection })
      .then(() => {
        this.#closed = true;
      })
      .finally(() => {
        this.#closing = undefined;
      });
    await this.#closing;
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
