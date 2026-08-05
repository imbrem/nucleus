import type {
  BrowserKernelEndpoint,
  KernelId,
  ManagedBrowserHolConnection,
  PinnedSignedHolArtifact,
  ProducedSignedHol,
  ReceivedHolSnapshot,
  SignedHolArtifact,
} from "./index.js";

export interface WitKernelIdentity {
  /** Opaque ID interpreted only by the directory which issued it. */
  directoryId: KernelId;
  signer: string;
  publicKey: Uint8Array;
}

export interface WitPinnedHolArtifact {
  readonly expectedDirectoryId: KernelId;
  readonly signer: string;
  trustImport(): Promise<ReceivedHolSnapshot>;
  abandon(): Promise<void>;
}

/** Promise-shaped host view of `crates/repl/wit/kernel.wit`. */
export interface WitHolConnection {
  betaSignExport(): Promise<ProducedSignedHol>;
  stateImageHash(): Promise<string>;
  authenticate(
    expectedDirectoryId: KernelId,
    artifact: SignedHolArtifact,
  ): Promise<WitPinnedHolArtifact>;
  close(): Promise<void>;
}

/** Promise-shaped host view of the exported `covalence:kernel/hol` interface. */
export interface WitHolKernel {
  identity(): Promise<WitKernelIdentity>;
  open(): Promise<WitHolConnection>;
}

/**
 * Presents an existing Worker kernel through the proposed WIT resource shape.
 *
 * This is orchestration only: all proof, signature, validation, and trust
 * decisions remain in the existing Rust boundaries.
 */
export class BrowserWitHolKernel implements WitHolKernel {
  constructor(private readonly endpoint: BrowserKernelEndpoint) {}

  async identity(): Promise<WitKernelIdentity> {
    return {
      directoryId: this.endpoint.id,
      signer: this.endpoint.signer,
      publicKey: this.endpoint.publicKey.slice(),
    };
  }

  async open(): Promise<WitHolConnection> {
    return new BrowserWitHolConnection(await this.endpoint.openHol());
  }
}

class BrowserWitHolConnection implements WitHolConnection {
  constructor(private readonly connection: ManagedBrowserHolConnection) {}

  betaSignExport(): Promise<ProducedSignedHol> {
    return this.connection.produceSignedArtifact();
  }

  stateImageHash(): Promise<string> {
    return this.connection.stateImageHash();
  }

  async authenticate(
    expectedDirectoryId: KernelId,
    artifact: SignedHolArtifact,
  ): Promise<WitPinnedHolArtifact> {
    const pinned = await this.connection.authenticateSignedArtifact(
      expectedDirectoryId,
      artifact,
    );
    return new BrowserWitPinnedHolArtifact(pinned);
  }

  close(): Promise<void> {
    return this.connection.close();
  }
}

class BrowserWitPinnedHolArtifact implements WitPinnedHolArtifact {
  constructor(private readonly pinned: PinnedSignedHolArtifact) {}

  get expectedDirectoryId(): KernelId {
    return this.pinned.expectedKernelId;
  }

  get signer(): string {
    return this.pinned.signer;
  }

  trustImport(): Promise<ReceivedHolSnapshot> {
    return this.pinned.trustAndReceive();
  }

  abandon(): Promise<void> {
    return this.pinned.abandon();
  }
}
