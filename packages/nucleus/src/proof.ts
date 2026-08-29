import {
  host as proofHost,
  tactics as proofTactics,
} from "../generated/proof-host/host.js";
import type { Kernel } from "../generated/proof-host/interfaces/nucleus-proof-host.js";

type GeneratedFiles = Record<string, Uint8Array>;

type OptionalKernel = Kernel | undefined;

interface StrategyInterface {
  applyTactic(
    tacticId: bigint,
    arguments_: Uint8Array,
    kernel: OptionalKernel,
  ): Promise<Kernel>;
}

interface ProofExports {
  strategy?: StrategyInterface;
  "nucleus:proof/strategy@0.1.0"?: StrategyInterface;
}

interface InstantiationModule {
  instantiate(
    getCoreModule: (name: string) => Promise<WebAssembly.Module>,
    imports: Record<string, unknown>,
  ): ProofExports | Promise<ProofExports>;
}

export interface ProofStats {
  rows: bigint;
  synFacts: bigint;
}

/** The complete host API generated from `nucleus:proof/host`. */
export { proofHost };
export type { Kernel };

/** A live reusable untrusted component which constructs checked kernels. */
export class Strategy {
  readonly #exports: ProofExports;

  private constructor(exports: ProofExports) {
    this.#exports = exports;
  }

  /** Compiles and instantiates a strategy component once. */
  static async fromBytes(
    component: Uint8Array | ArrayBuffer,
  ): Promise<Strategy> {
    const { transpile } = await import("@bytecodealliance/jco");
    const bytes =
      component instanceof Uint8Array ? component : new Uint8Array(component);
    const generated = await transpile(bytes, {
      name: "proof",
      noTypescript: true,
      // The browser implementation consumes the component-model variant; its
      // public declaration currently exposes the CLI spelling instead.
      instantiation: { tag: "async" } as unknown as "async",
      asyncMode: {
        tag: "jspi",
        val: { imports: [], exports: [] },
      } as unknown as "jspi",
    });
    const rawFiles = generated.files as unknown;
    const files: GeneratedFiles = Array.isArray(rawFiles)
      ? Object.fromEntries(rawFiles as Array<[string, Uint8Array]>)
      : (rawFiles as GeneratedFiles);
    const source = files["proof.js"];
    if (source === undefined) {
      throw new Error("strategy transpilation did not produce proof.js");
    }

    const sourceBytes = Uint8Array.from(source);
    const sourceUrl = URL.createObjectURL(
      new globalThis.Blob([sourceBytes.buffer], { type: "text/javascript" }),
    );
    try {
      const module = (await import(sourceUrl)) as InstantiationModule;
      const instance = await module.instantiate(async (name) => {
        const core = files[name];
        if (core === undefined) {
          throw new Error(`strategy requested unknown core module ${name}`);
        }
        return WebAssembly.compile(Uint8Array.from(core).buffer);
      }, componentImports());
      if (
        instance.strategy === undefined &&
        instance["nucleus:proof/strategy@0.1.0"] === undefined
      ) {
        throw new Error(
          "component does not export the base strategy interface",
        );
      }
      return new Strategy(instance);
    } finally {
      URL.revokeObjectURL(sourceUrl);
    }
  }

  /** Applies a compact strategy-local tactic to a supplied or fresh kernel. */
  async applyTactic(
    tacticId: bigint,
    arguments_: Uint8Array = new Uint8Array(),
    kernel?: Kernel,
  ): Promise<Kernel> {
    const api = requiredExport(
      this.#exports.strategy ?? this.#exports["nucleus:proof/strategy@0.1.0"],
      "strategy",
    );
    return checkedKernel(await api.applyTactic(tacticId, arguments_, kernel));
  }

  /** Applies an optional human-readable tactic extension. */
  async applyTacticName(name: string, kernel?: Kernel): Promise<Kernel> {
    return this.applyTactic(1n, new TextEncoder().encode(name), kernel);
  }

  /** Runs the conventional tactic-zero addressed proof request. */
  async proveAddr(addr: Uint8Array): Promise<Kernel> {
    checkAddress(addr);
    return this.applyTactic(0n, addr);
  }
}

/** Runs tactic zero through a fresh strategy instance. */
export async function loadProof(
  component: Uint8Array | ArrayBuffer,
  arguments_: Uint8Array = new Uint8Array(),
): Promise<Kernel> {
  return (await Strategy.fromBytes(component)).applyTactic(0n, arguments_);
}

/** Fetches and runs a standard proof component. */
export async function fetchProof(
  input: RequestInfo | URL,
  init?: RequestInit,
  arguments_?: Uint8Array,
): Promise<Kernel> {
  const response = await fetch(input, init);
  if (!response.ok) {
    throw new Error(`proof server returned ${response.status}`);
  }
  return loadProof(await response.arrayBuffer(), arguments_);
}

/** Formats the kernel's checked CBOR address as lowercase hexadecimal. */
export function kernelAddress(kernel: Kernel): string {
  return hex(kernel.address());
}

/** Reads inexpensive kernel counters without serializing its arena. */
export function proofStats(kernel: Kernel): ProofStats {
  return { rows: kernel.len(), synFacts: kernel.synFactCount() };
}

function componentImports(): Record<string, unknown> {
  const maxRandomBytes = 1 << 20;
  const host = {
    ...proofHost,
    async casGetBytes(address: Uint8Array) {
      return unwrapAsyncOption(await proofHost.casGetBytes(address));
    },
    async casGetFact(address: Uint8Array) {
      return unwrapAsyncOption(await proofHost.casGetFact(address));
    },
  };
  const capabilities = {
    randomBytes(len: bigint): InstanceType<typeof proofHost.Bytes> {
      const size = Number(len);
      if (!Number.isSafeInteger(size) || size < 0 || size > maxRandomBytes) {
        throw new Error(
          `random byte request must be at most ${maxRandomBytes} bytes`,
        );
      }
      const value = new Uint8Array(size);
      for (let offset = 0; offset < value.length; offset += 65_536) {
        globalThis.crypto.getRandomValues(
          value.subarray(offset, Math.min(offset + 65_536, value.length)),
        );
      }
      return new proofHost.Bytes(value);
    },
  };
  const imports = {
    "nucleus:proof/host": host,
    "nucleus:proof/capabilities": capabilities,
    "nucleus:proof/tactics": proofTactics,
  };
  return {
    ...imports,
    "nucleus:proof/host@0.1.0": host,
    "nucleus:proof/capabilities@0.1.0": capabilities,
    "nucleus:proof/tactics@0.1.0": proofTactics,
  };
}

type AsyncOption<T> = T | undefined | { tag: "none" } | { tag: "some"; val: T };

/**
 * JCO 1.32 leaves an option wrapper around values lifted through a native
 * async export, although its generated declaration says `T | undefined`.
 * Imports into the next component require the declared canonical JS shape.
 */
function unwrapAsyncOption<T>(value: AsyncOption<T>): T | undefined {
  if (value !== null && typeof value === "object" && "tag" in value) {
    return value.tag === "some" ? value.val : undefined;
  }
  return value;
}

function hex(value: Uint8Array): string {
  return Array.from(value, (byte) => byte.toString(16).padStart(2, "0")).join(
    "",
  );
}

function requiredExport<T>(value: T | undefined, name: string): T {
  if (value === undefined) {
    throw new Error(`strategy does not export the ${name} extension`);
  }
  return value;
}

function checkedKernel(kernel: Kernel): Kernel {
  if (!(kernel instanceof proofHost.Kernel)) {
    throw new Error("strategy returned an unknown kernel resource");
  }
  return kernel;
}

function checkAddress(addr: Uint8Array): void {
  if (addr.length !== 32) {
    throw new Error(`addresses must contain 32 bytes, got ${addr.length}`);
  }
}
