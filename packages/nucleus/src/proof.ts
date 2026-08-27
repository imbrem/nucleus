import { host as proofHost } from "../generated/proof-host/host.js";
import type { Kernel } from "../generated/proof-host/interfaces/nucleus-proof-host.js";

type GeneratedFiles = Record<string, Uint8Array>;

interface StandardProofExports {
  standard?: {
    prove(target: Uint8Array): Promise<Kernel>;
  };
  "nucleus:proof/standard@0.1.0"?: {
    prove(target: Uint8Array): Promise<Kernel>;
  };
}

interface InstantiationModule {
  instantiate(
    getCoreModule: (name: string) => Promise<WebAssembly.Module>,
    imports: Record<string, unknown>,
  ): StandardProofExports | Promise<StandardProofExports>;
}

export interface ProofStats {
  rows: bigint;
  synFacts: bigint;
}

/** The complete host API generated from `nucleus:proof/host`. */
export { proofHost };
export type { Kernel };

/** Runs a standard proof component and returns its checked kernel. */
export async function loadStandardProof(
  component: Uint8Array | ArrayBuffer,
  target: Uint8Array = new Uint8Array(32),
): Promise<Kernel> {
  if (target.length !== 32) {
    throw new Error(
      `proof targets must contain 32 bytes, got ${target.length}`,
    );
  }
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
    throw new Error("proof transpilation did not produce proof.js");
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
        throw new Error(`proof requested unknown core module ${name}`);
      }
      return WebAssembly.compile(Uint8Array.from(core).buffer);
    }, componentImports());
    const standard =
      instance.standard ?? instance["nucleus:proof/standard@0.1.0"];
    if (standard === undefined) {
      throw new Error("component does not export the standard proof interface");
    }
    const kernel = await standard.prove(target);
    if (!(kernel instanceof proofHost.Kernel)) {
      throw new Error("standard proof returned an unknown kernel resource");
    }
    return kernel;
  } finally {
    URL.revokeObjectURL(sourceUrl);
  }
}

/** Fetches and runs a standard proof component. */
export async function fetchStandardProof(
  input: RequestInfo | URL,
  init?: RequestInit,
  target?: Uint8Array,
): Promise<Kernel> {
  const response = await fetch(input, init);
  if (!response.ok) {
    throw new Error(`proof server returned ${response.status}`);
  }
  return loadStandardProof(await response.arrayBuffer(), target);
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
  };
  return {
    ...imports,
    "nucleus:proof/host@0.1.0": host,
    "nucleus:proof/capabilities@0.1.0": capabilities,
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
