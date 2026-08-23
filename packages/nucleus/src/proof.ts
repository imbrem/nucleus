import {
  environment,
  exit,
  stderr,
  stdin,
  stdout,
} from "@bytecodealliance/preview2-shim/cli";
import {
  preopens,
  types as filesystemTypes,
} from "@bytecodealliance/preview2-shim/filesystem";
import { error as ioError, streams } from "@bytecodealliance/preview2-shim/io";

import { host as proofHost } from "../generated/proof-host/host.js";
import type { Kernel } from "../generated/proof-host/interfaces/nucleus-proof-host.js";

type GeneratedFiles = Record<string, Uint8Array>;

interface StandardProofExports {
  standard?: {
    prove(): Kernel;
  };
  "nucleus:proof/standard@0.1.0"?: {
    prove(): Kernel;
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
): Promise<Kernel> {
  const { transpile } = await import("@bytecodealliance/jco");
  const bytes =
    component instanceof Uint8Array ? component : new Uint8Array(component);
  const generated = await transpile(bytes, {
    name: "proof",
    noTypescript: true,
    // The browser implementation consumes the component-model variant; its
    // public declaration currently exposes the CLI spelling instead.
    instantiation: { tag: "async" } as unknown as "async",
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
    const kernel = standard.prove();
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
): Promise<Kernel> {
  const response = await fetch(input, init);
  if (!response.ok) {
    throw new Error(`proof server returned ${response.status}`);
  }
  return loadStandardProof(await response.arrayBuffer());
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
  const imports = {
    "nucleus:proof/host": proofHost,
    "wasi:cli/environment": environment,
    "wasi:cli/exit": exit,
    "wasi:cli/stderr": stderr,
    "wasi:cli/stdin": stdin,
    "wasi:cli/stdout": stdout,
    "wasi:filesystem/preopens": preopens,
    "wasi:filesystem/types": filesystemTypes,
    "wasi:io/error": ioError,
    "wasi:io/streams": streams,
  };
  return {
    ...imports,
    "nucleus:proof/host@0.1.0": proofHost,
    "wasi:cli/environment@0.2.3": environment,
    "wasi:cli/exit@0.2.3": exit,
    "wasi:cli/stderr@0.2.3": stderr,
    "wasi:cli/stdin@0.2.3": stdin,
    "wasi:cli/stdout@0.2.3": stdout,
    "wasi:filesystem/preopens@0.2.3": preopens,
    "wasi:filesystem/types@0.2.3": filesystemTypes,
    "wasi:io/error@0.2.3": ioError,
    "wasi:io/streams@0.2.3": streams,
  };
}

function hex(value: Uint8Array): string {
  return Array.from(value, (byte) => byte.toString(16).padStart(2, "0")).join(
    "",
  );
}
