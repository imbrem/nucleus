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
import {
  error as ioError,
  streams,
} from "@bytecodealliance/preview2-shim/io";

import { ProofKernel, proofHost } from "./proof-host.js";

type GeneratedFiles = Record<string, Uint8Array>;

interface StandardProofExports {
  standard?: {
    prove(): ProofKernel;
  };
  "nucleus:proof/standard@0.1.0"?: {
    prove(): ProofKernel;
  };
}

interface InstantiationModule {
  instantiate(
    getCoreModule: (name: string) => Promise<WebAssembly.Module>,
    imports: Record<string, unknown>,
  ): StandardProofExports | Promise<StandardProofExports>;
}

/** Runs a standard proof component and returns its checked kernel. */
export async function loadStandardProof(
  component: Uint8Array | ArrayBuffer,
): Promise<ProofKernel> {
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
  // Jco's Node and browser entry points currently return different containers
  // around the same `(name, bytes)` files.
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
    const instance = await module.instantiate(
      async (name) => {
        const core = files[name];
        if (core === undefined) {
          throw new Error(`proof requested unknown core module ${name}`);
        }
        return WebAssembly.compile(Uint8Array.from(core).buffer);
      },
      componentImports(),
    );
    const standard =
      instance.standard ?? instance["nucleus:proof/standard@0.1.0"];
    if (standard === undefined) {
      throw new Error("component does not export the standard proof interface");
    }
    const kernel = standard.prove();
    if (!(kernel instanceof ProofKernel)) {
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
): Promise<ProofKernel> {
  const response = await fetch(input, init);
  if (!response.ok) {
    throw new Error(`proof server returned ${response.status}`);
  }
  return loadStandardProof(await response.arrayBuffer());
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

  // Jco currently requests unversioned names while its generated type surface
  // also exposes the canonical versioned interface names.
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
