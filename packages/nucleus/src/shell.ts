import {
  _setStderr,
  _setStdin,
  _setStdout,
} from "@bytecodealliance/preview2-shim/cli";

import type { Repl } from "../generated/nucleus.js";
import { withVfs, type ReadOnlyVfs, type VfsFile } from "./vfs-host.js";

let shellRun = 0;
let shellQueue = Promise.resolve();

export interface ShellResult {
  status: number;
  stdout: string;
  stderr: string;
}

export interface ShellOptions {
  args: string[];
  stdin?: string;
  vfs?: ReadOnlyVfs;
}

class ReplVfs implements ReadOnlyVfs {
  constructor(private readonly repl: Repl) {}

  open(name: string): VfsFile {
    let handle: number;
    try {
      handle = this.repl.openObject(name);
    } catch {
      throw "not-found";
    }
    if (handle < 0) throw "not-found";
    return {
      size: () => {
        const length = this.repl.objectLength(handle);
        if (length < 0) throw "backend";
        return BigInt(length);
      },
      readAt: (offset, length) => {
        if (offset > BigInt(Number.MAX_SAFE_INTEGER)) throw "invalid-range";
        return this.repl.readObject(handle, Number(offset), length);
      },
      close: () => this.repl.closeObject(handle),
    };
  }
}

/** Queues one SQLite component invocation over a JS-provided VFS. */
export function runShell(
  repl: Repl,
  options: ShellOptions,
): Promise<ShellResult> {
  const result = shellQueue.then(() => runShellExclusive(repl, options));
  shellQueue = result.then(
    () => undefined,
    () => undefined,
  );
  return result;
}

async function runShellExclusive(
  repl: Repl,
  options: ShellOptions,
): Promise<ShellResult> {
  const database = options.args.find((argument) => !argument.startsWith("-"));
  if (
    database &&
    database !== ":memory:" &&
    !(database.startsWith("file:") && database.includes("vfs=cas"))
  ) {
    return {
      status: 1,
      stdout: "",
      stderr: "only the host VFS is available\n",
    };
  }

  const stdoutDecoder = new TextDecoder();
  const stderrDecoder = new TextDecoder();
  const encoder = new TextEncoder();
  const stdout: string[] = [];
  const stderr: string[] = [];
  const input = encoder.encode(options.stdin ?? "");
  let inputOffset = 0;

  _setStdout(output(stdout, stdoutDecoder));
  _setStderr(output(stderr, stderrDecoder));
  _setStdin({
    blockingRead(length: bigint) {
      const remaining = input.length - inputOffset;
      const count = Number(length < BigInt(remaining) ? length : remaining);
      const chunk = input.slice(inputOffset, inputOffset + count);
      inputOffset += chunk.length;
      return chunk;
    },
  });

  let status = 1;
  try {
    // A shell invocation gets fresh SQLite globals, like a new process.
    const module = new URL("../generated/shell/shell.js", import.meta.url);
    module.searchParams.set("run", String(shellRun++));
    const { run } = (await import(
      module.href
    )) as typeof import("../generated/shell/shell.js");
    status = await withVfs(options.vfs ?? new ReplVfs(repl), () =>
      run(["-noinit", ...options.args]),
    );
  } catch (error) {
    if (isComponentExit(error)) status = error.code;
    else throw error;
  }

  stdout.push(stdoutDecoder.decode());
  stderr.push(stderrDecoder.decode());
  return { status, stdout: stdout.join(""), stderr: stderr.join("") };
}

function output(parts: string[], decoder: TextDecoder) {
  return {
    write(bytes: Uint8Array) {
      parts.push(decoder.decode(bytes, { stream: true }));
    },
    blockingFlush() {},
  };
}

function isComponentExit(error: unknown): error is Error & { code: number } {
  return (
    error instanceof Error &&
    "exitError" in error &&
    "code" in error &&
    typeof error.code === "number"
  );
}

export type { ReadOnlyVfs, VfsError, VfsFile } from "./vfs-host.js";
