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
  onStdout?: (text: string) => void;
  onStderr?: (text: string) => void;
}

export interface InteractiveShellOptions {
  args: string[];
  vfs?: ReadOnlyVfs;
  onStdout?: (text: string) => void;
  onStderr?: (text: string) => void;
}

export interface InteractiveShell {
  write(text: string): void;
  close(): void;
  readonly done: Promise<ShellResult>;
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

/** Starts one SQLite process whose stdin remains open until `close`. */
export async function startShell(
  repl: Repl,
  options: InteractiveShellOptions,
): Promise<InteractiveShell> {
  let release!: () => void;
  const turn = shellQueue;
  shellQueue = new Promise<void>((resolve) => {
    release = resolve;
  });
  await turn;

  const stdin = new ShellInput();
  const done = runShellExclusive(repl, options, stdin).finally(release);
  return {
    write: (text) => stdin.write(text),
    close: () => stdin.close(),
    done,
  };
}

async function runShellExclusive(
  repl: Repl,
  options: ShellOptions,
  interactiveInput?: ShellInput,
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

  _setStdout(output(stdout, stdoutDecoder, options.onStdout));
  _setStderr(output(stderr, stderrDecoder, options.onStderr));
  const stdin = interactiveInput
    ? {
        blockingRead: (length: bigint) => interactiveInput.blockingRead(length),
      }
    : {
        blockingRead(length: bigint) {
          const remaining = input.length - inputOffset;
          const count = Number(length < BigInt(remaining) ? length : remaining);
          const chunk = input.slice(inputOffset, inputOffset + count);
          inputOffset += chunk.length;
          return chunk;
        },
      };
  // The shim types describe the synchronous WIT surface. Jco lowers this
  // particular import through JSPI, so the interactive implementation may
  // return a Promise at runtime.
  _setStdin(stdin as unknown as Parameters<typeof _setStdin>[0]);

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

  finishOutput(stdout, stdoutDecoder, options.onStdout);
  finishOutput(stderr, stderrDecoder, options.onStderr);
  return { status, stdout: stdout.join(""), stderr: stderr.join("") };
}

function output(
  parts: string[],
  decoder: TextDecoder,
  emit?: (text: string) => void,
) {
  return {
    write(bytes: Uint8Array) {
      const text = decoder.decode(bytes, { stream: true });
      parts.push(text);
      emit?.(text);
    },
    blockingFlush() {},
  };
}

function finishOutput(
  parts: string[],
  decoder: TextDecoder,
  emit?: (text: string) => void,
) {
  const text = decoder.decode();
  parts.push(text);
  emit?.(text);
}

class ShellInput {
  private readonly encoder = new TextEncoder();
  private readonly queued: Uint8Array[] = [];
  private waiting?: { length: bigint; resolve: (bytes: Uint8Array) => void };
  private closed = false;

  blockingRead(length: bigint): Promise<Uint8Array> {
    if (this.waiting) throw new Error("SQLite issued overlapping stdin reads");
    const ready = this.take(length);
    if (ready) return Promise.resolve(ready);
    if (this.closed) return Promise.resolve(new Uint8Array());
    return new Promise((resolve) => {
      this.waiting = { length, resolve };
    });
  }

  write(text: string) {
    if (this.closed) throw new Error("SQLite stdin is closed");
    const bytes = this.encoder.encode(text);
    if (bytes.length !== 0) this.queued.push(bytes);
    this.wake();
  }

  close() {
    this.closed = true;
    this.wake();
  }

  private wake() {
    const waiting = this.waiting;
    if (!waiting) return;
    const bytes = this.take(waiting.length);
    if (!bytes && !this.closed) return;
    this.waiting = undefined;
    waiting.resolve(bytes ?? new Uint8Array());
  }

  private take(length: bigint): Uint8Array | undefined {
    const first = this.queued[0];
    if (!first) return undefined;
    const count = Math.min(first.length, Number(length));
    const bytes = first.slice(0, count);
    if (count === first.length) this.queued.shift();
    else this.queued[0] = first.slice(count);
    return bytes;
  }
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
