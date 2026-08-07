/**
 * Enough WASI to run the SQLite shell in a browser tab.
 *
 * The shell is `shell.c`, unmodified, compiled for `wasm32-wasip1`. It builds
 * there and not for `wasm32-unknown-unknown` for one reason: it uses stdio
 * heavily, and wasi-libc has real stdio where the freestanding target has none.
 *
 * This is a deliberately partial host. The shell needs 28 WASI functions; of
 * those, only argv, environment, stdio, clocks, randomness and exit do
 * anything. Every filesystem call returns `ENOSYS`, because the shell has no
 * filesystem here and must not be able to invent one — its databases arrive
 * through the CAS imports instead. A partial host that refuses loudly is
 * better than a complete one that quietly grants reach.
 */

import type { Repl } from "../generated/nucleus.js";

/** WASI `errno` values this host produces. */
const OK = 0;
const EBADF = 8;
const ENOSYS = 52;

/** Thrown by `proc_exit` to unwind out of the guest. */
export class Exit extends Error {
  constructor(public readonly code: number) {
    super(`guest exited with status ${code}`);
  }
}

/** What a guest is given and what it produced. */
export interface Wasi {
  /** The `wasi_snapshot_preview1` import object. */
  imports: Record<string, (...args: never[]) => unknown>;
  /** Called once the instance exists; every import needs its memory. */
  attach: (memory: WebAssembly.Memory) => void;
  /** Everything written to stdout. */
  stdout: () => string;
  /** Everything written to stderr. */
  stderr: () => string;
}

/**
 * Builds a partial WASI host.
 *
 * Deliberately partial: of the imports a guest asks for, only argv,
 * environment, stdio, clocks, randomness and exit do anything. Every
 * filesystem call returns `ENOSYS`, because neither guest has a filesystem
 * here and neither must be able to invent one — their databases arrive by
 * address. A host that refuses loudly is better than one that quietly grants
 * reach.
 */
export function createWasi(argv: string[], stdin: string): Wasi {
  const encoder = new TextEncoder();
  const decoder = new TextDecoder();

  const stdinBytes = encoder.encode(stdin);
  let stdinOffset = 0;
  const out: Uint8Array[] = [];
  const err: Uint8Array[] = [];

  let memory: WebAssembly.Memory;
  const view = () => new DataView(memory.buffer);
  const bytes = () => new Uint8Array(memory.buffer);

  const join = (parts: Uint8Array[]) =>
    decoder.decode(
      parts.reduce((all, part) => {
        const next = new Uint8Array(all.length + part.length);
        next.set(all);
        next.set(part, all.length);
        return next;
      }, new Uint8Array()),
    );

  function writeStrings(strings: string[], pointers: number, buffer: number) {
    const data = view();
    let cursor = buffer;
    for (const [index, text] of strings.entries()) {
      data.setUint32(pointers + index * 4, cursor, true);
      const encoded = encoder.encode(`${text}\0`);
      bytes().set(encoded, cursor);
      cursor += encoded.length;
    }
  }

  function gather(iovs: number, count: number): Uint8Array {
    const data = view();
    const parts: Uint8Array[] = [];
    for (let index = 0; index < count; index += 1) {
      const pointer = data.getUint32(iovs + index * 8, true);
      const length = data.getUint32(iovs + index * 8 + 4, true);
      parts.push(bytes().slice(pointer, pointer + length));
    }
    const total = parts.reduce((sum, part) => sum + part.length, 0);
    const joined = new Uint8Array(total);
    let cursor = 0;
    for (const part of parts) {
      joined.set(part, cursor);
      cursor += part.length;
    }
    return joined;
  }

  const imports = {
    args_sizes_get(count: number, size: number) {
      const total = argv.reduce(
        (sum, text) => sum + encoder.encode(text).length + 1,
        0,
      );
      view().setUint32(count, argv.length, true);
      view().setUint32(size, total, true);
      return OK;
    },
    args_get(pointers: number, buffer: number) {
      writeStrings(argv, pointers, buffer);
      return OK;
    },
    environ_sizes_get(count: number, size: number) {
      view().setUint32(count, 0, true);
      view().setUint32(size, 0, true);
      return OK;
    },
    environ_get: () => OK,

    fd_write(fd: number, iovs: number, count: number, written: number) {
      const data = gather(iovs, count);
      if (fd === 1) out.push(data);
      else if (fd === 2) err.push(data);
      else return EBADF;
      view().setUint32(written, data.length, true);
      return OK;
    },
    fd_read(fd: number, iovs: number, count: number, read: number) {
      if (fd !== 0) return EBADF;
      const data = view();
      let total = 0;
      for (
        let index = 0;
        index < count && stdinOffset < stdinBytes.length;
        index += 1
      ) {
        const pointer = data.getUint32(iovs + index * 8, true);
        const length = data.getUint32(iovs + index * 8 + 4, true);
        const slice = stdinBytes.subarray(
          stdinOffset,
          Math.min(stdinOffset + length, stdinBytes.length),
        );
        bytes().set(slice, pointer);
        stdinOffset += slice.length;
        total += slice.length;
      }
      // Zero means end of input, which is how a guest knows to stop.
      view().setUint32(read, total, true);
      return OK;
    },
    fd_close: () => OK,
    fd_sync: () => OK,
    fd_seek: () => ENOSYS,
    fd_fdstat_set_flags: () => OK,
    fd_fdstat_get(fd: number, stat: number) {
      // Character device, so stdio is not treated as seekable.
      const data = view();
      data.setUint8(stat, 2);
      data.setUint16(stat + 2, 0, true);
      data.setBigUint64(stat + 8, 0n, true);
      data.setBigUint64(stat + 16, 0n, true);
      return fd <= 2 ? OK : EBADF;
    },
    fd_prestat_get: () => EBADF,
    fd_prestat_dir_name: () => EBADF,
    fd_filestat_get: () => ENOSYS,
    fd_filestat_set_size: () => ENOSYS,
    fd_readdir: () => ENOSYS,
    path_open: () => ENOSYS,
    path_filestat_get: () => ENOSYS,
    path_filestat_set_times: () => ENOSYS,
    path_create_directory: () => ENOSYS,
    path_remove_directory: () => ENOSYS,
    path_unlink_file: () => ENOSYS,
    path_readlink: () => ENOSYS,
    path_symlink: () => ENOSYS,
    poll_oneoff: () => ENOSYS,

    clock_time_get(_id: number, _precision: bigint, slot: number) {
      view().setBigUint64(slot, BigInt(Date.now()) * 1_000_000n, true);
      return OK;
    },
    random_get(pointer: number, length: number) {
      crypto.getRandomValues(bytes().subarray(pointer, pointer + length));
      return OK;
    },
    proc_exit(code: number) {
      throw new Exit(code);
    },
  };

  return {
    imports: imports as unknown as Wasi["imports"],
    attach: (value) => {
      memory = value;
    },
    stdout: () => join(out),
    stderr: () => join(err),
  };
}

/** What one run of the shell produced. */
export interface ShellResult {
  /** Exit status, as the shell reported it. */
  status: number;
  /** Everything written to stdout. */
  stdout: string;
  /** Everything written to stderr. */
  stderr: string;
}

/** Options for {@link runShell}. */
export interface ShellOptions {
  /** Arguments after `argv[0]`, as at a `sqlite3` prompt. */
  args: string[];
  /** Text fed to the shell's standard input. */
  stdin?: string;
}

/**
 * Runs the SQLite shell against `kernel`, in a fresh wasm instance.
 *
 * A fresh instance per run is not a limitation to work around: the shell is a
 * program, it terminates by calling `exit`, and a new instance is exactly what
 * a new process is. Nothing carries over, which is the same property the
 * native subprocess has.
 */
/**
 * Runs the SQLite shell against `kernel`, in a fresh wasm instance.
 *
 * A fresh instance per run is not a limitation to work around: the shell is a
 * program, it terminates by calling `exit`, and a new instance is exactly what
 * a new process is. Nothing carries over, which is the same property the
 * native subprocess has.
 */
export async function runShell(
  kernel: Repl,
  wasm: BufferSource | Response | Promise<Response>,
  options: ShellOptions,
): Promise<ShellResult> {
  // `-noinit` because there is no home directory here and never will be.
  // Without it the shell warns about a `~/.sqliterc` it cannot read, on
  // stderr, for every invocation.
  const wasi = createWasi(
    ["sqlite3", "-noinit", ...options.args],
    options.stdin ?? "",
  );
  const instance = await instantiate(wasm, {
    wasi_snapshot_preview1: wasi.imports,
    "covalence:cas": casImports(kernel, () => memory),
  });
  const memory = instance.exports.memory as WebAssembly.Memory;
  wasi.attach(memory);

  const status = start(instance);
  return { status, stdout: wasi.stdout(), stderr: wasi.stderr() };
}

/**
 * The CAS a guest sees.
 *
 * These four are `covalence:cas/store` in the shape wasip1 can express. The
 * kernel holds each opened object until the guest releases it, so an address
 * forgotten mid-session cannot break a database the guest already has open.
 */
export function casImports(kernel: Repl, memory: () => WebAssembly.Memory) {
  const bytes = () => new Uint8Array(memory().buffer);
  return {
    cas_open(address: number): bigint {
      const hex = Array.from(bytes().subarray(address, address + 32))
        .map((byte) => byte.toString(16).padStart(2, "0"))
        .join("");
      try {
        return BigInt(kernel.openObject(hex));
      } catch {
        return -2n;
      }
    },
    cas_length(handle: bigint): bigint {
      return BigInt(kernel.objectLength(Number(handle)));
    },
    cas_read(handle: bigint, offset: bigint, length: number, out: number): number {
      try {
        const data = kernel.readObject(Number(handle), Number(offset), length);
        bytes().set(data, out);
        return data.length;
      } catch {
        return -1;
      }
    },
    cas_close(handle: bigint) {
      kernel.closeObject(Number(handle));
    },
  };
}

/** Instantiates a module from bytes or a response. */
export async function instantiate(
  wasm: BufferSource | Response | Promise<Response>,
  imports: WebAssembly.Imports,
): Promise<WebAssembly.Instance> {
  const source =
    wasm instanceof Response || wasm instanceof Promise
      ? await WebAssembly.instantiateStreaming(wasm, imports)
      : await WebAssembly.instantiate(wasm, imports);
  return "instance" in source ? source.instance : source;
}

/** Runs a guest's `_start`, turning its exit into a status. */
export function start(instance: WebAssembly.Instance): number {
  try {
    (instance.exports._start as () => void)();
  } catch (error) {
    if (error instanceof Exit) return error.code;
    throw error;
  }
  return 0;
}
