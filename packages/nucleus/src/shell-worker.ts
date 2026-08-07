/**
 * The SQLite shell, running as its own process.
 *
 * This is a Worker. It holds the shell's wasm instance and nothing else: no
 * kernel, no store, no page. Its databases arrive through the CAS channel, and
 * every one of its filesystem calls is refused, so there is nothing here for
 * it to reach.
 *
 * Being a separate context is the point rather than an implementation detail.
 * It is what the native binary already does with a subprocess, it keeps a slow
 * or wedged shell from freezing the REPL, and it is the step that makes "a
 * shell in one tab while the REPL runs in another" a change of transport
 * rather than a redesign.
 */

import { createWasi, instantiate, start } from "./wasi.js";
import { type Channel, OP, SLOT, STATE } from "./protocol.js";

/** Where a spawned shell should get its objects. */
export type Source =
  /** Back through a channel to the kernel in the page. */
  | { kind: "local"; channel: Channel }
  /** Straight from a kernel over HTTP, with no page involvement. */
  | { kind: "http"; baseUrl: string };

/** What the main thread sends to start a run. */
interface Start {
  wasm: ArrayBuffer;
  args: string[];
  stdin: string;
  source: Source;
}

/**
 * A CAS reached over HTTP, read synchronously.
 *
 * This is how `sql.js-httpvfs` does it, and the reason it works is narrow but
 * reliable: synchronous `XMLHttpRequest` is deprecated on a main thread but
 * still permitted inside a Worker. So a guest that must block can, without a
 * `SharedArrayBuffer` and therefore without cross-origin isolation.
 *
 * The consequence is worth stating plainly: the shell reads the *remote*
 * database directly, a page at a time. Nothing is copied into the page first.
 *
 * # These reads are not verified
 *
 * A whole object can be checked against its address by hashing it. A single
 * range cannot, without BLAKE3 range proofs — see issue #442. So this path
 * trusts the server for the bytes it returns, which `.fetch` does not.
 * That is a real difference in guarantee and the REPL says so before using it.
 */
function httpSource(baseUrl: string) {
  const base = baseUrl.replace(/\/$/, "");
  const open = new Map<number, { url: string; len: number }>();
  let next = 1;

  /** One synchronous request, returning status, headers and bytes. */
  function request(url: string, range?: [number, number]) {
    const xhr = new XMLHttpRequest();
    xhr.open("GET", url, false);
    if (range) xhr.setRequestHeader("Range", `bytes=${range[0]}-${range[1]}`);
    // Keeps bytes intact: without this the response is decoded as UTF-8 and
    // anything above 0x7f is mangled.
    xhr.overrideMimeType("text/plain; charset=x-user-defined");
    xhr.send();
    return xhr;
  }

  function toBytes(text: string): Uint8Array {
    const out = new Uint8Array(text.length);
    for (let index = 0; index < text.length; index += 1) {
      out[index] = text.charCodeAt(index) & 0xff;
    }
    return out;
  }

  return {
    open(hex: string): { handle: number; len: number } | null {
      const url = `${base}/cas/${hex}`;
      // A one-byte range is the cheapest way to learn the length, because
      // `Content-Range` carries the total.
      const probe = request(url, [0, 0]);
      if (probe.status === 404) return null;
      if (probe.status !== 206) return null;
      const header = probe.getResponseHeader("content-range") ?? "";
      const total = Number(header.split("/")[1]);
      if (!Number.isFinite(total)) return null;
      const handle = next;
      next += 1;
      open.set(handle, { url, len: total });
      return { handle, len: total };
    },
    length(handle: number): number {
      return open.get(handle)?.len ?? -1;
    },
    read(handle: number, offset: number, length: number): Uint8Array | null {
      const entry = open.get(handle);
      if (!entry) return null;
      if (length === 0) return new Uint8Array(0);
      // HTTP ranges are inclusive at both ends.
      const xhr = request(entry.url, [offset, offset + length - 1]);
      if (xhr.status !== 206) return null;
      const bytes = toBytes(xhr.responseText);
      // A short answer must not become a short page: SQLite would read the
      // difference as zeroes and see a corrupt database.
      return bytes.length === length ? bytes : null;
    },
    close(handle: number) {
      open.delete(handle);
    },
  };
}

/**
 * Performs one blocking CAS call against the kernel.
 *
 * Writes the request, wakes whoever is servicing the channel, and waits. The
 * wait is the whole reason this runs in a worker: `Atomics.wait` is forbidden
 * on a browser's main thread.
 */
function call(
  control: Int32Array,
  op: number,
  a = 0,
  b = 0,
  c = 0,
): { result: number; result2: number } {
  Atomics.store(control, SLOT.op, op);
  Atomics.store(control, SLOT.a, a);
  Atomics.store(control, SLOT.b, b);
  Atomics.store(control, SLOT.c, c);
  Atomics.store(control, SLOT.state, STATE.request);
  Atomics.notify(control, SLOT.state);

  // Spin through spurious wakeups until the kernel answers or goes away.
  for (;;) {
    Atomics.wait(control, SLOT.state, STATE.request);
    const state = Atomics.load(control, SLOT.state);
    if (state === STATE.response) break;
    if (state === STATE.closed) return { result: -1, result2: 0 };
  }
  const result = Atomics.load(control, SLOT.result);
  const result2 = Atomics.load(control, SLOT.result2);
  Atomics.store(control, SLOT.state, STATE.idle);
  return { result, result2 };
}

self.addEventListener("message", async (event: MessageEvent<Start>) => {
  const { wasm, args, stdin, source } = event.data;

  // `-noinit` because there is no home directory here and never will be.
  const wasi = createWasi(["sqlite3", "-noinit", ...args], stdin);

  let memory: WebAssembly.Memory;
  const guest = () => new Uint8Array(memory.buffer);

  const cas =
    source.kind === "http" ? overHttp(source.baseUrl, guest) : overChannel(source.channel, guest);

  try {
    const instance = await instantiate(wasm, {
      wasi_snapshot_preview1: wasi.imports,
      "covalence:cas": cas,
    });
    memory = instance.exports.memory as WebAssembly.Memory;
    wasi.attach(memory);

    const status = start(instance);
    self.postMessage({ status, stdout: wasi.stdout(), stderr: wasi.stderr() });
  } catch (error) {
    self.postMessage({
      status: -1,
      stdout: "",
      stderr: `shell worker failed: ${error}`,
    });
  }
});

/** CAS imports backed by a synchronous ranged HTTP source. */
function overHttp(baseUrl: string, guest: () => Uint8Array) {
  const source = httpSource(baseUrl);
  const hexAt = (address: number) =>
    Array.from(guest().subarray(address, address + 32))
      .map((byte) => byte.toString(16).padStart(2, "0"))
      .join("");

  return {
    cas_open(address: number): bigint {
      const opened = source.open(hexAt(address));
      return BigInt(opened ? opened.handle : -1);
    },
    cas_length(handle: bigint): bigint {
      return BigInt(source.length(Number(handle)));
    },
    cas_read(handle: bigint, offset: bigint, length: number, out: number): number {
      const bytes = source.read(Number(handle), Number(offset), length);
      if (!bytes) return -1;
      guest().set(bytes, out);
      return bytes.length;
    },
    cas_close(handle: bigint) {
      source.close(Number(handle));
    },
  };
}

/** CAS imports backed by the kernel in the page, over shared memory. */
function overChannel(channel: Channel, guest: () => Uint8Array) {
  const control = new Int32Array(channel.control);
  const data = new Uint8Array(channel.data);

  return {
    cas_open(address: number): bigint {
      // The address goes through shared memory; only its length is a number.
      data.set(guest().subarray(address, address + 32), 0);
      const { result } = call(control, OP.open, 32);
      return BigInt(result);
    },
    cas_length(handle: bigint): bigint {
      const { result } = call(control, OP.length, Number(handle));
      return BigInt(result);
    },
    cas_read(
      handle: bigint,
      offset: bigint,
      length: number,
      out: number,
    ): number {
      const { result } = call(
        control,
        OP.read,
        Number(handle),
        Number(offset),
        length,
      );
      if (result < 0) return -1;
      guest().set(data.subarray(0, result), out);
      return result;
    },
    cas_close(handle: bigint) {
      call(control, OP.close, Number(handle));
    },
  };
}
