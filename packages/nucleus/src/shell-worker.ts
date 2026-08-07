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

/** What the main thread sends to start a run. */
interface Start {
  wasm: ArrayBuffer;
  args: string[];
  stdin: string;
  channel: Channel;
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
  const { wasm, args, stdin, channel } = event.data;
  const control = new Int32Array(channel.control);
  const data = new Uint8Array(channel.data);

  // `-noinit` because there is no home directory here and never will be.
  const wasi = createWasi(["sqlite3", "-noinit", ...args], stdin);

  let memory: WebAssembly.Memory;
  const guest = () => new Uint8Array(memory.buffer);

  const cas = {
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

  try {
    const instance = await instantiate(wasm, {
      wasi_snapshot_preview1: wasi.imports,
      "covalence:cas": cas,
    });
    memory = instance.exports.memory as WebAssembly.Memory;
    wasi.attach(memory);

    const status = start(instance);
    self.postMessage({
      status,
      stdout: wasi.stdout(),
      stderr: wasi.stderr(),
    });
  } catch (error) {
    self.postMessage({
      status: -1,
      stdout: "",
      stderr: `shell worker failed: ${error}`,
    });
  }
});
