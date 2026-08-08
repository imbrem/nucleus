/**
 * The CAS protocol, over shared memory.
 *
 * The shell runs in a Worker of its own — a separate process in every sense
 * that matters here — and reaches the kernel through this. The kernel stays
 * where it is; only the request crosses.
 *
 * # Why shared memory rather than messages
 *
 * A WASI guest calling `cas_read` expects a number back *now*. It cannot await.
 * So the worker writes its request into a `SharedArrayBuffer`, wakes the
 * kernel's thread, and blocks on `Atomics.wait` until the answer appears.
 * `postMessage` alone cannot do this: it would return control to the worker's
 * event loop, which is exactly what a blocking call must not do.
 *
 * This is why the demo server sets COOP and COEP. `SharedArrayBuffer` only
 * exists on a cross-origin-isolated page.
 *
 * # Why this shape rather than a socket
 *
 * It is the same handle discipline as the native Unix-socket transport:
 * `open` resolves an address once and returns a handle, and reads name the
 * handle. The kernel holds the object until the shell releases it, so a
 * `.forget` while a shell has a database open cannot break it.
 */

/** Slots in the control array, which is an `Int32Array`. */
export const SLOT = {
  /** Handshake state; see {@link STATE}. */
  state: 0,
  /** Which operation, see {@link OP}. */
  op: 1,
  /** Operation-specific arguments. */
  a: 2,
  b: 3,
  c: 4,
  /** Result, or a negative value on failure. */
  result: 5,
  /** Second result word, for the length an open reports. */
  result2: 6,
} as const;

export const STATE = {
  idle: 0,
  request: 1,
  response: 2,
  /** The kernel is gone; the worker should stop asking. */
  closed: 3,
} as const;

export const OP = {
  open: 1,
  length: 2,
  read: 3,
  close: 4,
} as const;

/** Bytes reserved for payloads: a 32-byte address in, a page out. */
export const DATA_BYTES = 1 << 16;

/** How many `Int32` slots the control array needs. */
export const CONTROL_SLOTS = 8;

/** What a worker is handed in order to reach the kernel. */
export interface Channel {
  control: SharedArrayBuffer;
  data: SharedArrayBuffer;
}

/** Allocates a channel. */
export function createChannel(): Channel {
  return {
    control: new SharedArrayBuffer(CONTROL_SLOTS * 4),
    data: new SharedArrayBuffer(DATA_BYTES),
  };
}
