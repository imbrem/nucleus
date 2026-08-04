/**
 * FIFO executor for commands which may suspend on asynchronous transport.
 *
 * Keeping one command active at a time is essential for the browser kernel:
 * mutable WASM state must never be borrowed across `await`, and later Worker
 * messages must not overtake a channel admission or signed invocation.
 */
export class SerializedCommandQueue {
  #tail: Promise<void> = Promise.resolve();

  enqueue<T>(command: () => T | PromiseLike<T>): Promise<T> {
    const result = this.#tail.then(command);
    this.#tail = result.then(
      () => undefined,
      () => undefined,
    );
    return result;
  }
}
