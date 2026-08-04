import assert from "node:assert/strict";
import test from "node:test";

import {
  KERNEL_CHANNEL_PATH,
  KERNEL_INVOCATION_PATH,
  KernelFetchTransport,
  MAX_KERNEL_SIGNED_FRAME_BYTES,
} from "../dist/fetch_transport.js";
import { SerializedCommandQueue } from "../dist/serialized_commands.js";

function binaryResponse(bytes, init = {}) {
  return new Response(bytes, {
    status: 200,
    ...init,
    headers: {
      "content-type": "application/octet-stream",
      "content-length": String(bytes.byteLength),
      ...init.headers,
    },
  });
}

test("fetch transport sends exact channel enrollment without mutating caller bytes", async () => {
  const caller = new Uint8Array(32).fill(7);
  const token = new Uint8Array(32).fill(10);
  const requests = [];
  const transport = new KernelFetchTransport("https://kernel.test/api", {
    fetch: async (input, init) => {
      requests.push({ input: String(input), init, body: new Uint8Array(init.body) });
      return binaryResponse(new Uint8Array([1, 2, 3]));
    },
  });

  assert.deepEqual(await transport.requestChannel(caller, token), new Uint8Array([1, 2, 3]));
  caller.fill(0);
  assert.equal(requests[0].input, `https://kernel.test/api/${KERNEL_CHANNEL_PATH}`);
  assert.deepEqual(requests[0].body, new Uint8Array(32).fill(7));
  assert.equal(requests[0].init.method, "POST");
  assert.equal(requests[0].init.redirect, "error");
  assert.equal(requests[0].init.credentials, "omit");
  assert.equal(
    requests[0].init.headers.get("authorization"),
    `Nucleus-Bootstrap ${"0a".repeat(32)}`,
  );
});

test("fetch invocation is one bounded retry-free POST", async () => {
  let calls = 0;
  const transport = new KernelFetchTransport("https://kernel.test/", {
    fetch: async (input, init) => {
      calls += 1;
      assert.equal(String(input), `https://kernel.test/${KERNEL_INVOCATION_PATH}`);
      assert.deepEqual(new Uint8Array(init.body), new Uint8Array([9, 8]));
      return binaryResponse(new Uint8Array([6, 5, 4]));
    },
  });
  assert.deepEqual(await transport.invoke(new Uint8Array([9, 8])), new Uint8Array([6, 5, 4]));
  assert.equal(calls, 1);
  assert.throws(
    () => transport.invoke(new Uint8Array(MAX_KERNEL_SIGNED_FRAME_BYTES + 1)),
    /transport limit/,
  );
  assert.equal(calls, 1);
});

test("fetch transport rejects deceptive or unbounded response framing", async () => {
  const missingLength = new KernelFetchTransport("https://kernel.test/", {
    fetch: async () =>
      new Response(new Uint8Array([1]), {
        headers: { "content-type": "application/octet-stream" },
      }),
  });
  await assert.rejects(missingLength.invoke(new Uint8Array()), /Content-Length/);

  const longerThanDeclared = new KernelFetchTransport("https://kernel.test/", {
    fetch: async () =>
      binaryResponse(new Uint8Array([1, 2]), {
        headers: { "content-length": "1" },
      }),
  });
  await assert.rejects(
    longerThanDeclared.invoke(new Uint8Array()),
    /exceeds its declared Content-Length/,
  );

  const encoded = new KernelFetchTransport("https://kernel.test/", {
    fetch: async () =>
      binaryResponse(new Uint8Array(), {
        headers: { "content-encoding": "gzip" },
      }),
  });
  await assert.rejects(encoded.invoke(new Uint8Array()), /Content-Encoding/);
});

test("fetch transport bounds unsigned diagnostics and never retries failures", async () => {
  let calls = 0;
  const transport = new KernelFetchTransport("https://kernel.test/", {
    fetch: async () => {
      calls += 1;
      return new Response(new Uint8Array(4097), {
        status: 403,
        headers: {
          "content-type": "text/plain; charset=utf-8",
          "content-length": "4097",
        },
      });
    },
  });
  await assert.rejects(transport.invoke(new Uint8Array()), /transport limit/);
  assert.equal(calls, 1);
});

test("serialized commands preserve FIFO order across suspension and rejection", async () => {
  const queue = new SerializedCommandQueue();
  const order = [];
  let release;
  const blocked = new Promise((resolve) => {
    release = resolve;
  });

  const first = queue.enqueue(async () => {
    order.push("first-start");
    await blocked;
    order.push("first-end");
    throw new Error("expected");
  });
  const second = queue.enqueue(() => {
    order.push("second");
    return 2;
  });
  await Promise.resolve();
  assert.deepEqual(order, ["first-start"]);
  release();
  await assert.rejects(first, /expected/);
  assert.equal(await second, 2);
  assert.deepEqual(order, ["first-start", "first-end", "second"]);
});
