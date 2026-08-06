import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import test from "node:test";
import init, { Kernel } from "../generated/nucleus.js";

/** Loads the wasm kernel once for every test in this file. */
async function load() {
  const bytes = await readFile(
    new URL("../generated/nucleus_bg.wasm", import.meta.url),
  );
  await init({ module_or_path: bytes });
}

test("a kernel runs entirely in wasm", async () => {
  await load();
  const kernel = new Kernel();

  const database = await readFile(new URL("./fixture.sqlite", import.meta.url));
  const address = kernel.put(database);
  assert.match(address, /^[0-9a-f]{64}$/);

  const result = JSON.parse(kernel.query(address, "SELECT a, b, sum FROM adder ORDER BY a"));
  assert.deepEqual(result.columns, ["a", "b", "sum"]);
  assert.deepEqual(result.rows, [
    [2, 3, 5],
    [7, 8, 15],
  ]);
});

test("admitting verifies the content against its address", async () => {
  await load();
  const kernel = new Kernel();
  const database = await readFile(new URL("./fixture.sqlite", import.meta.url));

  // The honest path: the address the bytes actually hash to.
  const address = kernel.put(database);
  kernel.forget(address);
  assert.equal(kernel.admit(address, database), address);

  // The dishonest one: bytes that do not hash to the address asked for. This
  // is what makes an untrusted HTTP source usable, so it must not be lenient.
  kernel.forget(address);
  const tampered = Uint8Array.from(database);
  tampered[100] ^= 0xff;
  assert.throws(() => kernel.admit(address, tampered), /does not match its address/);
  assert.deepEqual(kernel.addresses(), []);
});

test("an address which was forgotten no longer opens", async () => {
  await load();
  const kernel = new Kernel();
  const database = await readFile(new URL("./fixture.sqlite", import.meta.url));
  const address = kernel.put(database);

  assert.equal(kernel.forget(address), true);
  assert.throws(() => kernel.query(address, "SELECT 1"));
});

test("the store reports what it holds", async () => {
  await load();
  const kernel = new Kernel();
  assert.deepEqual(JSON.parse(kernel.stats()), {
    objects: 0,
    bytes: 0,
    largest: 0,
  });

  const database = await readFile(new URL("./fixture.sqlite", import.meta.url));
  kernel.put(database);
  const stats = JSON.parse(kernel.stats());
  assert.equal(stats.objects, 1);
  assert.equal(stats.bytes, database.length);
});
