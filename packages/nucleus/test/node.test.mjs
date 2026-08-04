import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import test from "node:test";
import init, { smoke, WebKernel } from "../generated/nucleus.js";

test("runs the REPL kernel through the Wasm binding in Node", async () => {
  const bytes = await readFile(
    new URL("../generated/nucleus_bg.wasm", import.meta.url),
  );
  await init({ module_or_path: bytes });
  assert.equal(smoke(), 42);

  const source = new WebKernel();
  source.run("CREATE TABLE example(value TEXT)").free();
  source.run("INSERT INTO example VALUES ('immutable')").free();
  const image = source.serialize_main();

  const kernel = new WebKernel();
  const hash = kernel.put_image(image);
  kernel.attach_image(hash, "library");
  const result = kernel.run("SELECT value, 9223372036854775807 FROM library.example");
  assert.equal(result.kind(), "rows");
  assert.equal(result.column_count(), 2);
  assert.equal(result.row_count(), 1);
  assert.equal(result.value_kind(0, 0), "text");
  assert.equal(result.text(0, 0), "immutable");
  assert.equal(result.value_kind(0, 1), "integer");
  assert.equal(result.integer(0, 1), "9223372036854775807");
  assert.throws(() =>
    kernel.run("INSERT INTO library.example VALUES ('changed')"),
  );

  result.free();
  kernel.free();
  source.free();
});
