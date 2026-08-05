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
  const sourceConnection = source.open_connection();
  source.run(sourceConnection, "CREATE TABLE example(value TEXT)").free();
  source
    .run(sourceConnection, "INSERT INTO example VALUES ('immutable')")
    .free();
  const image = source.serialize_main(sourceConnection);

  const kernel = new WebKernel();
  const connection = kernel.open_connection();
  const otherConnection = kernel.open_connection();
  const holConnection = kernel.open_hol_connection();
  const hash = kernel.put_image(connection, image);
  kernel.attach_image(connection, hash, "library");
  const result = kernel.run(
    connection,
    "SELECT value, 9223372036854775807 FROM library.example",
  );
  assert.equal(result.kind(), "rows");
  assert.equal(result.column_count(), 2);
  assert.equal(result.row_count(), 1);
  assert.equal(result.value_kind(0, 0), "text");
  assert.equal(result.text(0, 0), "immutable");
  assert.equal(result.value_kind(0, 1), "integer");
  assert.equal(result.integer(0, 1), "9223372036854775807");
  assert.throws(() =>
    kernel.run(connection, "INSERT INTO library.example VALUES ('changed')"),
  );
  assert.throws(() =>
    kernel.run(otherConnection, "SELECT * FROM library.example"),
  );
  kernel.close_connection(otherConnection);
  assert.throws(() => kernel.run(otherConnection, "SELECT 1"));
  const theorem = kernel.run_hol(holConnection, "beta true");
  assert.equal(theorem.kind(), "hol-theorem");
  assert.equal(theorem.recipe(), "beta");
  assert.equal(theorem.context_id(), "0");
  assert.equal(theorem.conclusion_id(), "8");
  assert.equal(theorem.statement(), "(lambda x:bool. x) true = true");
  const signed = kernel.run_signed_hol_round_trip(holConnection);
  assert.equal(signed.kind(), "signed-hol-round-trip");
  assert.equal(signed.phase(0), "proof-persisted");
  assert.equal(signed.phase(signed.phase_count() - 1), "theorem-read");
  assert.equal(signed.statement(), "(lambda x:bool. x) true = true");
  assert.ok(signed.image().byteLength > 0);
  assert.equal(signed.public_key().byteLength, 32);
  assert.equal(signed.signature().byteLength, 64);
  assert.equal(signed.imported_context_id(), "0");
  assert.equal(signed.imported_conclusion_id(), signed.conclusion_id());
  assert.notEqual(signed.receiver_connection(), holConnection);
  assert.throws(() =>
    kernel.run(signed.receiver_connection(), "SELECT 1"),
  );
  assert.throws(() => kernel.run_hol(connection, "truth"));
  assert.throws(() => kernel.run(holConnection, "SELECT 1"));

  kernel.close_connection(signed.receiver_connection());
  signed.free();
  theorem.free();
  result.free();
  kernel.free();
  source.free();
});
