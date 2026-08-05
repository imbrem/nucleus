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
  assert.equal(theorem.judgement_id(), undefined);
  assert.equal(theorem.statement(), "(lambda x:bool. x) true = true");
  const truth = kernel.run_hol(holConnection, "truth");
  const truthReplay = kernel.run_hol(holConnection, "truth");
  assert.match(truth.judgement_id(), /^[1-9][0-9]*$/);
  assert.equal(truthReplay.judgement_id(), truth.judgement_id());
  const reflexivity = kernel.run_hol(holConnection, "reflexivity false");
  assert.match(reflexivity.judgement_id(), /^[1-9][0-9]*$/);
  assert.notEqual(reflexivity.judgement_id(), truth.judgement_id());
  assert.throws(() => kernel.run_hol(connection, "truth"));
  assert.throws(() => kernel.run(holConnection, "SELECT 1"));

  reflexivity.free();
  truthReplay.free();
  truth.free();
  theorem.free();
  result.free();
  kernel.free();
  source.free();
});
