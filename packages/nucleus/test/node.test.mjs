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

  const holSource = kernel.open_hol_connection();
  const holTarget = kernel.open_hol_connection();
  const holSnapshot = kernel.hol_export_snapshot(holSource);
  const schema = holSnapshot.schema();
  const holImage = holSnapshot.image();
  const signer = holSnapshot.signer();
  const publicKey = holSnapshot.public_key();
  const signature = holSnapshot.signature();
  kernel.close_connection(holSource);

  assert.throws(() =>
    kernel.hol_trust_import(
      holTarget,
      schema,
      holImage,
      signer,
      publicKey.slice(1),
      signature,
    ),
  );
  const tampered = signature.slice();
  tampered[0] ^= 1;
  assert.throws(() =>
    kernel.hol_trust_import(
      holTarget,
      schema,
      holImage,
      signer,
      publicKey,
      tampered,
    ),
  );
  assert.throws(() =>
    kernel.hol_trust_import(
      connection,
      schema,
      holImage,
      signer,
      publicKey,
      signature,
    ),
  );

  const trusted = kernel.hol_trust_import(
    holTarget,
    schema,
    holImage,
    signer,
    publicKey,
    signature,
  );
  assert.equal(trusted.import_id(), 0);
  assert.equal(trusted.trusted_import_id(), 0);
  assert.equal(trusted.schema(), schema);
  assert.equal(trusted.image(), holImage);
  assert.equal(trusted.signer(), signer);
  const inspected = kernel.hol_trusted_import(
    holTarget,
    trusted.trusted_import_id(),
  );
  assert.equal(inspected.import_id(), trusted.import_id());
  assert.equal(inspected.schema(), schema);

  inspected.free();
  trusted.free();
  holSnapshot.free();
  result.free();
  kernel.free();
  source.free();
});
