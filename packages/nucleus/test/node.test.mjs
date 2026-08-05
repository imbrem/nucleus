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
  assert.throws(() => kernel.run(signed.receiver_connection(), "SELECT 1"));
  assert.throws(() => kernel.run_hol(connection, "truth"));
  assert.throws(() => kernel.run(holConnection, "SELECT 1"));

  const infinity = kernel.assume_dedekind_infinity();
  assert.equal(infinity.kind(), "signed-assumption");
  assert.match(infinity.attestation_text(), /^authority=signed-assumption\n/);
  assert.match(infinity.attestation_text(), /\nfalsehood=all-bool-identity\n/);
  assert.ok(infinity.image().byteLength > 0);
  assert.equal(infinity.public_key().byteLength, 32);
  assert.equal(infinity.signature().byteLength, 64);
  assert.equal(kernel.active_connection(), infinity.receiver_connection());
  const infinityState = kernel.open_retained_trusted_hol_state(
    infinity.receiver_connection(),
    infinity.retained_id(),
  );
  assert.equal(infinityState.context_id(), infinity.context_id());
  assert.equal(infinityState.conclusion_id(), infinity.conclusion_id());
  const infinityTruth = kernel.run_hol(infinityState.connection(), "truth");
  assert.equal(infinityTruth.kind(), "hol-theorem");
  infinityTruth.free();
  kernel.close_connection(infinity.receiver_connection());
  const infinityTruthAfterOwnerClose = kernel.run_hol(
    infinityState.connection(),
    "truth",
  );
  infinityTruthAfterOwnerClose.free();
  kernel.close_connection(infinityState.connection());
  infinityState.free();
  infinity.free();

  const missingZero = kernel.prove_natlike_missing_zero();
  assert.equal(missingZero.kind(), "signed-natlike-missing-zero");
  assert.equal(missingZero.theorem_oracle(), "(APP missing zero)");
  assert.match(
    missingZero.attestation_text(),
    /^authority=kernel-derived-theorem\nsource-assumption=dedekind-infinity\n/,
  );
  assert.match(
    missingZero.attestation_text(),
    /\ntheorem=natlike-missing-zero\ntheorem-oracle=\(APP missing zero\)\nintermediate-persistence=none\n/,
  );
  assert.match(missingZero.namespace_id(), /^\d+$/);
  assert.match(missingZero.schema(), /^[0-9a-f]{64}$/);
  assert.match(missingZero.image_hash(), /^[0-9a-f]{64}$/);
  assert.match(missingZero.signer(), /^[0-9a-f]{64}$/);
  assert.ok(missingZero.image().byteLength > 0);
  assert.equal(missingZero.public_key().byteLength, 32);
  assert.equal(missingZero.signature().byteLength, 64);
  assert.equal(kernel.active_connection(), missingZero.receiver_connection());
  const missingZeroState = kernel.open_retained_trusted_hol_state(
    missingZero.receiver_connection(),
    missingZero.retained_id(),
  );
  assert.equal(missingZeroState.context_id(), missingZero.context_id());
  assert.equal(missingZeroState.conclusion_id(), missingZero.conclusion_id());
  const missingZeroTruth = kernel.run_hol(
    missingZeroState.connection(),
    "truth",
  );
  assert.equal(missingZeroTruth.kind(), "hol-theorem");
  missingZeroTruth.free();
  kernel.close_connection(missingZero.receiver_connection());
  kernel.close_connection(missingZeroState.connection());
  missingZeroState.free();
  missingZero.free();

  const produced = kernel.produce_signed_hol_artifact(holConnection);
  const receiver = kernel.open_hol_connection();
  const wrongReceiver = kernel.open_hol_connection();
  const pinned = kernel.authenticate_pinned_signed_hol_artifact(
    7,
    produced.signer(),
    produced.public_key(),
    produced.namespace_id(),
    produced.image(),
    produced.schema(),
    produced.image_hash(),
    produced.signer(),
    produced.public_key(),
    produced.signature(),
  );
  const retained = kernel.trust_pinned_signed_hol_artifact_retained(
    receiver,
    pinned,
  );
  const beforeRereads = kernel.hol_image_hash(receiver);
  assert.throws(
    () =>
      kernel.reread_received_hol_artifact(
        wrongReceiver,
        retained.retained_id(),
      ),
    /belongs to another connection/,
  );
  for (let rereadIndex = 0; rereadIndex < 3; rereadIndex += 1) {
    const reread = kernel.reread_received_hol_artifact(
      receiver,
      retained.retained_id(),
    );
    assert.equal(reread.context_id(), retained.context_id());
    assert.equal(reread.conclusion_id(), retained.conclusion_id());
    reread.free();
  }
  assert.equal(kernel.hol_image_hash(receiver), beforeRereads);

  const state = kernel.open_retained_trusted_hol_state(
    receiver,
    retained.retained_id(),
  );
  const child = state.connection();
  assert.equal(kernel.active_connection(), child);
  assert.equal(state.source_namespace_id(), produced.namespace_id());
  assert.equal(state.context_id(), retained.context_id());
  assert.equal(state.conclusion_id(), retained.conclusion_id());
  const childTruth = kernel.run_hol(child, "truth");
  assert.equal(childTruth.kind(), "hol-theorem");
  childTruth.free();
  kernel.close_connection(receiver);
  const childTruthAfterOwnerClose = kernel.run_hol(child, "truth");
  assert.equal(childTruthAfterOwnerClose.kind(), "hol-theorem");
  childTruthAfterOwnerClose.free();
  kernel.close_connection(child);
  assert.throws(
    () =>
      kernel.open_retained_trusted_hol_state(receiver, retained.retained_id()),
    /unknown retained HOL artifact/,
  );
  state.free();

  kernel.close_connection(signed.receiver_connection());
  kernel.close_connection(wrongReceiver);
  retained.free();
  produced.free();
  signed.free();
  theorem.free();
  result.free();
  kernel.free();
  source.free();
});
