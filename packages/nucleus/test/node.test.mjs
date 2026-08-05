import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import test from "node:test";
import init, {
  smoke,
  WebKernel,
  WebReplDirectory,
} from "../generated/nucleus.js";

test("runs the REPL kernel through the Wasm binding in Node", async () => {
  const bytes = await readFile(
    new URL("../generated/nucleus_bg.wasm", import.meta.url),
  );
  await init({ module_or_path: bytes });
  assert.equal(smoke(), 42);

  const directory = new WebReplDirectory();
  const firstKernel = directory.register_kernel(
    "worker",
    "worker:first",
    new Uint8Array(32).fill(1),
  );
  const secondKernel = directory.register_kernel(
    "worker",
    "worker:second",
    new Uint8Array(32).fill(2),
  );
  const managed = directory.insert_connection(firstKernel, "nucleus/hol", "17");
  const secondManaged = directory.insert_connection(
    secondKernel,
    "nucleus/sql",
    "4",
  );
  assert.equal(directory.kernel_count(), 2);
  assert.equal(directory.connection_count(), 2);
  directory.select_connection(managed);
  assert.equal(directory.active_connection(), managed);
  directory.select_connection(secondManaged);
  assert.equal(directory.active_connection(), secondManaged);
  const firstKernelRow = directory.kernel(0);
  assert.equal(firstKernelRow.transport(), "worker");
  assert.equal(firstKernelRow.endpoint(), "worker:first");
  assert.deepEqual(firstKernelRow.public_key(), new Uint8Array(32).fill(1));
  const connectionRow = directory.connection(0);
  assert.equal(connectionRow.kernel_id(), String(firstKernel));
  assert.equal(connectionRow.protocol(), "nucleus/hol");
  assert.equal(connectionRow.remote_connection_id(), "17");
  assert.throws(() => directory.unregister_kernel(firstKernel));
  directory.remove_connection(managed);
  directory.remove_connection(secondManaged);
  directory.unregister_kernel(firstKernel);
  directory.unregister_kernel(secondKernel);
  assert.equal(directory.kernel_count(), 0);
  firstKernelRow.free();
  connectionRow.free();
  directory.free();

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

  const producerKernel = new WebKernel();
  const producerConnection = producerKernel.open_hol_connection();
  const produced =
    producerKernel.produce_signed_hol_artifact(producerConnection);
  const receiverKernel = new WebKernel();
  const receiverConnection = receiverKernel.open_hol_connection();
  const receiverProbeConnection = receiverKernel.open_hol_connection();
  const receiverProbe = receiverKernel.produce_signed_hol_artifact(
    receiverProbeConnection,
  );
  assert.equal(produced.kind(), "signed-hol-artifact");
  assert.equal(produced.phase(0), "proof-persisted");
  assert.equal(produced.phase(2), "snapshot-signed");
  assert.notEqual(produced.signer(), receiverProbe.signer());

  const authenticate = (candidate, image, signature) =>
    receiverKernel.authenticate_pinned_signed_hol_artifact(
      17,
      produced.signer(),
      produced.public_key(),
      candidate.namespace_id(),
      image,
      candidate.schema(),
      candidate.image_hash(),
      candidate.signer(),
      candidate.public_key(),
      signature,
    );

  const wrongBytes = produced.image();
  wrongBytes[0] ^= 1;
  assert.throws(
    () => authenticate(produced, wrongBytes, produced.signature()),
    /signature-authenticated/,
  );
  const wrongSignature = produced.signature();
  wrongSignature[0] ^= 1;
  assert.throws(
    () => authenticate(produced, produced.image(), wrongSignature),
    /signature-authenticated/,
  );
  const oversized = new Uint8Array(WebKernel.max_image_bytes() + 1);
  assert.throws(
    () => authenticate(produced, oversized, produced.signature()),
    /image-size-checked/,
  );
  const beforePin = receiverKernel.hol_image_hash(receiverConnection);
  assert.throws(
    () =>
      authenticate(
        receiverProbe,
        receiverProbe.image(),
        receiverProbe.signature(),
      ),
    /signer-pinned/,
  );
  assert.equal(receiverKernel.hol_image_hash(receiverConnection), beforePin);
  const pinned = authenticate(produced, produced.image(), produced.signature());
  assert.equal(receiverKernel.hol_image_hash(receiverConnection), beforePin);
  const received = receiverKernel.trust_pinned_signed_hol_artifact(
    receiverConnection,
    pinned,
  );
  assert.equal(received.kind(), "received-hol-snapshot");
  assert.equal(received.phase(0), "image-size-checked");
  assert.equal(received.phase(received.phase_count() - 1), "theorem-read");
  assert.equal(received.context_id(), "0");
  assert.equal(received.conclusion_id(), produced.conclusion_id());

  kernel.close_connection(signed.receiver_connection());
  received.free();
  receiverProbe.free();
  produced.free();
  receiverKernel.free();
  producerKernel.free();
  signed.free();
  theorem.free();
  result.free();
  kernel.free();
  source.free();
});
