import assert from "node:assert/strict";
import { createReadStream } from "node:fs";
import { stat } from "node:fs/promises";
import { createServer } from "node:http";
import { extname, join } from "node:path";
import test from "node:test";
import { chromium } from "playwright-core";

const root = new URL("..", import.meta.url).pathname;
const contentTypes = {
  ".html": "text/html; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".wasm": "application/wasm",
};

test("downloads and attaches an immutable SQLite image in a Worker", async (context) => {
  const server = createServer(async (request, response) => {
    const relative = new URL(request.url ?? "/", "http://localhost").pathname;
    const path = join(root, relative);
    try {
      const info = await stat(path);
      if (!info.isFile()) throw new Error("not a file");
      response.writeHead(200, {
        "content-type":
          contentTypes[extname(path)] ?? "application/octet-stream",
      });
      createReadStream(path).pipe(response);
    } catch {
      response.writeHead(404).end();
    }
  });
  await new Promise((resolve) => server.listen(0, "127.0.0.1", resolve));
  context.after(() => server.close());

  const executablePath = process.env.CHROMIUM_PATH;
  assert.ok(executablePath, "CHROMIUM_PATH is set by the Nix shell");
  const browser = await chromium.launch({
    executablePath,
    headless: true,
    args: ["--no-sandbox"],
  });
  context.after(() => browser.close());
  const page = await browser.newPage();
  const address = server.address();
  assert.notEqual(address, null);
  assert.equal(typeof address, "object");
  await page.goto(`http://127.0.0.1:${address.port}/test/browser.html`);
  await page.waitForFunction(
    () =>
      document.body.dataset.result !== undefined ||
      document.body.dataset.error !== undefined,
  );
  assert.equal(await page.locator("body").getAttribute("data-error"), null);
  const result = JSON.parse(
    await page.locator("body").getAttribute("data-result"),
  );
  assert.match(result.hash, /^[0-9a-f]{64}$/);
  assert.deepEqual(result.result, {
    kind: "rows",
    columns: ["name", "value"],
    rows: [
      [
        { kind: "text", value: "exact" },
        { kind: "integer", value: "9223372036854775807" },
      ],
    ],
  });
  assert.equal(result.readonly, true);
  assert.equal(result.namespace, 1);
  assert.deepEqual(result.namespaceView, { parent: 0, name: "demo" });
  assert.deepEqual(result.exportView, {
    sort: "term",
    local: 3,
    name: "truth",
  });
  assert.equal(result.resolved, 7);
  assert.equal(result.snapshotHash, result.snapshotImage);
  assert.match(result.snapshotSchema, /^[0-9a-f]{64}$/);
  assert.match(result.snapshotSigner, /^[0-9a-f]{64}$/);
  assert.equal(result.publicKeyLength, 32);
  assert.equal(result.signatureLength, 64);
  assert.equal(result.descriptorLength, 49);
  assert.equal(result.compiledDescriptorMatches, true);
  assert.equal(result.malformedDescriptorRejected, true);
  assert.equal(result.ambiguousSchemaSourceRejected, true);
  assert.equal(result.attestationHasBytes, false);
  assert.deepEqual(result.snapshotRows, {
    kind: "rows",
    columns: ["namespace_id", "export_id", "sort", "local_id", "name"],
    rows: [
      [
        { kind: "integer", value: "1" },
        { kind: "integer", value: "7" },
        { kind: "text", value: "term" },
        { kind: "integer", value: "3" },
        { kind: "text", value: "truth" },
      ],
    ],
  });
  assert.deepEqual(result.inspectedImport, result.trustedImport);
  assert.equal(result.importedNamespace, 1);
  assert.deepEqual(result.importedExport, {
    connectionId: 3,
    trustedImportId: 0,
    importId: 0,
    namespaceId: 1,
    exportId: 7,
    sort: "term",
    sourceId: 3,
    term: { kind: "bool", value: true },
  });
  assert.equal(result.trustedImport.importId, 0);
  assert.equal(result.trustedImport.trustedImportId, 0);
  assert.equal(result.trustedImport.schema, result.snapshotSchema);
  assert.equal(result.trustedImport.image, result.snapshotImage);
  assert.equal(result.trustedImport.signer, result.snapshotSigner);
  assert.equal(result.tamperedRejected, true);
  assert.equal(result.observerReadRejected, true);
  assert.deepEqual(result.trustedRows, {
    kind: "rows",
    columns: [
      "import_id",
      "hex(i.schema_hash)",
      "hex(i.image_hash)",
      "trusted_import_id",
      "hex(t.signer_hash)",
      "length(t.public_key)",
      "length(t.signature)",
    ],
    rows: [
      [
        { kind: "integer", value: "0" },
        { kind: "text", value: result.snapshotSchema.toUpperCase() },
        { kind: "text", value: result.snapshotImage.toUpperCase() },
        { kind: "integer", value: "0" },
        { kind: "text", value: result.snapshotSigner.toUpperCase() },
        { kind: "integer", value: "32" },
        { kind: "integer", value: "64" },
      ],
    ],
  });
  assert.deepEqual(result.observerRows, {
    kind: "rows",
    columns: [
      "(SELECT count(*) FROM observer_snapshot.hol_import)",
      "(SELECT count(*) FROM observer_snapshot.hol_trusted_import)",
    ],
    rows: [
      [
        { kind: "integer", value: "0" },
        { kind: "integer", value: "0" },
      ],
    ],
  });

  const demo = await browser.newPage();
  await demo.goto(`http://127.0.0.1:${address.port}/repl.html`);
  await demo.getByText("connection 1 ready").waitFor();
  await demo.locator("#sql").fill("SELECT 42 AS answer");
  await demo.locator("#run").click();
  await demo.getByRole("cell", { name: "42" }).waitFor();
  assert.equal(await demo.getByRole("columnheader").textContent(), "answer");

  await demo.locator("#new").click();
  await demo.locator("#connection").selectOption("2");
  await demo.locator("#sql").fill("SELECT 84 AS independent");
  await demo.locator("#run").click();
  await demo.getByRole("cell", { name: "84" }).waitFor();

  await demo.locator("#new-hol").click();
  await demo.getByText("hol connection 3 ready").waitFor();
  await demo.locator("#hol-star").click();
  await demo.getByText("kind 1 = star").waitFor();
  await demo.locator("#hol-arrow").click();
  await demo.getByText("kind 3 = 1 -> 1").waitFor();
  await demo.locator("#hol-rank").click();
  await demo.getByText("rank 3 = 1").waitFor();
  await demo.locator("#hol-term-demo").click();
  await demo.getByText("term 7 : 2; freevars = 100,101").waitFor();
  await demo.locator("#hol-proof-demo").click();
  await demo
    .getByText("context 1; theorem 1 |- 7; truth 0 |- 8; proved = true")
    .waitFor();
  await demo.locator("#hol-binding-demo").click();
  await demo
    .getByText("bound 9 unbound=0:2 closed=false; lambda 10 : 4 closed=true")
    .waitFor();
  await demo.locator("#hol-reflexivity-demo").click();
  await demo
    .getByText("theorem 0 |- 11; equality 10 = 10; proved = true")
    .waitFor();
  await demo.locator("#hol-beta-demo").click();
  await demo.getByText("theorem 0 |- 13; (10 8) = 8; proved = true").waitFor();
  await demo.locator("#hol-weakening-demo").click();
  await demo
    .getByText(
      "context 3 => 2 proved=true; theorem 3 |- 16; before=false after=true",
    )
    .waitFor();
  await demo.locator("#hol-export-signed").click();
  await demo.getByText(/signed HOL snapshot [0-9a-f]{64}/).waitFor();
  await demo.locator("#new-hol").click();
  await demo.getByText("hol connection 4 ready").waitFor();
  await demo.locator("#hol-trust-import").click();
  await demo.getByText(/trusted import 0 references local import 0/).waitFor();
});
