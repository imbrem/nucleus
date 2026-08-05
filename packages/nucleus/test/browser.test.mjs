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
    // --disable-dev-shm-usage keeps Chromium alive in containers whose
    // /dev/shm is too small for a second page plus the Wasm kernel.
    args: ["--no-sandbox", "--disable-dev-shm-usage"],
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
  assert.deepEqual(result.theorem, {
    kind: "hol-theorem",
    recipe: "beta",
    context: "0",
    conclusion: "8",
    statement: "(lambda x:bool. x) true = true",
  });
  assert.equal(result.signed.kind, "signed-hol-round-trip");
  assert.equal(result.signed.phases[0], "proof-persisted");
  assert.equal(result.signed.phases.at(-1), "theorem-read");
  assert.equal(result.signed.statement, "(lambda x:bool. x) true = true");
  assert.ok(result.signed.image > 0);
  assert.equal(result.signed.publicKey, 32);
  assert.equal(result.signed.signature, 64);
  assert.equal(result.signed.attestation, true);
  assert.equal(result.signed.importedContext, "0");
  assert.equal(result.signed.importedConclusion, result.signed.conclusion);

  const demo = await browser.newPage();
  await demo.goto(`http://127.0.0.1:${address.port}/repl.html`);
  await demo.getByText("sql connection 1 ready").waitFor();
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
  await demo.locator("#connection").selectOption("3");
  await demo.locator("#recipe").fill("reflexivity false");
  await demo.locator("#run-hol").click();
  await demo.getByText("statement\tfalse = false").waitFor();

  const downloads = [];
  const bothDownloads = new Promise((resolve) => {
    demo.on("download", (download) => {
      downloads.push(download);
      if (downloads.length === 2) resolve();
    });
  });
  await demo.locator("#run-signed-hol").click();
  await demo.getByText("kind\tsigned-hol-round-trip").waitFor();
  await demo.getByText(/phases\tproof-persisted,.*theorem-read/).waitFor();
  await demo.getByText("statement\t(lambda x:bool. x) true = true").waitFor();
  await demo.getByText("receiver\thol receiver 4").waitFor();
  await bothDownloads;
  assert.deepEqual(
    downloads.map((download) => download.suggestedFilename()).sort(),
    ["beta.attestation.txt", "beta.sqlite3"],
  );
  assert.equal(
    await demo
      .locator("#connection option", { hasText: "hol receiver 4" })
      .count(),
    1,
  );

  const interkernel = await browser.newPage();
  await interkernel.goto(
    `http://127.0.0.1:${address.port}/test/interkernel.html`,
  );
  await interkernel.waitForFunction(
    () =>
      document.body.dataset.result !== undefined ||
      document.body.dataset.error !== undefined,
  );
  assert.equal(
    await interkernel.locator("body").getAttribute("data-error"),
    null,
  );
  const interkernelResult = JSON.parse(
    await interkernel.locator("body").getAttribute("data-result"),
  );
  assert.equal(interkernelResult.distinctKernels, true);
  assert.notEqual(
    interkernelResult.producerSigner,
    interkernelResult.receiverSigner,
  );
  assert.deepEqual(interkernelResult.producerPhases, [
    "proof-persisted",
    "namespace-exported",
    "snapshot-signed",
  ]);
  assert.deepEqual(interkernelResult.receiverPhases, [
    "image-size-checked",
    "signature-authenticated",
    "image-detached-validated",
    "signer-trusted",
    "snapshot-accepted",
    "namespace-imported",
    "theorem-read",
  ]);
  assert.equal(interkernelResult.registeredWithoutTrust, true);
  assert.equal(interkernelResult.selectedIndependently, true);
  assert.equal(new Set(interkernelResult.kernelIds).size, 2);
  assert.deepEqual(
    new Set(interkernelResult.connectionKernels),
    new Set(interkernelResult.kernelIds),
  );
  assert.match(interkernelResult.liveKernelCloseError, /open connections/);
  assert.deepEqual(interkernelResult.afterProducerClose, {
    kernels: 1,
    connections: 3,
  });
  assert.equal(interkernelResult.receiverSurvivedProducerClose, true);
  assert.deepEqual(interkernelResult.afterIndependentClose, {
    kernels: 0,
    connections: 0,
  });
  assert.match(interkernelResult.wrongBytesError, /signature-authenticated/);
  assert.match(
    interkernelResult.wrongSignatureError,
    /signature-authenticated/,
  );
  // The exact 64 MiB boundary is covered in Rust and Node/Wasm. Allocating it
  // here would turn this Worker/PKI test into a Chromium container memory test.
  assert.match(interkernelResult.wrongNamespaceError, /theorem-read/);
  assert.equal(interkernelResult.ownershipPreserved, true);
  assert.equal(interkernelResult.importedContext, "0");
  assert.equal(
    interkernelResult.importedConclusion,
    interkernelResult.producerConclusion,
  );
});
