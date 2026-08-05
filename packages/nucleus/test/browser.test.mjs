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
    undefined,
    { timeout: 120_000 },
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
  assert.equal(result.missingZero.kind, "signed-natlike-missing-zero");
  assert.equal(result.missingZero.theoremOracle, "(APP missing zero)");
  assert.match(result.missingZero.namespace, /^\d+$/);
  assert.match(result.missingZero.schema, /^[0-9a-f]{64}$/);
  assert.match(result.missingZero.imageHash, /^[0-9a-f]{64}$/);
  assert.match(result.missingZero.signer, /^[0-9a-f]{64}$/);
  assert.ok(result.missingZero.image > 0);
  assert.equal(result.missingZero.publicKey, 32);
  assert.equal(result.missingZero.signature, 64);
  assert.equal(result.missingZero.attestation, true);
  assert.equal(result.missingZero.reopened.context, result.missingZero.context);
  assert.equal(
    result.missingZero.reopened.conclusion,
    result.missingZero.conclusion,
  );
  assert.equal(result.missingZero.reopened.truth, "true");

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

  await demo.locator("#assume-infinity").click();
  await demo.getByText("kind\tsigned-assumption").waitFor();
  await demo.getByText("authority\tsigned-assumption").waitFor();
  await demo.getByText("assumption\tdedekind-infinity").waitFor();
  await demo.getByText("falsehood\tall-bool-identity").waitFor();
  await demo.getByText("receiver\thol assumption receiver 5").waitFor();

  const infinityDownloads = [];
  const bothInfinityDownloads = new Promise((resolve) => {
    demo.on("download", (download) => {
      infinityDownloads.push(download);
      if (infinityDownloads.length === 2) resolve();
    });
  });
  await demo.locator("#download-infinity").click();
  await bothInfinityDownloads;
  assert.deepEqual(
    infinityDownloads.map((download) => download.suggestedFilename()).sort(),
    ["attestation.txt", "proof.sqlite"],
  );

  await demo.locator("#open-infinity-state").click();
  await demo.getByText(/Opened trusted state/).waitFor();
  await demo.locator("#recipe").fill("truth");
  await demo.locator("#run-hol").click();
  await demo.getByText("statement\ttrue").waitFor();

  const laterDownloads = [];
  const bothLaterDownloads = new Promise((resolve) => {
    demo.on("download", (download) => {
      laterDownloads.push(download);
      if (laterDownloads.length === 2) resolve();
    });
  });
  await demo.locator("#download-infinity").click();
  await bothLaterDownloads;
  assert.deepEqual(
    laterDownloads.map((download) => download.suggestedFilename()).sort(),
    ["attestation.txt", "proof.sqlite"],
  );

  await demo.locator("#connection").selectOption("5");
  await demo.locator("#close").click();
  await demo.getByText("Assumption receiver cleaned up").waitFor();
  assert.equal(await demo.locator('#connection option[value="5"]').count(), 0);
  assert.equal(await demo.locator("#download-infinity").isDisabled(), true);
  assert.equal(await demo.locator("#open-infinity-state").isDisabled(), true);

  await demo.locator("#connection").selectOption("6");
  await demo.locator("#recipe").fill("truth");
  await demo.locator("#run-hol").click();
  await demo.getByText("statement\ttrue").waitFor();

  await demo.locator("#prove-missing-zero").click();
  await demo
    .getByText("kind\tsigned-natlike-missing-zero")
    .waitFor({ timeout: 120_000 });
  await demo.getByText("theorem_oracle\t(APP missing zero)").waitFor();
  await demo.getByText("receiver\thol missing-zero receiver 7").waitFor();

  const missingZeroDownloads = [];
  const bothMissingZeroDownloads = new Promise((resolve) => {
    demo.on("download", (download) => {
      missingZeroDownloads.push(download);
      if (missingZeroDownloads.length === 2) resolve();
    });
  });
  await demo.locator("#download-missing-zero").click();
  await bothMissingZeroDownloads;
  assert.deepEqual(
    missingZeroDownloads.map((download) => download.suggestedFilename()).sort(),
    ["missing-zero.attestation.txt", "missing-zero.sqlite"],
  );

  await demo.locator("#open-missing-zero-state").click();
  await demo.getByText(/Opened trusted state/).waitFor();
  await demo.locator("#connection").selectOption("7");
  await demo.locator("#close").click();
  await demo.getByText("Missing-zero receiver cleaned up").waitFor();
  assert.equal(await demo.locator('#connection option[value="7"]').count(), 0);
  assert.equal(await demo.locator("#download-missing-zero").isDisabled(), true);
  assert.equal(
    await demo.locator("#open-missing-zero-state").isDisabled(),
    true,
  );
  await demo.locator("#connection").selectOption("8");
  await demo.locator("#recipe").fill("truth");
  await demo.locator("#run-hol").click();
  await demo.getByText("statement\ttrue").waitFor();
});
