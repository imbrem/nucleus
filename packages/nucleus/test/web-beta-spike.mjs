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

test("a direct wasm-bindgen guest builds an authority-free checked HOL plan", async (context) => {
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

  const browser = await chromium.launch({
    executablePath: process.env.CHROMIUM_PATH,
    headless: true,
    args: ["--no-sandbox", "--disable-dev-shm-usage"],
  });
  context.after(() => browser.close());
  const page = await browser.newPage();
  const address = server.address();
  assert.notEqual(address, null);
  assert.equal(typeof address, "object");
  await page.goto(`http://127.0.0.1:${address.port}/test/web-beta-spike.html`);
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
  assert.match(result.namespace, /^\d+$/);
  assert.match(result.schema, /^[0-9a-f]{64}$/);
  assert.match(result.imageHash, /^[0-9a-f]{64}$/);
  assert.match(result.signer, /^[0-9a-f]{64}$/);
  assert.equal(result.signerMatchesKernel, true);
  assert.ok(result.imageBytes > 0);
  assert.equal(result.publicKeyBytes, 32);
  assert.equal(result.signatureBytes, 64);
  assert.equal(result.recipeBytes, 105);
  assert.equal(result.guestWasDisposableWorker, true);
  // The disposable realm protects the key but deliberately does not pretend to
  // remove browser network/storage/timer capabilities from untrusted JS glue.
  assert.equal(result.guestStillHadAmbientBrowserCapabilities, true);
  assert.equal(result.malformedRejected, true);
});
