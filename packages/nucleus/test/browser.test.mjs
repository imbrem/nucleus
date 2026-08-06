import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { readFile } from "node:fs/promises";
import { createServer } from "node:http";
import { join } from "node:path";
import test from "node:test";
import { chromium } from "playwright-core";

const root = new URL("..", import.meta.url).pathname;
const repository = new URL("../../..", import.meta.url).pathname;
const fixture = new URL("./fixture.sqlite", import.meta.url).pathname;

/**
 * Serves the package with Caddy, from the config `glu demo` uses.
 *
 * Not a server written here. A static file server has to get conditional
 * requests, byte ranges, and content types right, and a hand-rolled one gets
 * them subtly wrong -- which matters, because reading a database without
 * downloading it *is* a pile of range requests. Caddy already does all of it,
 * it is already in the toolchain, and sharing the demo's config means a test
 * sees the headers a visitor gets.
 *
 * `crates/repl/samples/` is served at `/cas/`, which is the whole of the
 * "minimal kernel" these tests use: the files are named by their own
 * addresses, so a file server answers `GET /cas/<address>` correctly with no
 * CAS-aware code anywhere. Anything that serves a directory -- nginx, S3,
 * GitHub Pages -- is a read-only kernel by that fact alone.
 */
async function servePackage(context) {
  const port = await freePort();
  const origin = `http://127.0.0.1:${port}`;
  const caddy = spawn(
    "caddy",
    ["run", "--adapter", "caddyfile", "--config", join(root, "demo.caddyfile")],
    {
      stdio: ["ignore", "ignore", "pipe"],
      env: {
        ...process.env,
        NUCLEUS_ADDRESS: origin,
        NUCLEUS_ROOT: root,
        NUCLEUS_SAMPLES: join(repository, "crates/repl/samples"),
        NUCLEUS_TLS: "",
      },
    },
  );
  context.after(() => caddy.kill());
  await waitFor(origin, caddy);
  return origin;
}

/** Picks a port nothing is listening on. */
async function freePort() {
  const probe = createServer();
  await new Promise((resolve) => probe.listen(0, "127.0.0.1", resolve));
  const { port } = probe.address();
  await new Promise((resolve) => probe.close(resolve));
  return port;
}

/** Waits for `origin` to answer, or reports why it never will. */
async function waitFor(origin, child) {
  let complaint = "";
  child.stderr?.on("data", (chunk) => {
    complaint += chunk;
  });
  for (let attempt = 0; attempt < 200; attempt += 1) {
    try {
      await fetch(`${origin}/demo.html`);
      return;
    } catch {
      await new Promise((resolve) => setTimeout(resolve, 25));
    }
  }
  throw new Error(`the demo server never came up:\n${complaint}`);
}

/**
 * Starts the real HTTP kernel over the fixture database.
 *
 * This is the separate-process, cross-origin half of the demo: a kernel the
 * page reaches only over HTTP.
 */
async function startKernel(context) {
  const child = spawn(
    "cargo",
    ["run", "--quiet", "-p", "covalence-bin-cas-serve", "--", fixture],
    { cwd: repository, stdio: ["ignore", "pipe", "inherit"] },
  );
  context.after(() => child.kill());

  let output = "";
  const lines = await new Promise((resolve, reject) => {
    child.stdout.on("data", (chunk) => {
      output += chunk;
      const complete = output.trim().split("\n");
      // One line per admitted file, then the base URL.
      if (complete.length >= 2) resolve(complete);
    });
    child.on("exit", (code) => reject(new Error(`cas-serve exited ${code}`)));
  });

  return { address: lines[0].split(" ")[0], baseUrl: lines[lines.length - 1] };
}

async function openPage(context, origin) {
  const executablePath = process.env.CHROMIUM_PATH;
  assert.ok(executablePath, "CHROMIUM_PATH is set by the Nix shell");
  const browser = await chromium.launch({
    executablePath,
    headless: true,
    args: ["--no-sandbox"],
  });
  context.after(() => browser.close());
  const page = await browser.newPage();
  page.on("console", (message) => {
    if (message.type() === "error") console.error("page:", message.text());
  });
  await page.goto(`${origin}/test/browser.html`);
  await page.waitForFunction(() => document.body.dataset.ready === "yes");
  return page;
}

test("a kernel runs in the browser and reads a database by address", async (context) => {
  const origin = await servePackage(context);
  const page = await openPage(context, origin);
  const database = await readFile(fixture);

  const result = await page.evaluate(async (bytes) => {
    const kernel = new window.nucleus.Kernel();
    const address = kernel.put(new Uint8Array(bytes));
    return {
      address,
      mount: kernel.mountName(),
      uri: kernel.uri(address),
      rows: JSON.parse(kernel.query(address, "SELECT a, b, sum FROM adder ORDER BY a")),
    };
  }, Array.from(database));

  assert.match(result.address, /^[0-9a-f]{64}$/);
  assert.equal(result.mount, "cas");
  assert.ok(result.uri.includes("vfs=cas"), result.uri);
  assert.deepEqual(result.rows.columns, ["a", "b", "sum"]);
  assert.deepEqual(result.rows.rows, [
    [2, 3, 5],
    [7, 8, 15],
  ]);
});

test("the browser reads a database from a kernel it reaches over HTTP", async (context) => {
  const origin = await servePackage(context);
  const kernel = await startKernel(context);
  const page = await openPage(context, origin);

  const result = await page.evaluate(async ({ baseUrl, address }) => {
    const local = new window.nucleus.Kernel();
    // Fetched across an origin, verified against its address, then admitted.
    const length = await window.nucleus.fetchInto(local, baseUrl, address);
    return {
      length,
      held: local.addresses(),
      rows: JSON.parse(local.query(address, "SELECT sum FROM adder ORDER BY a")),
    };
  }, kernel);

  assert.ok(result.length > 0);
  assert.deepEqual(result.held, [kernel.address]);
  assert.deepEqual(result.rows.rows, [[5], [15]]);
});

test("the HTTP kernel really serves ranges", async (context) => {
  const origin = await servePackage(context);
  const kernel = await startKernel(context);
  const page = await openPage(context, origin);

  const result = await page.evaluate(
    async ({ baseUrl, address }) =>
      await window.nucleus.fetchRange(baseUrl, address, 0, 14),
    kernel,
  );

  // Every SQLite database begins with this, so a ranged read is verifiable by
  // eye as well as by assertion. `bytes=0-14` is 15 bytes, because HTTP ranges
  // are inclusive at both ends -- asking for 0-15 would also pull the NUL that
  // terminates the header string.
  const header = new TextDecoder().decode(Uint8Array.from(Object.values(result.bytes)));
  assert.equal(header, "SQLite format 3");
  assert.match(result.contentRange, /^bytes 0-14\//);
});

test("bytes which do not match their address are refused", async (context) => {
  const origin = await servePackage(context);
  const kernel = await startKernel(context);
  const page = await openPage(context, origin);

  const result = await page.evaluate(async ({ baseUrl, address }) => {
    const local = new window.nucleus.Kernel();
    const response = await fetch(`${baseUrl}/cas/${address}`);
    const bytes = new Uint8Array(await response.arrayBuffer());
    // A hostile or broken server, simulated by corrupting what it sent.
    bytes[100] ^= 0xff;
    try {
      local.admit(address, bytes);
      return { refused: false, held: local.addresses() };
    } catch (error) {
      return { refused: true, message: String(error), held: local.addresses() };
    }
  }, kernel);

  assert.ok(result.refused, "tampered content must be refused");
  assert.match(result.message, /does not match its address/);
  assert.deepEqual(result.held, [], "refused content must not be stored");
});

test("the upstream SQLite shell runs in the browser", async (context) => {
  const origin = await servePackage(context);
  const page = await openPage(context, origin);
  const database = await readFile(fixture);

  const result = await page.evaluate(async (bytes) => {
    const kernel = new window.nucleus.Kernel();
    const address = kernel.put(new Uint8Array(bytes));

    // `shell.wasm` is `shell.c` compiled for wasm32-wasip1, fetched like any
    // other asset and instantiated with a partial WASI host.
    const shell = await fetch("../generated/shell.wasm");
    const run = await window.nucleus.runShell(kernel, shell, {
      args: [
        `file:${address}?mode=ro&immutable=1&vfs=cas`,
        "-batch",
        "-header",
        "SELECT a, b, sum FROM adder;",
      ],
    });
    return { ...run, address };
  }, Array.from(database));

  assert.equal(result.status, 0, `stderr: ${result.stderr}`);
  assert.equal(result.stdout.trim(), "a|b|sum\n2|3|5\n7|8|15");
});

test("the shell in the browser has no filesystem to reach", async (context) => {
  const origin = await servePackage(context);
  const page = await openPage(context, origin);

  const result = await page.evaluate(async () => {
    const kernel = new window.nucleus.Kernel();
    const shell = await fetch("../generated/shell.wasm");
    return await window.nucleus.runShell(kernel, shell, {
      args: ["/etc/passwd", "-batch", "SELECT 1;"],
    });
  });

  // Its databases arrive by address or not at all.
  assert.notEqual(result.status, 0);
});
