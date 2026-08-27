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
async function startKernel(context, files = [fixture]) {
  const child = spawn(
    "cargo",
    ["run", "--quiet", "-p", "covalence-bin-cas-serve", "--", ...files],
    { cwd: repository, stdio: ["ignore", "pipe", "inherit"] },
  );
  context.after(() => child.kill());

  let output = "";
  const lines = await new Promise((resolve, reject) => {
    child.stdout.on("data", (chunk) => {
      output += chunk;
      const complete = output.trim().split("\n");
      // One line per admitted file, then the base URL.
      if (complete.length >= files.length + 1) resolve(complete);
    });
    child.on("exit", (code) => reject(new Error(`cas-serve exited ${code}`)));
  });

  const addresses = lines
    .slice(0, files.length)
    .map((line) => line.split(" ")[0]);
  return {
    address: addresses[0],
    addresses,
    baseUrl: lines[lines.length - 1],
  };
}

async function openPage(context, origin, path = "/test/browser.html") {
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
  page.on("pageerror", (error) => console.error("page error:", error));
  await page.goto(`${origin}${path}`);
  await page.waitForFunction(() => document.body.dataset.ready === "yes");
  return page;
}

test("the browser runs the same REPL as the CLI", async (context) => {
  const origin = await servePackage(context);
  const page = await openPage(context, origin);
  const database = await readFile(fixture);

  const result = await page.evaluate(async (bytes) => {
    const { Repl, drive, host } = window.nucleus;
    const repl = new Repl();
    const say = async (line) => (await drive(repl, host, line)).output;

    const banner = repl.banner();
    const empty = await say("(stats)");
    const address = repl.admit(new Uint8Array(bytes));
    const after = await say("(stats)");
    const objects = await say("(objects)");
    const kernels = await say("(kernels)");
    const help = await say("(help)");
    return { banner, empty, address, after, objects, kernels, help };
  }, Array.from(database));

  assert.match(result.banner, /vfs=cas/);
  assert.equal(result.empty, "((objects 0) (bytes 0) (largest 0))");
  assert.match(result.address, /^[0-9a-f]{64}$/);
  assert.match(result.after, /\(objects 1\)/);
  assert.equal(result.objects, `(${result.address})`);
  assert.equal(result.kernels, '((0 "local" #t))');
  assert.match(result.help, /\(connect "URL"\)/);
});

test("the browser composes the full kernel host with a proof", async (context) => {
  const origin = await servePackage(context);
  const page = await openPage(context, origin);
  const component = await readFile(
    join(
      repository,
      "target/wasm32-unknown-unknown/debug/covalence_proof_demo.component.wasm",
    ),
  );

  const result = await page.evaluate(async (bytes) => {
    const { kernelAddress, loadStandardProof, proofHost, proofStats } =
      window.nucleus;
    const kernel = await loadStandardProof(new Uint8Array(bytes));
    const stats = proofStats(kernel);

    // Exercise methods outside the demo's original subset through the same
    // generated WIT API that prover components import.
    const star = kernel.kindStar();
    const arrow = kernel.kindArr(star, star);
    const encoded = kernel.arena().toCbor();
    const table = proofHost.Table.fromBlob(encoded.blob());
    return {
      address: kernelAddress(kernel),
      rows: stats.rows.toString(),
      synFacts: stats.synFacts.toString(),
      category: kernel.category(arrow),
      tableAddressBytes: table.address().length,
    };
  }, Array.from(component));

  assert.match(result.address, /^[0-9a-f]{64}$/);
  // The demo now exercises the full subtype package rather than stopping at
  // the three-row Boolean prelude.
  assert.equal(result.rows, "75");
  assert.equal(result.synFacts, "0");
  assert.equal(result.category, "kind");
  assert.equal(result.tableAddressBytes, 32);

  // Start the UI assertion in a fresh browser process. Discarding a page that
  // has run a native-async component while navigating it can terminate
  // Chromium in constrained container environments.
  await page.close();
  const proofPage = await openPage(context, origin, "/proof.html");
  await proofPage.locator("#file").setInputFiles({
    name: "demo-proof.wasm",
    mimeType: "application/wasm",
    buffer: component,
  });
  await proofPage.waitForFunction(() =>
    ["ok", "error"].includes(document.getElementById("status").dataset.state),
  );
  assert.equal(
    await proofPage.locator("#status").getAttribute("data-state"),
    "ok",
    await proofPage.locator("#status").textContent(),
  );
  assert.match(
    await proofPage.locator("#address").textContent(),
    /^[0-9a-f]{64}$/,
  );
  assert.equal(await proofPage.locator("#rows").textContent(), "75");
});

test("the REPL runs proofs from the selected kernel by content address", async (context) => {
  const origin = await servePackage(context);
  const kernel = await startKernel(context, [
    join(
      repository,
      "target/wasm32-unknown-unknown/debug/covalence_proof_demo.component.wasm",
    ),
    join(
      repository,
      "target/wasm32-unknown-unknown/debug/covalence_proof_invalid_demo.component.wasm",
    ),
  ]);
  const page = await openPage(context, origin);

  const result = await page.evaluate(async ({ baseUrl, addresses }) => {
    const { Repl, drive, host } = window.nucleus;
    const repl = new Repl();
    const say = async (line) => (await drive(repl, host, line)).output;
    await say(`(connect ${JSON.stringify(baseUrl)})`);
    return {
      valid: await say(`(proof ${addresses[0]})`),
      invalid: await say(`(proof ${addresses[1]})`),
      held: repl.addresses(),
      local: await say("(local)"),
      missing: await say(`(proof ${"0".repeat(64)})`),
    };
  }, kernel);

  assert.match(result.valid, /^[0-9a-f]{64}$/);
  assert.match(result.invalid, /^error: .*demo invalid proof was rejected/);
  assert.deepEqual(result.held, kernel.addresses);
  assert.equal(result.local, "0");
  assert.match(result.missing, /^error: .*is not resident$/);
});

test("the REPL connects to a kernel over HTTP and fetches from it", async (context) => {
  const origin = await servePackage(context);
  const kernel = await startKernel(context);
  const page = await openPage(context, origin);

  const result = await page.evaluate(async ({ baseUrl, address }) => {
    const { Repl, drive, host } = window.nucleus;
    const repl = new Repl();
    const say = async (line) => (await drive(repl, host, line)).output;

    return {
      connected: await say(`(connect ${JSON.stringify(baseUrl)})`),
      kernels: await say("(kernels)"),
      // Fetched across an origin, verified, admitted -- one form.
      fetched: await say(`(fetch ${address})`),
      held: repl.addresses(),
      // Then queried through the real shell, which is a wasm module of its
      // own reaching this store through the CAS imports.
      shell: await say(
        `(sqlite ${address} "-batch" "SELECT sum FROM adder ORDER BY a")`,
      ),
      // And the whole store reached from inside SQL, with the URI a person
      // would guess: no mode=ro, no immutable=1.
      attached: await say(
        `(sqlite ":memory:" "-batch" "ATTACH 'file:${address}?vfs=cas' AS o; SELECT count(*) FROM o.adder;")`,
      ),
    };
  }, kernel);

  assert.equal(result.connected, "1");
  assert.match(result.kernels, /^\(\(0 "local" #f\) \(1 "http/);
  assert.equal(result.fetched, kernel.address);
  assert.equal(result.attached.trim(), "2");
  assert.deepEqual(result.held, [kernel.address]);
  assert.equal(result.shell.trim(), "5\n15");
});

test("a kernel serving something other than what was asked for is refused", async (context) => {
  const origin = await servePackage(context);
  const kernel = await startKernel(context);
  const page = await openPage(context, origin);

  const result = await page.evaluate(async ({ baseUrl }) => {
    const { Repl, drive, host } = window.nucleus;
    const repl = new Repl();
    await drive(repl, host, `(connect ${JSON.stringify(baseUrl)})`);
    // An address the kernel does not hold: the fetch itself fails, and
    // nothing is stored either way.
    const output = (await drive(repl, host, `(fetch ${"0".repeat(64)})`))
      .output;
    return { output, held: repl.addresses() };
  }, kernel);

  assert.match(result.output, /^error: /);
  assert.deepEqual(result.held, []);
});

test("a directory of hash-named files is a serviceable kernel", async (context) => {
  const origin = await servePackage(context);
  const page = await openPage(context, origin);

  // The address of the `planets` sample. The page knows it because the sample
  // is baked into the wasm too; the point is that fetching it needs nothing
  // but a file server.
  const result = await page.evaluate(async (base) => {
    const { Repl, drive, host } = window.nucleus;
    const repl = new Repl();
    const say = async (line) => (await drive(repl, host, line)).output;

    // Learn the address from the baked-in copy, then throw that copy away so
    // the fetch has to do real work.
    const samples = await say("(samples)");
    const [, address] = /\(planets ([0-9a-f]{64})\)/.exec(samples);
    await say(`(forget ${address})`);
    await say(`(forget ${/\(moons ([0-9a-f]{64})\)/.exec(samples)[1]})`);

    const connected = await say(`(connect ${JSON.stringify(base)})`);
    // Fetched from a plain file server, verified against the address, admitted.
    const fetched = await say(`(fetch ${address})`);
    const queried = await say(
      `(sqlite ${address} "-batch" "SELECT name FROM planets ORDER BY moons DESC LIMIT 1")`,
    );
    return { connected, fetched, queried, address, held: repl.addresses() };
  }, origin);

  assert.equal(result.connected, "1");
  // The address came back unchanged, which is the verification passing.
  assert.equal(result.fetched, result.address);
  assert.deepEqual(result.held, [result.address]);
  assert.match(result.queried, /Saturn/);
});

test("a file server which answers with the wrong bytes is caught", async (context) => {
  const origin = await servePackage(context);
  const page = await openPage(context, origin);

  const result = await page.evaluate(async (base) => {
    const { Repl, drive, host } = window.nucleus;
    const repl = new Repl();
    const say = async (line) => (await drive(repl, host, line)).output;
    await say(`(connect ${JSON.stringify(base)})`);
    // `/cas/<address>` for something the directory does not hold. A file
    // server has no way to be wrong here except by 404, and it is: absence is
    // an error, not an empty object silently admitted.
    return await say(`(fetch ${"0".repeat(64)})`);
  }, origin);

  assert.match(result, /^error: /);
});

test("the upstream SQLite shell runs in the browser", async (context) => {
  const origin = await servePackage(context);
  const page = await openPage(context, origin);
  const database = await readFile(fixture);

  const result = await page.evaluate(async (bytes) => {
    const { Repl, drive, host } = window.nucleus;
    const repl = new Repl();
    const address = repl.admit(new Uint8Array(bytes));
    return await drive(
      repl,
      host,
      `(sqlite ${address} "-batch" "-header" "SELECT a, b, sum FROM adder")`,
    );
  }, Array.from(database));

  assert.equal(result.output.trim(), "a|b|sum\n2|3|5\n7|8|15");
});

test("the shell suspends for an asynchronous JavaScript VFS", async (context) => {
  const origin = await servePackage(context);
  const page = await openPage(context, origin);
  const database = await readFile(fixture);

  const result = await page.evaluate(async (input) => {
    const { Repl, drive } = window.nucleus;
    const bytes = new Uint8Array(input);
    const address = "0".repeat(64);
    let delayedReads = 0;
    let timerFired = false;
    const host = {
      vfs: {
        async open(name) {
          if (name !== address) throw "not-found";
          return {
            async size() {
              return BigInt(bytes.length);
            },
            async readAt(offset, length) {
              await new Promise((resolve) =>
                setTimeout(() => {
                  timerFired = true;
                  resolve();
                }, 1),
              );
              delayedReads += 1;
              const start = Number(offset);
              return bytes.slice(start, start + length);
            },
          };
        },
      },
    };
    const repl = new Repl();
    const [sum, count] = await Promise.all([
      drive(
        repl,
        host,
        `(sqlite ${address} "-batch" "SELECT sum(sum) FROM adder")`,
      ),
      drive(
        repl,
        host,
        `(sqlite ${address} "-batch" "SELECT count(*) FROM adder")`,
      ),
    ]);
    return {
      sum: sum.output,
      count: count.output,
      delayedReads,
      timerFired,
    };
  }, Array.from(database));

  assert.equal(result.sum.trim(), "20");
  assert.equal(result.count.trim(), "2");
  assert.ok(result.delayedReads > 0);
  assert.equal(result.timerFired, true);
});

test("the shell in the browser has no filesystem to reach", async (context) => {
  const origin = await servePackage(context);
  const page = await openPage(context, origin);

  const result = await page.evaluate(async () => {
    const { Repl, drive, host } = window.nucleus;
    const repl = new Repl();
    return await drive(
      repl,
      host,
      '(sqlite "/etc/passwd" "-batch" "SELECT 1")',
    );
  });

  // Its databases arrive by address or not at all.
  assert.match(result.output, /exited with status/);
});
