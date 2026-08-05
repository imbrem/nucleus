import assert from "node:assert/strict";
import { createReadStream } from "node:fs";
import { createServer } from "node:http";
import { extname, join } from "node:path";
import { spawn } from "node:child_process";
import { createInterface } from "node:readline";
import { stat } from "node:fs/promises";
import test from "node:test";
import { chromium } from "playwright-core";

const packageRoot = new URL("..", import.meta.url).pathname;
const repositoryRoot = new URL("../../..", import.meta.url).pathname;
const contentTypes = {
  ".html": "text/html; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".wasm": "application/wasm",
};

async function launchKernel(context, allowedOrigin, componentPath) {
  const mode = componentPath === undefined ? "--kernel-http" : "--kernel-http-hol-component";
  const kernelArguments = [
    "run",
    "--quiet",
    "--locked",
    "-p",
    "covalence-bin-nucleus",
    "--",
    mode,
    "127.0.0.1:0",
    allowedOrigin,
  ];
  if (componentPath !== undefined) kernelArguments.push(componentPath);
  const child = spawn(
    "cargo",
    kernelArguments,
    { cwd: repositoryRoot, stdio: ["ignore", "pipe", "pipe"] },
  );
  let stderr = "";
  child.stderr.setEncoding("utf8");
  child.stderr.on("data", (chunk) => {
    stderr += chunk;
  });
  context.after(() => {
    if (child.exitCode === null) child.kill();
  });
  const metadata = new Map();
  for await (const line of createInterface({ input: child.stdout })) {
    const split = line.indexOf("\t");
    if (split !== -1) metadata.set(line.slice(0, split), line.slice(split + 1));
    if (
      metadata.has("url") &&
      metadata.has("public_key") &&
      (componentPath === undefined || metadata.has("component"))
    )
      break;
  }
  assert.equal(child.exitCode, null, stderr);
  assert.match(
    metadata.get("url"),
    /^http:\/\/127\.0\.0\.1:\d+\/v0\/signed-message$/,
  );
  assert.match(metadata.get("public_key"), /^[0-9a-f]{64}$/);
  return {
    child,
    url: metadata.get("url"),
    key: metadata.get("public_key"),
    component: metadata.get("component"),
  };
}

async function launchBrowser(context) {
  const executablePath = process.env.CHROMIUM_PATH;
  assert.ok(executablePath, "CHROMIUM_PATH is set by the Nix shell");
  const browser = await chromium.launch({
    executablePath,
    headless: true,
    args: ["--no-sandbox", "--disable-dev-shm-usage"],
  });
  context.after(() => browser.close());
  return browser;
}

async function launchStaticServer(context) {
  const server = createServer(async (request, response) => {
    const relative = new URL(request.url ?? "/", "http://localhost").pathname;
    const path = join(packageRoot, relative);
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
  const address = server.address();
  assert.notEqual(address, null);
  assert.equal(typeof address, "object");
  return `http://127.0.0.1:${address.port}`;
}

async function runPage(
  browser,
  base,
  endpoint,
  key,
  mode = "round-trip",
  component,
) {
  const page = await browser.newPage();
  const query = new URLSearchParams({ endpoint, key, mode });
  if (component !== undefined) query.set("component", component);
  await page.goto(`${base}/test/http-kernel.html?${query}`);
  await page.waitForFunction(
    () =>
      document.body.dataset.result !== undefined ||
      document.body.dataset.error !== undefined,
  );
  return {
    error: await page.locator("body").getAttribute("data-error"),
    outcomeUnknown:
      (await page.locator("body").getAttribute("data-outcome-unknown")) ===
      "true",
    result: await page.locator("body").getAttribute("data-result"),
  };
}

const holComponentPath = process.env.HOL_PROOF_COMPONENT_PATH;

test(
  "real Chromium imports and re-inspects a native allowlisted component artifact",
  { skip: holComponentPath === undefined },
  async (context) => {
    const base = await launchStaticServer(context);
    const [kernel, browser] = await Promise.all([
      launchKernel(context, base, holComponentPath),
      launchBrowser(context),
    ]);
    const page = await runPage(
      browser,
      base,
      kernel.url,
      kernel.key,
      "component-round-trip",
      kernel.component,
    );
    assert.equal(page.error, null);
    assert.equal(page.outcomeUnknown, false);
    const result = JSON.parse(page.result);
    assert.equal(result.kind, "signed-hol-component-artifact");
    assert.equal(result.component, kernel.component);
    assert.match(result.schema, /^[0-9a-f]{64}$/);
    assert.match(result.imageHash, /^[0-9a-f]{64}$/);
    assert.match(result.signer, /^[0-9a-f]{64}$/);
    assert.ok(result.imageBytes > 0);
    assert.deepEqual(result.received, {
      kind: "received-hol-snapshot",
      phases: result.received.phases,
      importId: "0",
      namespace: "1",
      context: "0",
      conclusion: "8",
    });
    assert.deepEqual(result.inspectedAfterReturn, result.received);
    assert.match(result.receiverState, /^[0-9a-f]{64}$/);
    assert.deepEqual(result.beforeCleanup, { kernels: 2, connections: 1 });
    assert.deepEqual(result.lifecycle, [
      "opening",
      "established",
      "closing",
      "closed",
    ]);
    const code =
      kernel.child.exitCode ??
      (await new Promise((resolve) =>
        kernel.child.once("exit", (exitCode) => resolve(exitCode)),
      ));
    assert.equal(code, 0);
  },
);

test(
  "real Chromium treats a wrong allowlisted hash as an authenticated definite error",
  { skip: holComponentPath === undefined },
  async (context) => {
    const base = await launchStaticServer(context);
    const [kernel, browser] = await Promise.all([
      launchKernel(context, base, holComponentPath),
      launchBrowser(context),
    ]);
    const page = await runPage(
      browser,
      base,
      kernel.url,
      kernel.key,
      "component-wrong-hash",
      kernel.component,
    );
    assert.equal(page.error, null);
    const result = JSON.parse(page.result);
    assert.match(result.operationError, /not allowlisted/i);
    assert.equal(result.outcomeUnknown, false);
    assert.deepEqual(result.lifecycle, [
      "opening",
      "established",
      "closing",
      "closed",
    ]);
  },
);

test(
  "real Chromium exactly retries an ambiguous allowlisted component command",
  { skip: holComponentPath === undefined },
  async (context) => {
    const base = await launchStaticServer(context);
    const [kernel, browser] = await Promise.all([
      launchKernel(context, base, holComponentPath),
      launchBrowser(context),
    ]);
    const proxy = await launchFailureProxy(
      context,
      kernel.url,
      "truncate-command",
    );
    const page = await runPage(
      browser,
      base,
      proxy.url,
      kernel.key,
      "component-recover",
      kernel.component,
    );
    assert.equal(page.error, null);
    const result = JSON.parse(page.result);
    assert.equal(result.outcomeUnknown, true);
    assert.equal(result.component, kernel.component);
    assert.deepEqual(result.lifecycle, [
      "opening",
      "established",
      "command-unknown",
      "established",
      "closing",
      "closed",
    ]);
    assert.deepEqual(proxy.requestAt(2), proxy.requestAt(3));
    assert.deepEqual(proxy.responseAt(2), proxy.responseAt(3));
  },
);

async function launchFailureProxy(context, target, failure) {
  let posts = 0;
  const requests = [];
  const responses = [];
  const server = createServer(async (request, response) => {
    response.setHeader("access-control-allow-origin", "*");
    response.setHeader("access-control-allow-methods", "POST, OPTIONS");
    response.setHeader("access-control-allow-headers", "Content-Type");
    if (request.method === "OPTIONS") {
      response.writeHead(204, { "content-length": "0" }).end();
      return;
    }
    posts += 1;
    const chunks = [];
    for await (const chunk of request) chunks.push(chunk);
    const requestBody = Buffer.concat(chunks);
    requests.push(requestBody);
    const upstream = await fetch(target, {
      method: "POST",
      body: requestBody,
      headers: { "content-type": "application/octet-stream" },
    });
    const body = Buffer.from(await upstream.arrayBuffer());
    responses.push(Buffer.from(body));
    if (
      (failure === "truncate" && posts === 2) ||
      (failure === "truncate-command" && posts === 3)
    ) {
      response.writeHead(200, {
        "content-type": "application/octet-stream",
        "content-length": String(body.length),
        "access-control-allow-origin": "*",
      });
      response.end(body.subarray(0, Math.max(1, body.length - 1)));
      return;
    }
    if (
      (failure === "tamper" && posts === 3) ||
      (failure === "tamper-handshake" && posts === 2)
    ) {
      body[body.length - 1] ^= 1;
    }
    response.writeHead(upstream.status, {
      "content-type": "application/octet-stream",
      "content-length": String(body.length),
      "access-control-allow-origin": "*",
    });
    response.end(body);
  });
  await new Promise((resolve) => server.listen(0, "127.0.0.1", resolve));
  context.after(() => server.close());
  const address = server.address();
  assert.notEqual(address, null);
  assert.equal(typeof address, "object");
  return {
    url: `http://127.0.0.1:${address.port}/v0/signed-message`,
    postCount: () => posts,
    requestAt: (index) => requests[index],
    responseAt: (index) => responses[index],
  };
}

test("real Chromium imports a signed beta artifact from native HTTP", async (context) => {
  const base = await launchStaticServer(context);
  const [kernel, browser] = await Promise.all([
    launchKernel(context, base),
    launchBrowser(context),
  ]);
  const page = await runPage(browser, base, kernel.url, kernel.key);
  assert.equal(page.error, null);
  assert.equal(page.outcomeUnknown, false);
  const result = JSON.parse(page.result);
  assert.deepEqual(result, {
    kind: "native-http-signed-hol-round-trip",
    statement: "(lambda x:bool. x) true = true",
    signer: result.signer,
    remoteConnection: "1",
    imageBytes: result.imageBytes,
    importId: "0",
    namespace: "1",
    context: "0",
    conclusion: "8",
    kernelId: 1,
    closedConnectionId: 1,
    sessionId: "1",
    sessionLifecycle: ["opening", "established", "closing", "closed"],
    independentInspection: {
      kernels: 1,
      connections: 0,
      sessionState: "closed",
      connectionLifecycle: ["opened", "closed"],
    },
    afterExplicitCleanup: { kernels: 0, connections: 0 },
  });
  assert.match(result.signer, /^[0-9a-f]{64}$/);
  assert.ok(result.imageBytes > 0);
  const code =
    kernel.child.exitCode ??
    (await new Promise((resolve) =>
      kernel.child.once("exit", (exitCode) => resolve(exitCode)),
    ));
  assert.equal(code, 0);
});

test("real Chromium rejects an out-of-band endpoint key mismatch", async (context) => {
  const base = await launchStaticServer(context);
  const [kernel, browser] = await Promise.all([
    launchKernel(context, base),
    launchBrowser(context),
  ]);
  const wrong = `${kernel.key.startsWith("00") ? "01" : "00"}${kernel.key.slice(2)}`;
  const page = await runPage(browser, base, kernel.url, wrong);
  assert.equal(page.result, null);
  assert.equal(page.outcomeUnknown, false);
  assert.match(
    page.error,
    /different endpoint|pinned endpoint|signer|signature|public key/i,
  );
});

test("real Chromium reports ambiguous handshake failure without application retry", async (context) => {
  const base = await launchStaticServer(context);
  const [kernel, browser] = await Promise.all([
    launchKernel(context, base),
    launchBrowser(context),
  ]);
  const proxy = await launchFailureProxy(context, kernel.url, "truncate");
  const page = await runPage(browser, base, proxy.url, kernel.key);
  assert.equal(page.result, null);
  assert.match(page.error, /native signed-kernel request failed/i);
  assert.equal(page.outcomeUnknown, true);
  assert.equal(proxy.postCount(), 2);
});

test("real Chromium treats a complete tampered post-dispatch reply as unknown", async (context) => {
  const base = await launchStaticServer(context);
  const [kernel, browser] = await Promise.all([
    launchKernel(context, base),
    launchBrowser(context),
  ]);
  const proxy = await launchFailureProxy(context, kernel.url, "tamper");
  const page = await runPage(browser, base, proxy.url, kernel.key);
  assert.equal(page.result, null);
  assert.match(page.error, /reply could not be accepted/i);
  assert.equal(page.outcomeUnknown, true);
  assert.equal(proxy.postCount(), 3);
});

test("real Chromium exactly retries one pending command and accepts its cached reply", async (context) => {
  const base = await launchStaticServer(context);
  const [kernel, browser] = await Promise.all([
    launchKernel(context, base),
    launchBrowser(context),
  ]);
  const proxy = await launchFailureProxy(
    context,
    kernel.url,
    "truncate-command",
  );
  const page = await runPage(
    browser,
    base,
    proxy.url,
    kernel.key,
    "recover-command",
  );
  assert.equal(page.error, null);
  const result = JSON.parse(page.result);
  assert.equal(result.outcomeUnknown, true);
  assert.equal(result.retryExact, true);
  assert.match(result.opened, /^\d+$/);
  assert.equal(proxy.postCount(), 6);
  assert.deepEqual(proxy.requestAt(2), proxy.requestAt(3));
  assert.deepEqual(proxy.responseAt(2), proxy.responseAt(3));
});

test("real Chromium poisons a failed OpenSession acceptance instead of retrying it", async (context) => {
  const base = await launchStaticServer(context);
  const [kernel, browser] = await Promise.all([
    launchKernel(context, base),
    launchBrowser(context),
  ]);
  const proxy = await launchFailureProxy(
    context,
    kernel.url,
    "tamper-handshake",
  );
  const page = await runPage(
    browser,
    base,
    proxy.url,
    kernel.key,
    "handshake-poison",
  );
  assert.equal(page.error, null);
  const result = JSON.parse(page.result);
  assert.match(result.acceptanceError, /signature|acceptance|session/i);
  assert.match(result.replayError, /already emitted|fresh session/i);
  assert.equal(proxy.postCount(), 2);
});

test("real Chromium cannot command a kernel restricted to another origin", async (context) => {
  const base = await launchStaticServer(context);
  const [kernel, browser] = await Promise.all([
    launchKernel(context, "http://127.0.0.1:1"),
    launchBrowser(context),
  ]);
  const page = await runPage(browser, base, kernel.url, kernel.key);
  assert.equal(page.result, null);
  assert.match(page.error, /failed to fetch|cors/i);
  assert.equal(page.outcomeUnknown, false);
});
