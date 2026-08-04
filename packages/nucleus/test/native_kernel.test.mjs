import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { createReadStream } from "node:fs";
import { stat } from "node:fs/promises";
import { createServer } from "node:http";
import { extname, join } from "node:path";
import test from "node:test";
import { chromium } from "playwright-core";

import { createKernelTestRelay } from "./kernel_relay.mjs";

const root = new URL("..", import.meta.url).pathname;
const contentTypes = {
  ".html": "text/html; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".wasm": "application/wasm",
};

test(
  "runs browser SQL against an allow-listed native kernel through an opaque relay",
  { skip: process.env.NUCLEUS_BIN === undefined },
  async (context) => {
    let relay;
    const server = createServer(async (request, response) => {
      if (relay !== undefined && (await relay(request, response))) return;
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
    await page.goto(`http://127.0.0.1:${address.port}/test/native_kernel.html`);
    await page.waitForFunction(
      () =>
        document.body.dataset.controllerKey !== undefined ||
        document.body.dataset.error !== undefined,
    );
    assert.equal(await page.locator("body").getAttribute("data-error"), null);
    const controllerKey = await page
      .locator("body")
      .getAttribute("data-controller-key");
    assert.match(controllerKey, /^[0-9a-f]{64}$/);

    const native = spawn(
      process.env.NUCLEUS_BIN,
      ["serve", "--listen", "127.0.0.1:0", "--allow-key", controllerKey],
      { stdio: ["ignore", "pipe", "pipe"] },
    );
    context.after(async () => {
      if (native.exitCode !== null) return;
      native.kill("SIGTERM");
      await new Promise((resolve) => native.once("exit", resolve));
    });
    const nativeInfo = await readNativeServerInfo(native);
    relay = createKernelTestRelay(`http://${nativeInfo.listen}/`);

    const result = await page.evaluate(
      async ({ endpoint, publicKey }) => {
        const repl = globalThis.nativeKernelTestRepl;
        let source;
        let reader;
        let primaryError;
        const step = async (name, operation) => {
          try {
            return await operation;
          } catch (error) {
            throw new Error(`${name}: ${String(error)}`);
          }
        };
        try {
          const kernel = await step(
            "connect",
            repl.connectFetch({
              endpoint,
              publicKey: Uint8Array.from(publicKey),
            }),
          );
          source = await step("open source", repl.openAt(kernel.id));
          await step(
            "create table",
            source.run("CREATE TABLE facts (name TEXT, value INTEGER)"),
          );
          await step(
            "insert",
            source.run("INSERT INTO facts VALUES ('native', 42)"),
          );
          const image = await step("serialize", source.serializeMain());
          const hash = await step("put image", source.putImage(image));

          reader = await step("open reader", repl.openAt(kernel.id));
          await step("attach image", reader.attachImage(hash, "snapshot"));
          const rows = await step(
            "read snapshot",
            reader.run("SELECT name, value FROM snapshot.facts"),
          );
          let readonly = false;
          try {
            await reader.run(
              "INSERT INTO snapshot.facts VALUES ('forbidden', 0)",
            );
          } catch {
            readonly = true;
          }
          return { hash, readonly, rows };
        } catch (error) {
          primaryError = error;
          throw error;
        } finally {
          try {
            await reader?.close();
            await source?.close();
          } catch (closeError) {
            if (primaryError === undefined) throw closeError;
          }
          repl.close();
        }
      },
      {
        endpoint: `${page.url().split("/test/")[0]}/kernel/`,
        publicKey: decodeHex(nativeInfo.kernelKey),
      },
    );

    assert.match(result.hash, /^[0-9a-f]{64}$/);
    assert.equal(result.readonly, true);
    assert.deepEqual(result.rows, {
      kind: "rows",
      columns: ["name", "value"],
      rows: [
        [
          { kind: "text", value: "native" },
          { kind: "integer", value: "42" },
        ],
      ],
    });
    // open + create + insert + serialize + put + open + attach + read +
    // rejected write + close + close: every operation gets exactly one attempt.
    assert.deepEqual(relay.counts, { channel: 1, invocation: 11 });
  },
);

function readNativeServerInfo(child) {
  return new Promise((resolve, reject) => {
    let stdout = "";
    let stderr = "";
    let listen;
    let kernelKey;
    const timeout = setTimeout(
      () => finish(new Error(`native kernel startup timed out: ${stderr}`)),
      10_000,
    );
    const finish = (error) => {
      clearTimeout(timeout);
      child.stdout.off("data", onStdout);
      child.stderr.off("data", onStderr);
      child.off("error", onError);
      child.off("exit", onExit);
      if (error !== undefined) reject(error);
      else resolve({ listen, kernelKey });
    };
    const inspect = () => {
      listen ??= /^listen (\S+)$/mu.exec(stdout)?.[1];
      kernelKey ??= /^kernel-key ([0-9a-f]{64})$/mu.exec(stdout)?.[1];
      if (listen !== undefined && kernelKey !== undefined) finish();
    };
    const onStdout = (chunk) => {
      stdout += chunk;
      inspect();
    };
    const onStderr = (chunk) => {
      stderr += chunk;
    };
    const onError = (error) => finish(error);
    const onExit = (code, signal) =>
      finish(
        new Error(
          `native kernel exited during startup (${code ?? signal}): ${stderr}`,
        ),
      );
    child.stdout.on("data", onStdout);
    child.stderr.on("data", onStderr);
    child.once("error", onError);
    child.once("exit", onExit);
  });
}

function decodeHex(value) {
  assert.match(value, /^[0-9a-f]{64}$/);
  return Array.from({ length: value.length / 2 }, (_, index) =>
    Number.parseInt(value.slice(index * 2, index * 2 + 2), 16),
  );
}
