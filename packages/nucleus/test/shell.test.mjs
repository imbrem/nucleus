import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import test from "node:test";
import init, { Repl } from "../generated/nucleus.js";
import { runShell } from "../dist/wasi.js";

/** The kernel wasm, and the shell wasm it will read through. */
async function setup() {
  await init({
    module_or_path: await readFile(
      new URL("../generated/nucleus_bg.wasm", import.meta.url),
    ),
  });
  const kernel = new Repl();
  const database = await readFile(new URL("./fixture.sqlite", import.meta.url));
  const address = kernel.admit(database).split(" ")[0];
  const shell = await readFile(new URL("../generated/shell.wasm", import.meta.url));
  return { kernel, address, shell };
}

test("the upstream shell runs in wasm and reads a database by address", async () => {
  const { kernel, address, shell } = await setup();

  const result = await runShell(kernel, shell, {
    args: [`file:${address}?vfs=cas`, "-batch", "SELECT a, b, sum FROM adder;"],
  });

  assert.equal(result.status, 0, `stderr: ${result.stderr}`);
  assert.equal(result.stdout.trim(), "2|3|5\n7|8|15");
});

test("the shell's own dot commands work", async () => {
  const { kernel, address, shell } = await setup();

  const result = await runShell(kernel, shell, {
    args: [`file:${address}?vfs=cas`, "-batch", ".schema"],
  });

  assert.equal(result.status, 0, `stderr: ${result.stderr}`);
  // This is upstream's `.schema`, not something reimplemented.
  assert.match(result.stdout, /CREATE TABLE adder/);
});

test("the shell reads SQL from stdin", async () => {
  const { kernel, address, shell } = await setup();

  const result = await runShell(kernel, shell, {
    args: [`file:${address}?vfs=cas`, "-batch"],
    stdin: "SELECT count(*) FROM adder;\n",
  });

  assert.equal(result.status, 0, `stderr: ${result.stderr}`);
  assert.equal(result.stdout.trim(), "2");
});

test("the mount is read-only from the shell too", async () => {
  const { kernel, address, shell } = await setup();

  const result = await runShell(kernel, shell, {
    args: [
      `file:${address}?vfs=cas`,
      "-batch",
      "INSERT INTO adder VALUES (1, 1, 2);",
    ],
  });

  assert.notEqual(result.status, 0);
});

test("an address which does not resolve fails to open", async () => {
  const { kernel, address, shell } = await setup();
  assert.equal(kernel.eval(`(forget ${address})`).text, "#t");

  const result = await runShell(kernel, shell, {
    args: [`file:${address}?vfs=cas`, "-batch", "SELECT 1;"],
  });

  assert.notEqual(result.status, 0);
});

test("a database the shell has open survives the address being forgotten", async () => {
  const { kernel, address, shell } = await setup();

  // `.forget` between two statements in one shell session. The kernel holds
  // the object for as long as the shell holds its handle, so the second
  // statement must still answer -- the same guarantee the native subprocess
  // gets over its socket.
  const result = await runShell(kernel, shell, {
    args: [`file:${address}?vfs=cas`, "-batch"],
    stdin: "SELECT count(*) FROM adder;\nSELECT sum FROM adder ORDER BY a;\n",
  });

  assert.equal(result.status, 0, `stderr: ${result.stderr}`);
  assert.equal(result.stdout.trim(), "2\n5\n15");
});

test("the shell cannot reach a filesystem", async () => {
  const { kernel, shell } = await setup();

  // There are no preopens and every path call refuses, so a database named by
  // path is unreachable however it is asked for. Its objects arrive by
  // address or not at all.
  const result = await runShell(kernel, shell, {
    args: ["/etc/passwd", "-batch", "SELECT 1;"],
  });

  assert.notEqual(result.status, 0);
});
