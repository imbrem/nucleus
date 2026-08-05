import assert from "node:assert/strict";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { fileURLToPath } from "node:url";
import test from "node:test";

const execFileAsync = promisify(execFile);

test("parses the experimental kernel WIT boundary", async () => {
  const wit = fileURLToPath(
    new URL("../../../crates/repl/wit", import.meta.url),
  );
  const { stdout } = await execFileAsync("wasm-tools", [
    "component",
    "wit",
    wit,
  ]);
  assert.match(stdout, /world kernel/);
  assert.match(stdout, /resource connection/);
  assert.match(stdout, /resource pinned-artifact/);
  assert.match(stdout, /authenticate/);
  assert.match(stdout, /trust-import/);
});
