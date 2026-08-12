import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import test from "node:test";
import { CadicalSolver } from "../dist/cadical-node.js";
import { drive, init, Repl } from "../dist/index.js";

async function repl() {
  await init({
    module_or_path: await readFile(
      new URL("../generated/nucleus_bg.wasm", import.meta.url),
    ),
  });
  return new Repl();
}

async function say(repl, host, form) {
  return (await drive(repl, host, form)).output;
}

test("the JS REPL checks real CaDiCaL SAT and binary LRAT results", async () => {
  const session = await repl();
  const host = { sat: new CadicalSolver() };

  assert.match(await say(session, host, "(sat-demo and-sat)"), /expected sat/);
  assert.match(await say(session, host, "(sat-solve)"), /^\(sat /);
  assert.equal(await say(session, host, "(sat-model)"), "(1 2 3)");
  assert.match(await say(session, host, "(sat-checked)"), /^\(sat /);
  assert.equal(await say(session, host, "(sat-status)"), "sat");

  assert.match(
    await say(session, host, "(sat-demo and-unsat)"),
    /expected unsat/,
  );
  assert.equal(await say(session, host, "(sat-solve)"), "unsat");
  assert.match(await say(session, host, "(sat-proof-text)"), / 0/);
  assert.match(
    await say(session, host, "(sat-proof)"),
    /^\([0-9a-f]{64} binary [1-9][0-9]*\)$/,
  );
  assert.match(await say(session, host, "(sat-result)"), /^\(unsat /);
  assert.equal(await say(session, host, "(sat-checked)"), "unsat");
  assert.equal(await say(session, host, "(sat-status)"), "unsat");
  assert.match(await say(session, host, "(sat-database)"), /^[0-9a-f]{64}$/);
});

test("a malicious JS solver claim cannot create checked state", async () => {
  const session = await repl();
  const hostile = {
    sat: { solve: async () => ({ kind: "sat", model: [1n, 2n, 3n] }) },
  };
  await say(session, hostile, "(sat-demo and-unsat)");
  const before = await say(session, hostile, "(sat-database)");
  assert.match(await say(session, hostile, "(sat-solve)"), /^error:/);
  assert.match(await say(session, hostile, "(sat-status)"), /^\(rejected /);
  assert.match(await say(session, hostile, "(sat-result)"), /^error:/);
  assert.match(await say(session, hostile, "(sat-checked)"), /^error:/);
  assert.equal(await say(session, hostile, "(sat-database)"), before);
});
