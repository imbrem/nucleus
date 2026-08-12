import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import test from "node:test";
import init, { Repl } from "../generated/nucleus.js";
import { CadicalSolver } from "../dist/cadical-node.js";
import { drive } from "../dist/index.js";

await init({
  module_or_path: await readFile(
    new URL("../generated/nucleus_bg.wasm", import.meta.url),
  ),
});

test("the browser REPL checks an untrusted SAT model", async () => {
  const repl = new Repl();
  assert.match(repl.eval("(sat-demos)").text, /full-adder-unsat/);
  assert.match(
    repl.eval('(sat-set "p cnf 1 1\\n1 0\\n")').text,
    /custom/,
  );

  const host = {
    sat: {
      async solve(request) {
        assert.equal(request.proof.format, "binary-lrat");
        assert.match(new TextDecoder().decode(request.dimacs), /^p cnf /);
        return {
          kind: "sat",
          problem: request.problem,
          model: [1n, -2n, 3n],
        };
      },
    },
  };
  const result = await drive(repl, host, "(sat-solve)");
  assert.match(result.output, /checked-model/);
  assert.match(repl.eval("(sat-verify)").text, /sat; checked-model/);
});

test("a lying provider cannot create a checked result", async () => {
  const repl = new Repl();
  repl.eval("(sat-select and-sat)");
  const result = await drive(
    repl,
    {
      sat: {
        async solve(request) {
          return { kind: "sat", problem: request.problem, model: [] };
        },
      },
    },
    "(sat-solve)",
  );
  assert.match(result.output, /^error: SAT model rejected:/);
  assert.throws(() => repl.eval("(sat-result)"), /no checked SAT result/);
});

test("a wrong identity does not consume the pending solve", async () => {
  const repl = new Repl();
  repl.eval("(sat-select and-sat)");
  let request;
  const result = await drive(
    repl,
    {
      sat: {
        async solve(value) {
          request = value;
          return {
            kind: "unknown",
            problem: new Uint8Array(32),
            reason: "wrong identity",
          };
        },
      },
    },
    "(sat-solve)",
  );
  assert.match(result.output, /wrong problem/);
  assert.match(
    repl.completeSatUnknown(request.problem, "retry"),
    /unknown/,
  );
});

test("real CaDiCaL solves and refutes the circuit demos", async () => {
  const repl = new Repl();
  const host = { sat: new CadicalSolver() };

  repl.eval("(sat-select and-sat)");
  assert.match((await drive(repl, host, "(sat-solve)")).output, /checked-model/);

  repl.eval("(sat-select and-unsat)");
  assert.match((await drive(repl, host, "(sat-solve)")).output, /admitted=SatRefutation/);
  assert.match(repl.eval("(sat-proof)").text, /binary-lrat/);
  assert.match(repl.eval("(sat-proof-text)").text, /^\d+ .* 0/m);
});
