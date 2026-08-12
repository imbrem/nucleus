import assert from "node:assert/strict";
import test from "node:test";

import { drive } from "../dist/index.js";

const request = (job = "1") => ({
  kind: "solve",
  text: "",
  address: "",
  arguments: [],
  job,
  dimacs: new TextEncoder().encode("p cnf 1 1\n1 0\n"),
  maxModelLiterals: 1,
  maxProofBytes: 3,
});

class FakeRepl {
  constructor(step = request()) {
    this.step = step;
    this.pending = step.job;
    this.completions = 0;
    this.terminals = [];
  }

  eval() {
    if (!this.pending) throw new Error("no solve is pending");
    if (this.evaluated) throw new Error("a SAT solve is already pending");
    this.evaluated = true;
    return this.step;
  }

  completeSat(job, model) {
    this.terminals.push("sat");
    this.#take(job);
    assert.ok(model instanceof BigInt64Array);
    assert.deepEqual([...model], [1n]);
    return "(sat 1)";
  }

  completeUnsat(job, proof) {
    this.terminals.push("unsat");
    this.#take(job);
    assert.deepEqual([...proof], [1, 2, 3]);
    return "unsat";
  }

  abandonSat(job) {
    this.terminals.push("abandoned");
    this.#take(job);
  }

  completeSatUnknown(job) {
    this.terminals.push("unknown");
    this.#take(job);
  }

  completeSatFailure(job) {
    this.terminals.push("failed");
    this.#take(job);
  }

  cancelSat(job) {
    this.terminals.push("cancelled");
    this.#take(job);
  }

  #take(job) {
    if (job !== this.pending) throw new Error(`no pending SAT job ${job}`);
    this.pending = undefined;
    this.completions += 1;
  }
}

test("drive awaits an injected SAT solver and completes exactly once", async () => {
  const repl = new FakeRepl();
  let timerFired = false;
  let seen;
  const result = await drive(
    repl,
    {
      sat: {
        async solve(input) {
          seen = input;
          await new Promise((resolve) =>
            setTimeout(() => {
              timerFired = true;
              resolve();
            }, 1),
          );
          return { kind: "sat", model: [1n] };
        },
      },
    },
    "ignored by the fake",
  );

  assert.equal(result.output, "(sat 1)");
  assert.equal(timerFired, true);
  assert.equal(new TextDecoder().decode(seen.dimacs), "p cnf 1 1\n1 0\n");
  assert.deepEqual(seen.limits, {
    maxModelLiterals: 1,
    maxProofBytes: 3,
  });
  assert.equal(repl.completions, 1);
});

test("unknown and provider failure abandon the retained job", async () => {
  for (const [solve, terminal] of [
    [async () => ({ kind: "unknown", reason: "gave up" }), "unknown"],
    [
      async () => {
        throw new Error("solver crashed");
      },
      "failed",
    ],
  ]) {
    const repl = new FakeRepl();
    const result = await drive(repl, { sat: { solve } }, "ignored");
    assert.equal(repl.pending, undefined);
    assert.equal(repl.completions, 1);
    assert.deepEqual(repl.terminals, [terminal]);
    assert.match(result.output, /gave up|solver crashed/);
  }
});

test("malformed replies are abandoned before reaching Rust", async () => {
  for (const result of [
    { kind: "sat", model: ["not a bigint"] },
    { kind: "unsat", proof: "not bytes" },
  ]) {
    const repl = new FakeRepl();
    const line = await drive(
      repl,
      {
        sat: {
          async solve() {
            return result;
          },
        },
      },
      "ignored",
    );
    assert.match(line.output, /^error: /);
    assert.equal(repl.pending, undefined);
    assert.equal(repl.completions, 1);
  }
});

test("an already-aborted solve never invokes the provider", async () => {
  const repl = new FakeRepl();
  const controller = new AbortController();
  controller.abort();
  let calls = 0;
  const line = await drive(
    repl,
    {
      sat: {
        async solve() {
          calls += 1;
          return { kind: "sat", model: [1n] };
        },
      },
    },
    "ignored",
    { signal: controller.signal },
  );
  assert.equal(calls, 0);
  assert.match(line.output, /aborted/);
  assert.equal(repl.pending, undefined);
  assert.deepEqual(repl.terminals, ["cancelled"]);
});

test("abort abandons a job even when the provider ignores its signal", async () => {
  const repl = new FakeRepl();
  const controller = new AbortController();
  let started;
  const running = new Promise((resolve) => {
    started = resolve;
  });
  let finish;
  const ignored = new Promise((resolve) => {
    finish = resolve;
  });
  const driven = drive(
    repl,
    {
      sat: {
        async solve() {
          started();
          return await ignored;
        },
      },
    },
    "ignored",
    { signal: controller.signal },
  );
  await running;
  controller.abort();
  const line = await driven;
  assert.match(line.output, /aborted/);
  assert.equal(repl.pending, undefined);
  assert.equal(repl.completions, 1);
  assert.deepEqual(repl.terminals, ["cancelled"]);

  finish({ kind: "sat", model: [1n] });
  await Promise.resolve();
  assert.equal(repl.completions, 1);
});

test("abort listener is removed after a normal completion", async () => {
  const listeners = new Set();
  const signal = {
    aborted: false,
    addEventListener(_type, listener) {
      listeners.add(listener);
    },
    removeEventListener(_type, listener) {
      listeners.delete(listener);
    },
  };
  const repl = new FakeRepl();
  const line = await drive(
    repl,
    {
      sat: {
        async solve() {
          return { kind: "sat", model: [1n] };
        },
      },
    },
    "ignored",
    { signal },
  );
  assert.equal(line.output, "(sat 1)");
  assert.equal(listeners.size, 0);
});

test("oversized replies are abandoned before crossing the wasm boundary", async () => {
  for (const result of [
    { kind: "sat", model: [1n, 2n] },
    { kind: "unsat", proof: Uint8Array.of(1, 2, 3, 4) },
  ]) {
    const repl = new FakeRepl();
    const line = await drive(
      repl,
      {
        sat: {
          async solve() {
            return result;
          },
        },
      },
      "ignored",
    );
    assert.match(line.output, /exceeds its response bound/);
    assert.equal(repl.pending, undefined);
    assert.equal(repl.completions, 1);
  }
});

test("a stale cross-job completion cannot consume the current job", async () => {
  const repl = new FakeRepl(request("current"));
  repl.step = request("stale");
  const result = await drive(
    repl,
    {
      sat: {
        async solve() {
          return { kind: "sat", model: [1n] };
        },
      },
    },
    "ignored",
  );
  assert.match(result.output, /no pending SAT job stale/);
  assert.equal(repl.pending, "current");
  assert.equal(repl.completions, 0);
});

test("two concurrent drives invoke the provider only once", async () => {
  const repl = new FakeRepl();
  let calls = 0;
  let release;
  const blocked = new Promise((resolve) => {
    release = resolve;
  });
  const host = {
    sat: {
      async solve() {
        calls += 1;
        await blocked;
        return { kind: "unsat", proof: Uint8Array.of(1, 2, 3) };
      },
    },
  };
  const first = drive(repl, host, "first");
  const second = await drive(repl, host, "second");
  release();
  assert.match(second.output, /already pending/);
  assert.equal((await first).output, "unsat");
  assert.equal(calls, 1);
});
