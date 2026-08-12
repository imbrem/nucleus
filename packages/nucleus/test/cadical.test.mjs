import assert from "node:assert/strict";
import { chmod, mkdtemp, rm, writeFile } from "node:fs/promises";
import { createServer } from "node:http";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { test } from "node:test";
import { CadicalSolver, createCadicalServer } from "../dist/cadical-node.js";
import { HttpSatSolver, LRAT_CONTENT_TYPE } from "../dist/sat-http.js";

const request = {
  dimacs: new TextEncoder().encode("p cnf 1 1\n1 0\n"),
  limits: { maxModelLiterals: 4, maxProofBytes: 1024 },
};

async function fixture(source) {
  const directory = await mkdtemp(join(tmpdir(), "nucleus-cadical-test-"));
  const executable = join(directory, "fake-cadical");
  await writeFile(executable, `#!/usr/bin/env node\n${source}`, {
    mode: 0o700,
  });
  await chmod(executable, 0o700);
  return {
    executable,
    [Symbol.asyncDispose]: () =>
      rm(directory, { recursive: true, force: true }),
  };
}

test("native provider parses SAT and uses fixed binary-LRAT arguments", async () => {
  await using fake = await fixture(`
    const fs = require("node:fs");
    if (!process.argv.includes("--binary") || process.argv.includes("--no-binary")) process.exit(3);
    const input = process.argv.at(-2);
    if (!fs.readFileSync(input, "utf8").startsWith("p cnf")) process.exit(4);
    fs.writeSync(1, "s SATISFIABLE\\nv 1 0\\n");
    process.exitCode = 10;
  `);
  const result = await new CadicalSolver({ executable: fake.executable }).solve(
    request,
  );
  assert.deepEqual(result, { kind: "sat", model: [1n] });
});

test("native provider returns bounded binary LRAT", async () => {
  await using fake = await fixture(`
    const fs = require("node:fs");
    fs.writeFileSync(process.argv.at(-1), Uint8Array.of(97, 6, 0, 2, 4, 0));
    fs.writeSync(1, "s UNSATISFIABLE\\n");
    process.exitCode = 20;
  `);
  const result = await new CadicalSolver({ executable: fake.executable }).solve(
    request,
  );
  assert.equal(result.kind, "unsat");
  assert.deepEqual([...result.proof], [97, 6, 0, 2, 4, 0]);
});

test("real CaDiCaL emits a binary LRAT artifact", async () => {
  const result = await new CadicalSolver().solve({
    ...request,
    dimacs: new TextEncoder().encode("p cnf 1 2\n1 0\n-1 0\n"),
  });
  assert.equal(result.kind, "unsat");
  assert.equal(result.proof[0], "a".charCodeAt(0));
});

test("native provider kills and waits for timeout, oversize, and cancellation", async () => {
  await using sleeper = await fixture(`setInterval(() => {}, 1000);`);
  await assert.rejects(
    new CadicalSolver({ executable: sleeper.executable, timeoutMs: 20 }).solve(
      request,
    ),
    /timed out/,
  );

  await using noisy = await fixture(
    `require("node:fs").writeSync(1, "x".repeat(10000)); setInterval(() => {}, 1000);`,
  );
  await assert.rejects(
    new CadicalSolver({
      executable: noisy.executable,
      maxStdoutBytes: 10,
    }).solve(request),
    /stdout exceeds/,
  );

  const controller = new AbortController();
  const pending = new CadicalSolver({ executable: sleeper.executable }).solve(
    request,
    controller.signal,
  );
  controller.abort();
  await assert.rejects(pending, /aborted/);

  await using descendant = await fixture(`
    const { spawn } = require("node:child_process");
    spawn(process.execPath, ["-e", "setInterval(() => {}, 1000)"], {
      stdio: "inherit",
    });
    setInterval(() => {}, 1000);
  `);
  await assert.rejects(
    new CadicalSolver({
      executable: descendant.executable,
      timeoutMs: 20,
    }).solve(request),
    /timed out/,
  );
});

test("native provider normalizes crashes and output bounds", async () => {
  await using crashed = await fixture(`process.exit(7);`);
  await assert.rejects(
    new CadicalSolver({ executable: crashed.executable }).solve(request),
    /exited with status 7/,
  );

  await using proofBomb = await fixture(`
    const fs = require("node:fs");
    fs.writeFileSync(process.argv.at(-1), "x".repeat(2048));
    fs.writeSync(1, "s UNSATISFIABLE\\n");
    process.exitCode = 20;
  `);
  await assert.rejects(
    new CadicalSolver({ executable: proofBomb.executable }).solve(request),
    /proof exceeds/,
  );

  await using stderrBomb = await fixture(`
    require("node:fs").writeSync(2, "x".repeat(2048));
    setInterval(() => {}, 1000);
  `);
  await assert.rejects(
    new CadicalSolver({
      executable: stderrBomb.executable,
      maxStderrBytes: 16,
    }).solve(request),
    /stderr exceeds/,
  );
});

test("native provider accepts CRLF status output and validates bounds", async () => {
  await using fake = await fixture(`
    require("node:fs").writeSync(1, "s SATISFIABLE\\r\\nv 1 0\\r\\n");
    process.exitCode = 10;
  `);
  assert.deepEqual(
    await new CadicalSolver({ executable: fake.executable }).solve(request),
    { kind: "sat", model: [1n] },
  );
  assert.throws(() => new CadicalSolver({ timeoutMs: 0 }), /invalid/);
  assert.throws(
    () => new CadicalSolver({ maxProofBytes: Number.MAX_SAFE_INTEGER }),
    /invalid/,
  );
});

test("native provider reaps inherited pipes after a successful parent exit", async () => {
  await using fake = await fixture(`
    const { spawn } = require("node:child_process");
    const descendant = spawn(
      process.execPath,
      ["-e", "setInterval(() => {}, 1000)"],
      { stdio: "inherit" },
    );
    descendant.unref();
    require("node:fs").writeSync(1, "s SATISFIABLE\\nv 1 0\\n");
    process.exitCode = 10;
  `);
  assert.deepEqual(
    await new CadicalSolver({
      executable: fake.executable,
      timeoutMs: 500,
    }).solve(request),
    { kind: "sat", model: [1n] },
  );
});

test("HTTP adapter and server preserve the injected solver boundary", async () => {
  const proof = Uint8Array.of(97, 6, 0, 2, 4, 0);
  const server = createCadicalServer({
    solver: {
      solve: async (received) => {
        assert.deepEqual(received.dimacs, request.dimacs);
        return { kind: "unsat", proof };
      },
    },
  });
  await new Promise((resolve) => server.listen(0, "127.0.0.1", resolve));
  try {
    const address = server.address();
    const result = await new HttpSatSolver(
      `http://127.0.0.1:${address.port}/`,
    ).solve(request);
    assert.deepEqual(result, { kind: "unsat", proof });
  } finally {
    await new Promise((resolve, reject) =>
      server.close((error) => (error ? reject(error) : resolve())),
    );
  }
});

test("HTTP adapter caps a streamed hostile response", async () => {
  const server = createServer((_request, response) => {
    response.writeHead(200, { "content-type": LRAT_CONTENT_TYPE });
    response.end(Uint8Array.of(1, 2, 3, 4, 5));
  });
  await new Promise((resolve) => server.listen(0, "127.0.0.1", resolve));
  try {
    const address = server.address();
    await assert.rejects(
      new HttpSatSolver(`http://127.0.0.1:${address.port}/`).solve({
        ...request,
        limits: { ...request.limits, maxProofBytes: 4 },
      }),
      /exceeds/,
    );
  } finally {
    await new Promise((resolve, reject) =>
      server.close((error) => (error ? reject(error) : resolve())),
    );
  }
});

test("HTTP server validates hostile solver results before serialization", async () => {
  const hostile = [
    {
      kind: "sat",
      model: {
        length: 0,
        *[Symbol.iterator]() {
          while (true) yield 1n;
        },
      },
    },
    { kind: "sat", model: [0n] },
    { kind: "sat", model: [1n << 100n] },
    { kind: "unsat", proof: "not bytes" },
    { kind: "invalid", proof: Uint8Array.of(1) },
  ];
  for (const result of hostile) {
    const server = createCadicalServer({
      solver: { solve: async () => result },
    });
    await new Promise((resolve) => server.listen(0, "127.0.0.1", resolve));
    try {
      const address = server.address();
      await assert.rejects(
        new HttpSatSolver(`http://127.0.0.1:${address.port}/`).solve(request),
        /HTTP 502/,
        `hostile ${result.kind} result should be rejected`,
      );
    } finally {
      await new Promise((resolve, reject) =>
        server.close((error) => (error ? reject(error) : resolve())),
      );
    }
  }
});

test("HTTP server snapshots an untrusted model length", async () => {
  let reads = 0;
  const model = new Proxy([1n], {
    get(target, property, receiver) {
      if (property === "length") {
        reads += 1;
        return reads;
      }
      return Reflect.get(target, property, receiver);
    },
  });
  const server = createCadicalServer({
    solver: { solve: async () => ({ kind: "sat", model }) },
  });
  await new Promise((resolve) => server.listen(0, "127.0.0.1", resolve));
  try {
    const address = server.address();
    assert.deepEqual(
      await new HttpSatSolver(`http://127.0.0.1:${address.port}/`).solve(
        request,
      ),
      { kind: "sat", model: [1n] },
    );
    assert.equal(reads, 1);
  } finally {
    await new Promise((resolve, reject) =>
      server.close((error) => (error ? reject(error) : resolve())),
    );
  }
});

test("HTTP cancellation reaches the injected server capability", async () => {
  let observeAbort;
  const aborted = new Promise((resolve) => {
    observeAbort = resolve;
  });
  const server = createCadicalServer({
    solver: {
      solve: async (_request, signal) => {
        await new Promise((resolve) =>
          signal.addEventListener("abort", resolve, { once: true }),
        );
        observeAbort();
        return { kind: "unknown" };
      },
    },
  });
  await new Promise((resolve) => server.listen(0, "127.0.0.1", resolve));
  try {
    const address = server.address();
    const controller = new AbortController();
    const pending = new HttpSatSolver(
      `http://127.0.0.1:${address.port}/`,
    ).solve(request, controller.signal);
    setTimeout(() => controller.abort(), 10);
    await assert.rejects(pending, /abort/i);
    await aborted;
  } finally {
    await new Promise((resolve, reject) =>
      server.close((error) => (error ? reject(error) : resolve())),
    );
  }
});

test("HTTP server owns cancellation when the solver ignores its signal", async () => {
  let started;
  const running = new Promise((resolve) => {
    started = resolve;
  });
  let finish;
  const late = new Promise((resolve) => {
    finish = resolve;
  });
  const server = createCadicalServer({
    solver: {
      solve: async () => {
        started();
        return await late;
      },
    },
  });
  await new Promise((resolve) => server.listen(0, "127.0.0.1", resolve));
  const address = server.address();
  const controller = new AbortController();
  const pending = new HttpSatSolver(`http://127.0.0.1:${address.port}/`).solve(
    request,
    controller.signal,
  );
  await running;
  controller.abort();
  await assert.rejects(pending, /abort/i);
  await new Promise((resolve) => setTimeout(resolve, 10));
  finish({ kind: "sat", model: [1n] });
  await new Promise((resolve, reject) =>
    server.close((error) => (error ? reject(error) : resolve())),
  );
});
