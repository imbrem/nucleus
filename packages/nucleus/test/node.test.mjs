import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import test from "node:test";
import init, {
  ClassicalKernel,
  Cnf,
  Dnf,
  HolProver,
  Refutation,
  Repl,
} from "../generated/nucleus.js";

async function load() {
  await init({
    module_or_path: await readFile(
      new URL("../generated/nucleus_bg.wasm", import.meta.url),
    ),
  });
}

const fixture = () => readFile(new URL("./fixture.sqlite", import.meta.url));

test("classical HOL uses native i32 JavaScript values", async () => {
  await load();
  const prover = new HolProver();
  const p = prover.proposition("1");
  const q = prover.proposition("2");
  const theorem = prover.identity(p);

  assert.equal(typeof p, "number");
  assert.equal(typeof theorem, "number");
  assert.equal(HolProver.complement(HolProver.complement(p)), p);
  prover.weaken(theorem, Int32Array.of(q), Int32Array.of(-q));
  const view = JSON.parse(prover.theoremJson(theorem));
  assert.ok(view.premises.flat().every(Number.isSafeInteger));
  assert.ok(view.conclusions.flat().every(Number.isSafeInteger));
  assert.throws(() => HolProver.complement(0));
  assert.throws(() => prover.identity(0));
});

test("generated HOL declarations contain no string or BigInt IDs", async () => {
  const declarations = await readFile(
    new URL("../generated/nucleus.d.ts", import.meta.url),
    "utf8",
  );
  const hol = declarations.match(
    /export class HolProver \{(?<body>[\s\S]*?)\n\}/,
  )?.groups?.body;
  assert.ok(hol, "HolProver declaration is generated");
  assert.doesNotMatch(hol, /\b(?:bigint|BigInt64Array)\b/);
  assert.doesNotMatch(
    hol,
    /(?:identity|cut|resolve|copyTheorem)\([^\n]*: string/,
  );
  assert.match(hol, /identity\(proposition: number\): number/);
  assert.match(
    hol,
    /weaken\(theorem: number, premises: Int32Array, conclusions: Int32Array\): void/,
  );
});

test("WASM replays text and binary LRAT over text and binary DIMACS", async () => {
  await load();
  const textCnf = Cnf.fromDimacs(
    new TextEncoder().encode("p cnf 1 2\n1 0\n-1 0\n"),
  );
  const binaryCnf = Cnf.fromBinaryDimacs(Uint8Array.of(2, 0, 3, 0));
  assert.equal(textCnf.rowsJson(), binaryCnf.rowsJson());

  const text = Refutation.fromTextLrat(textCnf, "3 0 1 2 0\n");
  const binary = Refutation.fromBinaryLrat(
    binaryCnf,
    Uint8Array.of("a".charCodeAt(0), 6, 0, 2, 4, 0),
  );
  assert.equal(text.cnfJson(), binary.cnfJson());
  const kernel = new ClassicalKernel();
  const theorem = kernel.copyRefutation(text);
  assert.deepEqual(JSON.parse(kernel.theoremJson(theorem)), [[[1], [-1]], []]);
});

test("WASM matrices normalize only on demand", async () => {
  await load();
  const cnf = new Cnf("[[2,1,2],[2,1,2]]");
  const dnf = new Dnf("[[-1,-2,-1]]");
  assert.equal(cnf.rowsJson(), "[[2,1,2],[2,1,2]]");
  cnf.normalize();
  dnf.normalize();
  assert.equal(cnf.rowsJson(), "[[1,2]]");
  assert.equal(dnf.rowsJson(), "[[-2,-1]]");
});

/** Evaluates a form and returns its printed value, asserting it was one. */
function value(repl, text) {
  const step = repl.eval(text);
  assert.equal(step.kind, "output", `${text} -> ${step.kind}`);
  return step.text;
}

test("the browser REPL evaluates the same forms as the CLI", async () => {
  await load();
  const repl = new Repl();

  // A named list, not a sentence about a store -- and not a bare tuple whose
  // fields you have to remember the order of.
  assert.equal(value(repl, "(stats)"), "((objects 0) (bytes 0) (largest 0))");
  assert.equal(value(repl, "(objects)"), "()");
  assert.equal(value(repl, "(kernels)"), '((0 "local" #t))');
  assert.match(value(repl, "(help)"), /\(connect "URL"\)/);
});

test("a file picker admits, and the store then reports it", async () => {
  await load();
  const repl = new Repl();
  const database = await fixture();

  const address = repl.admit(database);
  assert.match(address, /^[0-9a-f]{64}$/);

  assert.deepEqual(repl.addresses(), [address]);
  assert.equal(value(repl, "(objects)"), `(${address})`);
  assert.equal(JSON.parse(repl.stats()).objects, 1);
});

test("(put …) says what a page cannot do rather than failing obscurely", async () => {
  await load();
  const repl = new Repl();
  assert.match(value(repl, '(put "/tmp/x.sqlite")'), /no filesystem here/);
});

test("kernels can be connected to and switched between", async () => {
  await load();
  const repl = new Repl();

  assert.equal(value(repl, '(connect "http://127.0.0.1:8080")'), "1");
  assert.equal(
    value(repl, "(kernels)"),
    '((0 "local" #f) (1 "http://127.0.0.1:8080" #t))',
  );
  assert.equal(value(repl, "(local)"), "0");
  assert.equal(value(repl, "(kernel 1)"), "1");

  // A URL without a scheme is not a URL.
  assert.throws(() => repl.eval('(connect "127.0.0.1:8080")'));
  assert.throws(() => repl.eval("(kernel 7)"), /no kernel 7/);
});

test("fetching asks the host for the selected kernel's URL", async () => {
  await load();
  const repl = new Repl();
  const address = repl.admit(await fixture());

  // Local has nothing to fetch from.
  assert.throws(() => repl.eval(`(fetch ${address})`));

  value(repl, '(connect "http://127.0.0.1:8080")');
  const step = repl.eval(`(fetch ${address})`);
  assert.equal(step.kind, "fetch");
  assert.equal(step.text, `http://127.0.0.1:8080/cas/${address}`);
  assert.equal(step.address, address);
});

test("fetched bytes are verified against the address asked for", async () => {
  await load();
  const repl = new Repl();
  const database = await fixture();
  const address = repl.admit(database);
  value(repl, `(forget ${address})`);

  assert.equal(repl.admitVerified(address, database), address);

  value(repl, `(forget ${address})`);
  const tampered = Uint8Array.from(database);
  tampered[100] ^= 0xff;
  assert.throws(
    () => repl.admitVerified(address, tampered),
    /does not match its address/,
  );
  assert.deepEqual(repl.addresses(), []);
});

test("forgetting removes an address from the store", async () => {
  await load();
  const repl = new Repl();
  const address = repl.admit(await fixture());

  // #t and #f, because the question is whether it was there.
  assert.equal(value(repl, `(forget ${address})`), "#t");
  assert.equal(value(repl, "(objects)"), "()");
  assert.equal(value(repl, `(forget ${address})`), "#f");
});

test("an unbound name is refused", async () => {
  await load();
  const repl = new Repl();
  assert.throws(() => repl.eval("(nope)"), /unbound: nope/);
});

test("input that is not an s-expression is refused", async () => {
  await load();
  const repl = new Repl();
  assert.throws(() => repl.eval("(stats"), /unterminated/);
  assert.throws(() => repl.eval(")"), /unexpected \)/);
});

test("samples give an empty store something to query", async () => {
  await load();
  const repl = new Repl();

  // No fixture file and no fetch: SQLite builds them here.
  const listed = value(repl, "(samples)");
  assert.match(listed, /^\(\(planets [0-9a-f]{64}\) \(moons [0-9a-f]{64}\)\)$/);
  assert.equal(JSON.parse(repl.stats()).objects, 2);

  // Content-addressed, so asking twice is the same two objects.
  assert.equal(value(repl, "(samples)"), listed);
  assert.equal(JSON.parse(repl.stats()).objects, 2);
});

test("objects is bounded and stats says how much there is", async () => {
  await load();
  const repl = new Repl();
  value(repl, "(samples)");

  assert.equal(value(repl, "(objects 1)").split(" ").length, 1);
  assert.equal(value(repl, "(objects)").split(" ").length, 2);
  assert.match(value(repl, "(stats)"), /\(objects 2\)/);
});

test("quit is quit", async () => {
  await load();
  const repl = new Repl();
  assert.equal(repl.eval("(quit)").kind, "quit");
});
