import assert from "node:assert/strict";
import test from "node:test";
import {
  navigation,
  nodeCategoryLabels,
  snapshotCopy,
  staticNaturalDemo,
} from "./src/lib/site-content.ts";

test("static walkthrough pins the frozen natural artifact", () => {
  assert.equal(staticNaturalDemo.artifact.rows, 1_331);
  assert.equal(staticNaturalDemo.artifact.bytes, 32_666);
  assert.equal(staticNaturalDemo.artifact.algorithm, "BLAKE3");
  assert.equal(
    staticNaturalDemo.artifact.address,
    "08b577109951887e8acca5a3039d7e0d1a324f1b0aad02da120993bceff18953",
  );
  assert.equal(staticNaturalDemo.theorem.name, "nat.one_plus_one");
  assert.match(staticNaturalDemo.introduction, /does not run/i);
});

test("site navigation exposes the static walkthrough", () => {
  assert.ok(navigation.some(({ href }) => href === "/demo/"));
  assert.equal(nodeCategoryLabels["tcb-direct"], "Direct TCB dependency");
  assert.match(snapshotCopy.tcbNote, /covalence-nucleus-core/);
});
