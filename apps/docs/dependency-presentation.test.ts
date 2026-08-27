import assert from "node:assert/strict";
import test from "node:test";
import {
  dependencyInventory,
  dependencyNodes,
} from "./src/lib/dependency-presentation.ts";
import type { DependenciesData } from "./src/lib/repository-model.ts";

const data: DependenciesData = {
  packages: [
    { id: "direct", name: "alpha", version: "2", checksum: "" },
    { id: "indirect", name: "beta", version: "1", checksum: "" },
    { id: "other-2", name: "other", version: "2", checksum: "" },
    { id: "other-1", name: "other", version: "1", checksum: "" },
  ],
  roots: [{ category: "tcb", dependencies: ["direct"] }],
  edges: [{ source: "direct", target: "indirect", kinds: ["normal"] }],
};

test("dependency presentation consistently classifies TCB reachability", () => {
  assert.deepEqual(
    dependencyNodes(data).map(({ id, category }) => [id, category]),
    [
      ["direct", "tcb-direct"],
      ["indirect", "tcb-indirect"],
      ["other-2", "external"],
      ["other-1", "external"],
    ],
  );
});

test("dependency inventory sorts names and versions", () => {
  assert.deepEqual(
    dependencyInventory(data).map(({ name, versions }) => [
      name,
      versions.map(({ version }) => version),
    ]),
    [
      ["alpha", ["2"]],
      ["beta", ["1"]],
      ["other", ["1", "2"]],
    ],
  );
});
