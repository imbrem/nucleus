import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";

interface Package {
  id: string;
  name: string;
  version: string;
}

interface Edge {
  source: string;
  target: string;
}

interface Dependencies {
  packages: Package[];
  edges: Edge[];
}

interface Crates {
  crates: Package[];
  edges: Edge[];
}

function generated<T>(workspace: "production" | "glu", name: string): T {
  return JSON.parse(
    readFileSync(
      new URL(`../../buck/cargo/${workspace}/${name}`, import.meta.url),
      "utf8",
    ),
  ) as T;
}

test("generated graph projections use stable and resolvable identities", () => {
  const crates = generated<Crates>("production", "crates.json");
  const dependencies = generated<Dependencies>(
    "production",
    "dependencies.json",
  );
  const crateIds = new Set(crates.crates.map(({ id }) => id));
  const dependencyIds = new Set(dependencies.packages.map(({ id }) => id));

  assert.equal(crateIds.size, crates.crates.length);
  assert.equal(dependencyIds.size, dependencies.packages.length);
  assert.ok([...crateIds].every((id) => id.startsWith("workspace#")));
  assert.ok(
    dependencies.edges.every(
      ({ source, target }) =>
        dependencyIds.has(source) && dependencyIds.has(target),
    ),
  );
  assert.ok(
    crates.edges.every(
      ({ source, target }) => crateIds.has(source) && crateIds.has(target),
    ),
  );
});

test("multiple versions are retained as separate package identities", () => {
  const dependencies = generated<Dependencies>("glu", "dependencies.json");
  const versions = dependencies.packages
    .filter(({ name }) => name === "syn")
    .map(({ version }) => version);

  assert.deepEqual(versions, ["2.0.119", "3.0.3"]);
});
