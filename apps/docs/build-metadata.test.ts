import assert from "node:assert/strict";
import test from "node:test";
import { buildMetadata } from "./build-metadata.ts";

test("build metadata is complete", () => {
  process.env.BUILD_COMMIT = "a".repeat(40);
  process.env.BUILD_DIRTY = "false";
  const metadata = buildMetadata();

  assert.equal(metadata.commit, "a".repeat(40));
  assert.equal(metadata.dirty, false);
  assert.equal(new Date(metadata.builtAt).toISOString(), metadata.builtAt);
  assert.match(metadata.rust, /^(unknown|rustc )/);
  assert.match(metadata.glu, /^\d+\.\d+\.\d+$/);
  delete process.env.BUILD_COMMIT;
  delete process.env.BUILD_DIRTY;
});
