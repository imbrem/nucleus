import assert from "node:assert/strict";
import test from "node:test";
import { smoke } from "../component/nucleus.js";

// The same export `glu ci` invokes under wasmtime, reached instead through the
// component's transpiled JavaScript. This route goes through WIT rather than
// wasm-bindgen, so it is not restricted to wasm32-unknown-unknown; the
// wasm-bindgen path in the sibling tests is unaffected by it.
test("loads the transpiled component in Node", () => {
  assert.equal(smoke(), 42);
});
