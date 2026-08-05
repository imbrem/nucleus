import assert from "node:assert/strict";
import test from "node:test";
import { withPage } from "./browser-harness.mjs";

test("downloads and attaches an immutable SQLite image in a Worker", () =>
  withPage(async (page, origin) => {
    await page.goto(`${origin}/test/browser.html`);
    await page.waitForFunction(
      () =>
        document.body.dataset.result !== undefined ||
        document.body.dataset.error !== undefined,
    );
    assert.equal(await page.locator("body").getAttribute("data-error"), null);
    const result = JSON.parse(
      await page.locator("body").getAttribute("data-result"),
    );
    assert.match(result.hash, /^[0-9a-f]{64}$/);
    assert.deepEqual(result.result, {
      kind: "rows",
      columns: ["name", "value"],
      rows: [
        [
          { kind: "text", value: "exact" },
          { kind: "integer", value: "9223372036854775807" },
        ],
      ],
    });
    assert.equal(result.readonly, true);
  }));
