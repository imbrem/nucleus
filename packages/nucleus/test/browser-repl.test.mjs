import assert from "node:assert/strict";
import test from "node:test";
import { withPage } from "./browser-harness.mjs";

test("manages independent connections in the interactive browser REPL", () =>
  withPage(async (page, origin) => {
    await page.goto(`${origin}/repl.html`);
    await page.getByText("connection 1 ready").waitFor();
    await page.locator("#sql").fill("SELECT 42 AS answer");
    await page.locator("#run").click();
    await page.getByRole("cell", { name: "42" }).waitFor();
    assert.equal(await page.getByRole("columnheader").textContent(), "answer");

    await page.locator("#new").click();
    await page.locator("#connection").selectOption("2");
    await page.locator("#sql").fill("SELECT 84 AS independent");
    await page.locator("#run").click();
    await page.getByRole("cell", { name: "84" }).waitFor();
  }));
