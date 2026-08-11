import assert from "node:assert/strict";
import { existsSync, readdirSync, readFileSync } from "node:fs";
import test from "node:test";

import {
  NOTE_ROOT,
  buildCorpus,
  headingId,
  noteSlug,
  parseFrontMatter,
  renderNote,
} from "./note-corpus.ts";

const repository = new URL("../../", import.meta.url);

function markdown(directory: string): string[] {
  const entries = readdirSync(new URL(`${directory}/`, repository), {
    withFileTypes: true,
  });
  return entries.flatMap((entry) =>
    entry.isDirectory()
      ? markdown(`${directory}/${entry.name}`)
      : entry.name.endsWith(".md")
        ? [`${directory}/${entry.name}`]
        : [],
  );
}

function corpus() {
  const files = Object.fromEntries(
    markdown(NOTE_ROOT).map((path) => [
      path,
      readFileSync(new URL(path, repository), "utf8"),
    ]),
  );
  return buildCorpus(files);
}

// The corpus gate named in #569: malformed metadata and dead internal links
// fail here as well as in the docs build, so a note can be checked without
// building the site.
test("every note has valid metadata and resolvable internal links", () => {
  const notes = corpus();

  assert.ok(notes.notes.length > 1, "the corpus should contain notes");
  assert.deepEqual(
    notes.problems.map((problem) => `${problem.path}: ${problem.message}`),
    [],
  );
});

// Links leaving `notes/` are the half the site cannot check: rendering has no
// filesystem, so it rewrites them to pinned GitHub URLs unconditionally.
test("links out of the corpus name files that exist", () => {
  const missing = corpus()
    .repositoryLinks.filter(
      ({ target }) => !existsSync(new URL(target, repository)),
    )
    .map(({ path, target }) => `${path} -> ${target}`);

  assert.deepEqual(missing, []);
});

test("notes render with headings, code, tables, and rewritten links", () => {
  const notes = buildCorpus({
    "notes/README.md": [
      "---",
      "title: Index",
      "status: active",
      "---",
      "",
      "# A Heading",
      "",
      "See [the note](guides/one.md#detail) and [a crate](../crates/nucleus).",
      "",
      "| a | b |",
      "| - | - |",
      "| 1 | 2 |",
      "",
      "```rust",
      "let x = 1;",
      "```",
      "",
    ].join("\n"),
    "notes/guides/one.md": [
      "---",
      "title: One",
      "status: research",
      "issues: [569]",
      "---",
      "",
      "## Detail",
      "",
      "Back to [the index](../README.md).",
      "",
    ].join("\n"),
  });

  assert.deepEqual(notes.problems, []);
  const html = renderNote(notes, notes.bySlug.get("")!, {
    base: "/nucleus",
    revision: "b".repeat(40),
    repository: "imbrem/nucleus",
  });

  assert.match(html, /<h1 id="a-heading">A Heading<\/h1>/);
  assert.match(html, /href="\/nucleus\/notes\/guides\/one\/#detail"/);
  assert.match(
    html,
    new RegExp(
      `href="https://github.com/imbrem/nucleus/blob/${"b".repeat(40)}/crates/nucleus"`,
    ),
  );
  assert.match(html, /<table>[\s\S]*<th>a<\/th>/);
  assert.match(html, /<code class="language-rust">/);
});

test("broken note links and unknown statuses are reported", () => {
  const notes = buildCorpus({
    "notes/README.md": [
      "---",
      "title: Index",
      "status: draft",
      "---",
      "",
      "[gone](nowhere.md) and [no anchor](#missing).",
      "",
    ].join("\n"),
    "notes/loose.md": "no front matter here\n",
  });

  const messages = notes.problems.map((problem) => problem.message).join("\n");
  assert.match(messages, /`status` must be one of/);
  assert.match(messages, /front matter/);
  // The index failed metadata validation, so it never reached link checking;
  // that is the point of reporting both from one pass.
  assert.equal(notes.notes.length, 0);
});

test("front matter accepts flow and block sequences", () => {
  const flow = parseFrontMatter("---\nissues: [1, 2]\n---\nbody\n");
  assert.deepEqual(flow?.fields.get("issues"), ["1", "2"]);
  assert.equal(flow?.body, "body\n");

  const block = parseFrontMatter("---\nissues:\n  - 1\n  - 2\n---\n");
  assert.deepEqual(block?.fields.get("issues"), ["1", "2"]);

  assert.equal(parseFrontMatter("no front matter\n"), null);
});

test("slugs collapse index notes onto their directory", () => {
  assert.equal(noteSlug("notes/README.md"), "");
  assert.equal(noteSlug("notes/architecture/README.md"), "architecture");
  assert.equal(
    noteSlug("notes/architecture/current-status.md"),
    "architecture/current-status",
  );
});

test("heading anchors match GitHub and disambiguate repeats", () => {
  const seen = new Map<string, number>();
  assert.equal(
    headingId("What `glu` does, exactly", seen),
    "what-glu-does-exactly",
  );
  assert.equal(headingId("Status", seen), "status");
  assert.equal(headingId("Status", seen), "status-1");
});
