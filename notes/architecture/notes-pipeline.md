---
title: The notes pipeline
status: active
issues: [569]
reviewed: 2026-08-11
summary: How Markdown under notes/ becomes pages on the Nucleus Pages site.
---

`notes/` is plain Markdown in the repository, and the deployed site renders it
under `/notes/`. Both statements have to stay true at once: the corpus is
useful because it is readable on GitHub in a pull request diff, and it is
discoverable because it is published. This note describes the machinery that
holds those together.

## Where the pieces are

| File                                                                           | Responsibility                                               |
| ------------------------------------------------------------------------------ | ------------------------------------------------------------ |
| [`apps/docs/note-corpus.ts`](../../apps/docs/note-corpus.ts)                   | Parsing, validation, link resolution, and Markdown rendering |
| [`apps/docs/src/lib/server/notes.ts`](../../apps/docs/src/lib/server/notes.ts) | Reads the corpus at build time and adapts it for the site    |
| [`apps/docs/src/routes/notes`](../../apps/docs/src/routes/notes)               | One prerendered route covering every note                    |
| [`apps/docs/note-corpus.test.ts`](../../apps/docs/note-corpus.test.ts)         | The narrow check that runs without building the site         |
| [`BUCK`](../../BUCK)                                                           | Declares `notes/**/*.md` as an input to the `docs` artifact  |

`note-corpus.ts` deliberately imports neither SvelteKit nor `node:fs`. The site
hands it the results of `import.meta.glob`; the test hands it files read from
disk. Both therefore see exactly the same corpus, which is the only reason the
test is worth trusting as a gate.

## How a note becomes a page

Vite reads every `notes/**/*.md` at build time. `buildCorpus` parses each file's
front matter, records its heading anchors, resolves its links, and derives the
navigation tree from the paths themselves — there is no second copy of the
hierarchy to maintain. `notes/README.md` becomes `/notes/`, a directory's
`README.md` becomes that directory's page, and everything else becomes
`/notes/<directory>/<name>/`.

Rendering happens in `$lib/server`, so `marked` and the Markdown source stay out
of the client bundle: pages are prerendered and the browser receives HTML.
Routes come from an `entries()` generator over the corpus, so adding a Markdown
file is the only step needed to publish it.

Links are rewritten during rendering rather than being written twice:

- a link to another note becomes that note's site URL, with `base` applied so
  it survives the `BASE_PATH` used for Pages deployments;
- a link to a repository file outside `notes/` becomes a GitHub link pinned to
  the commit the site was built from, falling back to `main` for dirty or
  unknown builds;
- absolute URLs and bare anchors are left alone.

Each page also carries a source link back to its own path at that revision, and
shows `status`, `reviewed`, `source-revision`, and related issues above the
body.

## What fails the build

Broken internal links are the failure mode this corpus is most prone to, since
notes are moved and renamed far more often than code. Two gates catch them.

`buildCorpus` reports problems, and `$lib/server/notes.ts` throws when there are
any, so `glu docs` fails rather than deploying a page with dead links. It
rejects missing or malformed front matter, a `status` outside the documented
vocabulary, a `reviewed` field that is not an ISO date, a link to a note that
does not exist, and a link to a heading anchor that does not exist in the note
it names.

`apps/docs/note-corpus.test.ts` reports the same problems from `pnpm test`,
without a site build, and additionally resolves every link that leaves `notes/`
against the working tree — the site cannot check those, since it has no
filesystem access at render time.

## Choices worth knowing about

**`marked`, not a framework.** The corpus needs GitHub-flavoured Markdown
rendered to HTML at build time and nothing else. mdsvex and its relatives
compile Markdown into Svelte components, which would let notes carry custom
components — exactly the property that would stop them being readable as plain
Markdown on GitHub. `marked` is a single dependency of the docs app, reached
through the pnpm workspace like every other JavaScript dependency, and it does
not appear in the Rust dependency graph or the trusted computing base.

**Front matter parsed, not YAML-parsed.** The convention in
[the corpus README](../README.md#front-matter) is a handful of scalar keys and
occasional lists. A YAML dependency would buy nothing; front matter that
outgrows the subset is a signal that the structure belongs in the body.

**One deployment.** Notes are emitted into the same `apps/docs/build` artifact
that already carries the crate and dependency graphs, Rustdoc, and Lean
documentation. There is no second Pages workflow, and there should not be one:
GitHub Pages allows a single deployment per repository, which is why the Lean
documentation already ships inside the site rather than beside it.

**No CMS.** Notes are files. The navigation comes from the filesystem, statuses
come from front matter, and the checks are a test and a build failure. If this
ever needs a database, something has gone wrong with the scope.

## Working on notes locally

```console
$ glu docs           # build the site into apps/docs/build
$ glu docs serve     # build, then serve it on 127.0.0.1:4173
```

For the narrow loop, `pnpm --filter @nucleus/docs test` runs the corpus checks
alone, and `pnpm --filter @nucleus/docs build` builds the site without Buck.
