---
title: Nucleus notes
status: active
issues: [564, 569]
reviewed: 2026-08-11
summary: Where evolving design, research, plans, and migration context live.
---

Nucleus is a minimal kernel foundation: a small trusted core that turns checked
transitions into theorems, with everything around it — serialization, storage,
imports, resolvers, proof search — treated as untrusted input. It is intended
eventually to host a rewritten [Covalence](https://github.com/imbrem/covalence),
but it is not required to preserve Covalence APIs or storage formats.

This directory is the project's durable long-form context. It is for material
that is too detailed or too provisional for the README, for agent instructions,
or for API documentation, but too valuable to leave in issue threads and chat
history.

## Documentation tiers

| Tier                      | Question it answers                         | Where it lives                   |
| ------------------------- | ------------------------------------------- | -------------------------------- |
| `README.md`               | What is this project, right now?            | Repository root                  |
| `AGENTS.md` / `CLAUDE.md` | How do I operate in this repository?        | Repository root                  |
| Rustdoc, Lean doc-gen     | What does this item mean?                   | Generated from source            |
| `notes/`                  | Why is it like this, and where is it going? | This directory                   |
| `apps/docs`               | How is all of the above presented?          | SvelteKit site deployed to Pages |

Notes are the only tier allowed to be exploratory. Everything else should
describe the repository as it is.

## Status vocabulary

Every note carries a `status` in its front matter, and the rendered site shows
it next to the title. Notes may be speculative; they may not be silently
speculative.

| Status       | Meaning                                                                |
| ------------ | ---------------------------------------------------------------------- |
| `research`   | Investigation and evidence. Describes something else, not Nucleus.     |
| `proposal`   | A suggested direction that has not been accepted.                      |
| `active`     | Describes the current intended design or state of the repository.      |
| `superseded` | Replaced by a later note, which the front matter or body should name.  |
| `historical` | Kept for context. Do not treat as a description of the current design. |

A note that says how something works must be `active` and must be true. A note
that says how something _could_ work is `proposal` or `research`, whatever its
level of detail. Do not present research sketches as implemented behaviour.

## Front matter

Notes begin with a `---` block. Only `title` and `status` are required; the
rest are used where they help.

```yaml
---
title: Storage foundations
status: proposal
issues: [528, 553]
reviewed: 2026-08-11
source-revision: ac1fcea2a0b0a75501af4a59dfb71790f3953ba7
summary: One line, shown in the site navigation.
---
```

- `title` — the heading the site and navigation use. Do not repeat it as an
  `#` heading in the body; the site renders it for you.
- `status` — one of the values above.
- `issues` — related issues or pull requests, as bare numbers or full URLs.
- `reviewed` — ISO date the note was last checked against the repository. Worth
  setting on anything that makes concrete claims about current code.
- `source-revision` — the external revision a note was researched against.
  Required in practice for imported or researched Covalence context, so a
  reader can tell what was actually inspected.
- `summary` — one line for the navigation tree.

The parser accepts a deliberately small subset of YAML: `key: value` scalars,
flow sequences (`[564, 569]`), and block sequences. Front matter that needs
more structure than that is a sign the structure belongs in the body.

## Organisation

What exists today:

```text
notes/
  README.md          this file
  architecture/      how Nucleus is put together and where it currently stands
```

Directories are created when the first real document needs one, not in advance,
so this tree is short on purpose. The category names to reach for first, when a
note does not belong in `architecture/`:

- `plans/` — intended direction for a subsystem or workflow.
- `research/` — investigation of something outside this repository.
- `covalence/` — curated context from the previous system, expected from
  [#570](https://github.com/imbrem/nucleus/issues/570).

Placing a note is a judgement call with a simple tiebreak: ask what the note
describes. Something in this repository, as it is, goes in `architecture/`.
Something in this repository, as it might become, goes in `plans/`. Something
outside this repository goes in `research/` or `covalence/`.

A directory may contain a `README.md`; the site treats it as that section's
index page and links to it. A directory without one still appears in the
navigation as a grouping.

## Linking

Write links the way you would for GitHub: relative paths to real files.

- `[the pipeline](architecture/notes-pipeline.md)` — a link to another note. The
  site rewrites it to the note's URL.
- `[the runner](../tools/glu/src/runner.rs)` — a link to a repository file
  outside `notes/`. The site rewrites it to a GitHub link pinned to the commit
  the site was built from.
- `[#569](https://github.com/imbrem/nucleus/issues/569)` — issues are ordinary
  external links, though `issues:` front matter is usually the better place.

Both kinds are checked. A link to a note that does not exist, or to a heading
anchor that does not exist, fails the docs build and the corpus test. Links
that leave `notes/` are checked against the working tree by the test. This is
the whole reason to avoid hand-written index pages: the filesystem is the
hierarchy, and the checks keep it honest.

## Review

Notes drift; that is expected and is why status exists. When you touch a
subsystem and find a note that no longer matches it:

- if the note is still broadly right, correct it and bump `reviewed`;
- if it has been overtaken, set its status to `superseded` or `historical` and
  say what replaced it, rather than deleting the history;
- if it was aspirational and the aspiration is now implemented, move the claim
  into the README or the API documentation and leave the note as the rationale.

Current Nucleus code and issues are authoritative. When a note disagrees with
the code, the code wins and the note is wrong.

## Reading this corpus

Notes are not loaded by default. Root agent guidance links into this directory
selectively, and each note is meant to be readable on its own. Start from
[the current status note](architecture/current-status.md) for where the
repository actually is, and from
[the notes pipeline](architecture/notes-pipeline.md) for how this directory
reaches the published site.
