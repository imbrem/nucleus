# Spike notes

A spike is an exploratory design built off the trunk so alternatives can be
compared before the real design is committed to. Spikes stay **open and
unmerged** on purpose — see `AGENTS.md` §2.

**The spike is the experiment. The note is the result.** A spike with no note is
the only kind that has actually gone to waste.

## Writing one

One file per spike or per family of related spikes, named for the design rather
than the branch: `hol-kernel-rust.md`, not `codex-hol-kernel-stack-2.md`.
Several attempts at the same component belong in one file, so they can be read
against each other.

Cover, in whatever order suits:

- **What was tried** — the design in a paragraph, and the PRs or branches it lives on.
- **What it got right** — the parts worth carrying forward, specifically.
- **Where it fought the grain** — the friction. This is the most valuable part
  and the one most often skipped. *Especially* API friction: an interface that
  reviewed fine and was unwieldy to write against is exactly the finding these
  spikes exist to surface.
- **What it implies for the real design** — the recommendation, stated plainly.

Do not write a changelog. Nobody will read a list of commits. Write the two or
three sentences you would say to someone about to make the same decision.

## Open questions this repository is spiking on

- **HOL kernel in Rust** — what the theorem handle is (`Rc`, arena index,
  session-scoped id), how private the constructors need to be, how much the
  checker recomputes versus caches. Spiked at least twice; a third is planned.
- **Proposition tables** — physical schema, source qualification, trust and
  deletion policy, and where the SAT/LRAT boundary sits.
- **HOL variants in Lean** — monomorphic locally nameless versus
  signature-parametric with kinded type variables; intrinsic versus checked
  syntax; tree versus arena representation.
- **JSON and CBOR profiles** — which subset is canonical, and what
  content-addressing does to it.
