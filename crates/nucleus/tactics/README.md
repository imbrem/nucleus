# Nucleus tactics

`covalence-nucleus-tactics` contains untrusted, replaceable proof programs over
the checked HOL API. A tactic may choose the wrong strategy or fail, but it can
only return theorem slots created by kernel-checked rules.

Multi-step tactics stage work on a kernel fork and commit only on success. This
keeps failure atomic and makes the same coarse operations suitable for Rust,
Python, and portable Wasm clients without promoting tactic policy into the TCB.
