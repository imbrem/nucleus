# Nucleus facade

`covalence-nucleus` makes its authority boundary visible in its module tree:

- the `core/` subcrate is the auditable assembly point for checked HOL and CAS
  authority and is re-exported as `covalence_nucleus::core`;
- the `script/` subcrate is an untrusted userspace frontend, namespace index,
  delaborator, and init accelerator layer, re-exported as
  `covalence_nucleus::script`;

The crate root re-exports the existing core facade for compatibility, but the
definitions of those exports live in the `core` subcrate. Parsing a script, choosing an
accelerator, attaching names, or checking a pinned hash grants no theorem
authority. Only operations exported through the checked kernels create facts.

The standard scripts in [`script/`](script/) pin three separate
identities: the exact source bytes, the complete output object (kernel address
plus external metadata address), and the kernel arena alone. These regression
checks are useful evidence about the untrusted build without making the
compiler trusted.
