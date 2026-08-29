# Nucleus script frontend

`covalence-nucleus-script` is an untrusted, userspace S-expression frontend
for the checked HOL API. It is intentionally not part of the trusted computing
base.

The boundary is:

```text
source text
    │ parse, resolve names, infer/check annotations, choose a representation
    │ (all untrusted)
    ▼
public Kernel operations ──► checked arena
                             + external name → Ref dictionary
```

A frontend bug can reject a program or construct a different checked arena. It
cannot insert an unchecked definition, equality, substitution fact, or theorem.
The dictionary is navigation metadata: it can be changed or discarded without
changing what the arena proves. Consumers that need stable meaning should retain
a checked descriptor such as `CoproductSchema`, `NaturalsDecl`, or
`NaturalArithmeticDecl`, and may additionally pin the arena address.

## Virtual source trees

The example library under [`library/`](library/) is split into modules such as
`logic/defs.cov`, `data/coprod/defs.cov`, `data/prod/defs.cov`, and
`nat/defs.cov`. A module imports another by its dot-qualified path:

```lisp
(import logic.defs)
```

Imports are private by default. A module may publish an imported module as-is,
rename that submodule, or publish its definitions directly while keeping the
source module private:

```lisp
(export logic.defs)
(export (logic.defs core))
(include logic.defs)
```

[`library/logic.cov`](library/logic.cov) uses the third form, so clients import
`logic` and see names such as `logic.and` and `logic.and.comm`; the physical
`logic.defs` split is not part of that public namespace.

`compile_tree("nat.defs", resources)` passes the logical name to the resolver
unchanged, loads each transitive dependency once, and automatically places
every file under its name-derived namespace. A folder-backed resolver may use
the conventional `nat/defs.cov` location; a CAS-backed resolver may map the
same name to an indexed hash anywhere in storage. The compiler cannot tell the
difference. The resolver is the format-neutral `ResourceVfs` from
`covalence-data-vfs`, returning shared `Bytes` without depending on SQLite.
`covalence-data-sqlite` can adapt the same mount to SQLite's random-access VFS.
A tree may therefore carry `.cov` sources, `.wasm` tactics, binary constants,
and `.sqlite` tactic state without giving the parser filesystem authority or
inventing a format per tactic.

The compiled namespace is a separate immutable navigation object with direct
binding, child, and dotted-path access. Resident exports mount shared immutable
subtrees without enumerating them. Opaque foreign mounts retain only an O256;
ordinary lookup never loads them, while `resolve_with` accepts an explicit
resolver and the default resolver rejects every foreign access. It is shaped
for straightforward WIT and Python wrappers and remains disposable metadata
rather than kernel state.

A module may also declare a portable proof request without running it:

```lisp
(proof checked (wasm tactics/check.wasm))
(proof cached (wasm !0123...cdef) !4567...cdef)
```

The component is selected by an opaque VFS resource or an O256; the optional
final O256 is the prover-local request name and defaults to zero. `compile_tree`
returns these declarations as metadata. The Nucleus facade's
`run_script_proofs` resolves and instantiates them through the reusable proof
API. Address-backed components are checked against their requested hash, and
the same optional CAS is available to the running component. None of this adds
a theorem constructor or parser to the trusted kernel.

Library `defs.cov` modules describe abstract public theories rather than a
preferred construction. For example, `nat/defs.cov` publishes the natural
structure, recursion, and arithmetic specifications. A future
`nat/concrete.cov` can select witnesses from a model, while private construction
modules contain the infinity-subtype proof. The same convention allows a
future `real/defs.cov` to expose a small axiomatization while a Dedekind-cut
construction remains an implementation and consistency proof.

Only `.cov` resources are decoded as UTF-8. Exact source hashes and dependency
order remain userspace metadata; all combined definitions still pass through
the checked kernel API.

## Small source language

The initial term grammar deliberately covers definitions rather than an
object-language proof syntax:

```text
declaration := (define name ('type-parameter ...) term)
             | (define name ('type-parameter ...) type term)
type        := bool | 'type-parameter | (-> type type)
term        := true | false | name | (term term ...)
             | (lambda name type term) | (inst name type ...)
             | (not term) | (and term term) | (or term term)
             | (imp term term) | (= term term)
             | (exists name type term) | (forall name type term)
             | (ty.exists 'name term) | (ty.forall 'name term)
```

Type parameters are explicit free variables. They do not silently assert a
polymorphic theorem. `inst` recompiles an open definition under an explicit type
substitution, through ordinary checked construction.

For example, [`logical-schemata.sexpr`](logical-schemata.sexpr) defines the open
universal property `IsCoprod`, the induction predicate used to carve naturals
from infinity, and the graph/specification of primitive recursion. None of those
forms asserts its body.

## Standard init path

The standard init build is split into two small scripts:

- [`logical-init.sexpr`](logical-init.sexpr) invokes the checked-Boolean-v0
  accelerator. Its kernel hash is the existing canonical logical-prefix hash.
- [`natural-init.sexpr`](natural-init.sexpr) imports that logical kernel and
  its namespace metadata by typed `O256` atoms, then invokes the natural-v0
  userspace accelerator.

Accelerators are versioned elaborator entry points, not kernel capabilities.
The logical accelerator submits the canonical manifest through its checked
compiler. The natural accelerator compiles the source schemata and performs
the existing derived infinity, subtype, recursion, and arithmetic proof
orchestration through public checked operations.

Each build pins `(script hash, output-object hash, kernel hash)`. The output
object contains the kernel hash and a hash of canonical namespace/import
metadata. Keeping the kernel identity separate means names can evolve without
silently changing the logical artifact.

`compile_init_slice` performs the current userspace assembly:

1. Compile the opcode-free logical init definitions.
2. Compile the source schemata in equality-only mode.
3. Use checked infinity and subtype rules to construct `nat`, `zero`, and
   `succ`, then prove separation, injectivity, and induction.
4. Construct primitive recursion and prove its zero, successor, and uniqueness
   laws.
5. Define addition and multiplication, prove their exported laws, and prove the
   unary statement `1 + 1 = 2`.
6. Project the dependency closure into a deterministic, opcode-free
   `CheckedPrefix`, accompanied by external names and typed descriptors.

The present frozen prefix has 1,331 rows. Its address and the semantic roots for
the natural carrier, zero, successor, induction, successor injectivity, and
zero/successor separation are pinned by regression tests.

## Formal verification boundary

Lean does not formalize this parser or assume the compiler is correct. The
source-independent formal stack instead:

- specifies the arena wire decoder and checked resolution;
- lowers resolved closed Ethane expressions to intrinsic HOL terms;
- gives deterministic semantics to those terms;
- decodes the three canonical Peano laws; and
- turns exact checked declaration and theorem rows into a `CNatModel`.

The remaining mechanical bridge is to materialize those resolution and lowering
witnesses for the frozen prefix. It should consume the canonical arena artifact
and exact references, never source syntax or the userspace dictionary.

## Representation policy

`LogicEncoding::EqualityOnly` emits only the raw logical definitions and is the
canonical init-slice mode. `LogicEncoding::Compact` emits checked logical macro
rows for tactic-oriented work. The kernel's lowering rules relate compact rows
to the same opcode-free definitions; selecting either encoding is an untrusted
frontend policy, not a new axiom.
