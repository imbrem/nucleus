# HOL script frontend

`covalence-logic-hol-script` is an untrusted, userspace S-expression frontend
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

## Small source language

The initial grammar deliberately covers definitions rather than proofs:

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

For example, [`theories/init.sexpr`](theories/init.sexpr) defines the open
universal property `IsCoprod`, the induction predicate used to carve naturals
from infinity, and the graph/specification of primitive recursion. None of those
forms asserts its body.

## Modules and namespaces

`compile_module` adds a deliberately small module layer without adding kernel
authority or changing the arena encoding:

```scheme
(import prelude
  !(ASNFZ4mrze8BI0VniavN7wEjRWeJq83vASNFZ4mrze8=)
  !(EjRWeJq83vASNFZ4mrze8BI0VniavN7wEjRWeJq83vA=))

(namespace example
  (define truth () bool true)
  (namespace laws
    (define truth-again () bool truth)))
```

The two import addresses identify the dependency's kernel arena and its
separate namespace metadata. Imports are declarations only in this first
version: resolution and friendly-name-to-address policy remain caller-owned,
and adding or changing an import cannot change the compiled kernel.
Addresses use `!(...)`, containing exactly 32 bytes as canonical padded
standard Base64. This is a distinct `O256` atom kind rather than a symbol.

Nested definitions have dot-qualified identities (`example.truth`,
`example.laws.truth-again`). Unqualified references search the current
namespace and then its parents; names containing a dot start at the module
root. The returned `Namespace` is a tree of local names to `Ref` values. It is
navigation metadata and can be freely edited or discarded.

`delaborate_module` is the intentionally basic inverse view. It prints the
kernel address and row count, imports, namespace tree, and `%n` for every
anonymous local row. It is an audit view rather than a claim to recover the
proof program which produced an arena: elaboration discards macro choices,
binder spellings, and sharing decisions. A later expression delaborator can
replace `(anonymous %n)` with Scheme forms while retaining `%n` as the stable
fallback for rows it does not know how to raise.

This split leaves room for Scheme-defined derived forms such as `ind`, with
Rust or Wasm accelerators implementing the same userspace expansion protocol.
Neither a macro nor an accelerator can mint theorem facts; expanded work still
passes through the existing public `Kernel` operations.

## Standard init path

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
