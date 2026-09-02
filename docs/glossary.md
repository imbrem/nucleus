# Glossary

**Checked**
: Validated by the kernel rather than accepted from a caller.

**Content address**
: A digest that identifies exact bytes. It does not by itself say that the
bytes are a valid proof, theory, or other object. Nucleus currently uses the
BLAKE3 family:

- **Regular BLAKE3** is unkeyed: the same bytes always have the same digest.
  This is the mode used for ordinary content addresses.
- **Keyed BLAKE3** hashes with a 32-byte key. It provides a separate keyed
  namespace and can authenticate identifiers when the key is secret.
- **Context BLAKE3** uses BLAKE3's derive-key mode with a public,
  human-readable context string. It provides domain separation: the same bytes
  intentionally receive different identifiers in different contexts. Nucleus
  can prederive and reuse the corresponding context key.

**HOL (higher-order logic)**
: The small ambient logic implemented by the kernel. Nucleus can define and
reason about other logics inside it.

**LCF style**
: An API in which theorem values cannot be forged by callers; they are produced
only by a small kernel from existing theorem values and checked inputs.

**Provenance**
: Information about where an artifact came from, such as a signer, tool,
source, or execution record. Provenance is separate from whether a theorem is
valid.

**Semantic envelope**
: The use of HOL to state and prove claims about another logic or computation
system. Such a proof need not execute its decision procedure or exhibit an
object-level derivation.

**TCB (trusted computing base)**
: The code and assumptions whose failure could make an invalid theorem appear
valid. Nucleus aims to keep this small and replaceable.

**Theorem handle**
: An opaque reference to a theorem established by a kernel. Possessing an
integer or serialized value that resembles a handle must not forge one.

**Wasm proof component**
: Untrusted proof-producing code compiled as a WebAssembly component. It may
call exposed kernel operations but cannot create theorems on its own.

**WIT (WebAssembly Interface Type)**
: The interface language used to describe capabilities available across a Wasm
component boundary.

**Compact row**
: An arena row that stands for a larger opcode-free term. Compact rows are
macros: a literal (`tm.nat`, `tm.int`, `tm.bytes`) or a builtin opcode
(`tm.op1.v1`, `tm.op2.v1`, `tm.num1.v1`, `tm.num2.v1`). They carry no meaning
of their own.

**Init slice**
: The checked, opcode-free prefix of definitions and theorems every kernel
starts from. Compact rows name constants in it.

**Lowering**
: Expanding a compact row into the opcode-free init definitions it stands for.
A compact row only has a meaning once it lowers, so the kernel rejects one
whose definition the init slice does not yet contain.
