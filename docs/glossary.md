# Glossary

**Checked**
: Validated by the kernel rather than accepted from a caller.

**Content address**
: A digest that identifies exact bytes. It does not by itself say that the
bytes are a valid proof, theory, or other object.

**LCF style**
: An API in which theorem values cannot be forged by callers; they are produced
only by a small kernel from existing theorem values and checked inputs.

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
