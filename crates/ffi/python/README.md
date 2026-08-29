# covalence

Python bindings for Covalence.

## Layout

The package is a mixed one: hand-written Python in `python/covalence`, and the
compiled extension module staged beside it as `covalence._covalence`. The
compiled module is private; ordinary Python modules such as `covalence.lib.hash`
name the public surface. This keeps that surface independent of the Rust module
and leaves room for composition modules: `covalence.cas` combines the
checked logic objects and userspace providers, while a later
`covalence.nucleus` can do the same for the full stack.

There is one extension module for the whole project, not one per Rust crate.
`crates/ffi/python` is where Covalence crates are composed into a Python API;
the crates being wrapped never depend on it.

## What is exposed

`covalence-lib-hash`: the fixed-width namespaces and the operations on them.
Each namespace is its own class deriving from `Obj` — `O256`, `Blake3`,
`Sha256`, `ContextKey`, `Sha1`, `GitHash` — so `isinstance(value, Obj)` asks
the general question while two namespaces with matching bytes still compare
unequal.

```python
>>> import covalence
>>> from covalence.lib.hash import O256, COV_ROOT, git_blob
>>> covalence.lib.hash is not None
True
>>> O256.hash(b"abc")
O256.from_hex('6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85')
>>> COV_ROOT.tag(b"sexpr").tag(b"list")     # derive a child name
O256.from_hex('...')
>>> str(git_blob(b""))
'e69de29bb2d1d6434b8b29ae775ad8c2e48c5391'
```

Everything is a thin wrapper: hashing, encoding, and derivation are implemented
once, in the crate being wrapped. Malformed input raises `InvalidLengthError`,
`InvalidHexError`, or `InvalidBase64Error` — all `ValueError` — and anything
that is not bytes-like raises `TypeError`.

`covalence.data.cbor.Cbor` exposes the immutable shared CBOR data model. Its
constructors keep representation-sensitive values explicit: arrays and ordered
map entries return tuples, simple values retain their numeric code, and floats
retain their original width and raw bits. Python integers are converted to the
shared arbitrary-precision Rust `Int` without narrowing. Equality works
directly against Python integers, booleans, `None`, bytes, strings, lists, and
insertion-ordered dictionaries; no conversion call is required.
The `Cbor(value)` constructor (also available as `Cbor.from_python(value)`)
recursively converts those scalar types, lists, and dictionaries.

`covalence.data.sexpr` exposes the reusable owned S-expression reader. It can
stream `open`, `atom`, and `close` events or fold those events into immutable
`Document` and `SExpr` objects. Symbols, strings, byte strings, exact number
spellings, keywords, and directives remain distinct. The reader and both AST
directions are iterative and impose no arbitrary nesting limit. Parsed trees
retain `u64` byte spans; `erase()` produces the distinct `ErasedDocument` and
`ErasedSExpr` types, whose nodes carry no source-position fields.
`SExpr.format()` and `Document.format()` choose flat or indented layouts from a
requested width while retaining atom kinds and binary values.

```python
>>> from covalence.data.cbor import Cbor
>>> value = Cbor.array([Cbor.integer(2**256), Cbor.text("large")])
>>> value.kind
'array'
>>> value.value[0].value == 2**256
True
```

`covalence.cas` exposes the whole-object CAS LCF boundary. `CasAssertion` is
ordinary unchecked data; `check()` hashes the complete blob in Rust before it
can return the opaque `CasFact`. Stores are userspace policy. `IndexCas` assigns
stable integer IDs, while `get_checked()` checks bytes returned by any
duck-typed Python CAS. A provider with `get_fact()` may avoid rehashing, but the
fact's address is still compared with the request.

```python
>>> from covalence.cas import CasAssertion
>>> from covalence.lib.hash import O256
>>> blob = b"provided by Python"
>>> address = O256.hash(blob)
>>> fact = CasAssertion(address, blob).check()
>>> fact.hash == address and fact.blob == blob
True
```

`covalence.logic.hol` exposes the one-based Ethane arena in two layers.
`Arena` is mutable wire data and may contain unchecked rows. `Kernel` starts
empty and can only grow through checked row and syntactic-fact rules. Both
layers retain the low-level integer-index API. A kernel can additionally
return opaque `Kind`, `Ty`, and `Tm` handles, while `SynFact` snapshots prevent
evidence from being reused after its slot is overwritten or across kernels.

```python
>>> from covalence.logic.hol import Kernel
>>> kernel = Kernel()
>>> star = kernel.star()
>>> bool_ty = kernel.bool_ty(star)
>>> truth = kernel.bool(bool_ty, True)
>>> kernel.tm(truth).reference == truth
True
```

`Prover` instantiates a portable WASM component implementing the
`nucleus:proof/proof` world once and may be called repeatedly. A prover-local
name may be text, bytes-like data, an `O256`, a nonnegative integer, or `None`;
`None`, an omitted name, and `ZERO_O256` all request the conventional default.
Each call may extend a supplied `Kernel`; omitting it creates a fresh one. The
component source may itself be bytes or an `O256`. Address-based loading
requires a CAS, and the same optional CAS is wired into later component calls.
The explicit entry points are `prove_addr`, `prove_name`, `prove_ix`, and
`prove_bytes`; `prove` dispatches among them from the Python value's type.
`load_proof` is the one-shot convenience which builds a `Prover` and requests
its default on a fresh kernel. Components receive no inherited filesystem,
network, environment, or command-line capabilities.

```python
>>> from covalence.logic.hol import Prover, load_proof
>>> from covalence.lib.hash import ZERO_O256
>>> with open("proof.wasm", "rb") as source:
...     prover = Prover(source.read())
>>> kernel = prover.prove()
>>> prover.prove(None).address == prover.prove(ZERO_O256).address
True
>>> len(kernel) >= 0
True
```

The checked-in dictionary-backed provider is runnable directly:

```sh
glu python crates/ffi/python/examples/dict_cas.py
```

It deliberately stores raw bytes in a plain Python `dict` and performs the
check only when resolving. Files, HTTP, SQLite, generated data, or any other
Python logic can use the same protocol without becoming part of the trusted
constructor boundary.

| Path                | Contents                                       |
| ------------------- | ---------------------------------------------- |
| `src/`              | The `#[pymodule]` and its bindings             |
| `python/covalence/` | The importable package, `py.typed`, and `.pyi` |
| `examples/`         | checked-in runnable API demonstrations         |
| `tests/`            | pytest suite, run against the staged package   |

## Building and running

```sh
glu build python   # stage the package into target/python
glu python         # a REPL that can import covalence
glu python -c 'import covalence; print(covalence.__version__)'
glu test           # among other things, runs the pytest suite
```

`glu build python` compiles the extension and stages the importable package
into `target/python`, outside the source tree so that a build output never
lands in a directory Buck globs as a source. `glu python` runs whichever
`python3` is on `PATH` with that directory on `PYTHONPATH`.

Cargo compiles this crate rather than Buck's Rust rules; `//:python` is the
`genrule` that wraps it. `rust_library` produces an rlib, so no Rust rule here
can emit something an interpreter loads, and `pyo3`'s build script needs
`links` metadata Buck's prelude discards.

## Installing into an environment

`glu` stages the package rather than installing it, so nothing in CI needs a
packaging tool. To get Covalence into an environment of your own, use maturin:

```sh
python3 -m venv --system-site-packages .venv
. .venv/bin/activate
maturin develop -m crates/ffi/python/Cargo.toml   # editable install
maturin build   -m crates/ffi/python/Cargo.toml   # wheel into target/wheels
```

`--system-site-packages` keeps the pinned interpreter's packages — pytest, and
whatever the test suite grows to need — visible inside the virtual
environment, which is then the place for anything nixpkgs does not carry.
Because `glu` uses the `python3` on `PATH`, an activated environment is picked
up without further configuration.

## Supported Python

3.11 and later, on the stable ABI. PyO3 is built with `abi3-py311`, so one
extension module loads into every interpreter in that range and a wheel does
not have to be rebuilt per version. Widening the range means relaxing that
feature in `covalence-lib-python`, which is also where the PyO3 version and the
`extension-module` policy are pinned and explained.

Wheels are built for whatever platform maturin is run on; there is no
cross-platform release process yet.
