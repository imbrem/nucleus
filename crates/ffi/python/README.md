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

`CasRangeFact` narrows that to a byte range, introduced by `CasFact.range`, by
`slice` and `fuse` on an existing one, or by checking a `RangeProof` while
holding none of the rest of the blob. An `end` of `None` runs to the end of the
blob, which is the stronger claim: such a fact also knows the blob's length.

Above those sits an equality calculus. A `BlobExpr` is syntax — a digest,
literal bytes, a run of zeros, a concatenation, or a slice — and `BlobEq` is the
claim that two of them denote the same byte string in every model of the CAS.
`BlobFact` is the checked form, built only by the rules and by the bridges to
and from `CasRangeFact`. Its observations are three-valued: `decide()`,
`len_bytes` and `eval()` answer `None` where the rules do not settle a question,
so an expression has `len_bytes` rather than `len()`. `left + right` is
concatenation and `blob[3:7]` is a slice, on a fact as well as an expression.

```python
>>> from covalence.cas import BlobEq, BlobExpr, BlobFact
>>> from covalence.lib.hash import O256
>>> joined = BlobExpr.bytes(b"ab") + BlobExpr.bytes(b"c")
>>> BlobEq(joined, BlobExpr.bytes(b"abc")).decide()
True
>>> BlobFact.check(BlobEq(joined, BlobExpr.bytes(b"abc")))[0:2].prop.rhs.eval()
b'ab'
>>> BlobExpr.blake3(O256.hash(b"unresolved")).len_bytes is None
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

`covalence.logic.alethe.solve_qf_uf` runs cvc5 with Alethe proof output enabled,
lowers the SMT and proof terms to checked Ethane row indices, and returns only
after the proof establishes the exact sequent `assertions |- false`. The solver
argv is fixed by the module rather than the caller: the problem goes on stdin,
`--proof-granularity=dsl-rewrite` is what keeps cvc5 from emitting `hole`
steps, and the run is bounded by `timeout` seconds. The result also retains the
problem, raw proof output, solver version, executable, and options as untrusted
provenance. `check_qf_uf` checks already captured cvc5 stdout without starting
a process. A refutation's indices address its own checked arena, which
`refutation.kernel()` returns; `theorem_in` and `assertions_in` reject a kernel
those indices do not address.

```python
>>> from covalence.logic.alethe import solve_qf_uf
>>> result = solve_qf_uf("""(set-logic QF_UF)
... (declare-const p Bool)
... (assert p)
... (assert (not p))
... (check-sat)
... """)
>>> result.refutation.theorem > 0
True
```

`Strategy` instantiates a portable WASM component implementing the
`nucleus:proof/proof` world once and may be called repeatedly. Its one portable
operation applies a numeric tactic with small byte arguments to an optional
checked `Kernel`; omitting the kernel lets the strategy choose its checked
starting point. `apply_tactic_name` encodes a UTF-8 name as tactic one, and
`prove_addr` encodes an address as tactic zero. The component source may itself
be bytes or an `O256`. Address-based loading requires a CAS, and the same
optional CAS is wired into later component calls.
`load_proof` is the one-shot convenience which builds a `Strategy` and requests
its default on a fresh kernel. Components receive no inherited filesystem,
network, environment, or command-line capabilities.

```python
>>> from covalence.logic.hol import Strategy, load_proof
>>> with open("proof.wasm", "rb") as source:
...     strategy = Strategy(source.read())
>>> kernel = strategy.apply_tactic(0)
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

### Installing a wheel from a particular commit

Alpha releases are the easiest way to try Covalence on a supported platform:

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install --pre covalence
```

Pin the selected alpha in a dependency file when reproducibility matters, for
example `covalence==0.1.0a1`. PyPI selects the compatible wheel and installs any
declared Python dependencies automatically. At present Covalence has no
third-party Python runtime dependencies.

Maintainers publish an immutable prerelease by tagging a green `main` commit
with a PEP 440 development or alpha version:

```sh
git tag -a covalence-v0.1.0.dev1 -m 'Covalence Python 0.1.0.dev1'
git push origin covalence-v0.1.0.dev1
# Once distribution plumbing is established, publish alphas in the same way:
git tag -a covalence-v0.1.0a1 -m 'Covalence Python 0.1.0a1'
git push origin covalence-v0.1.0a1
```

The **Publish Python prerelease** workflow validates the tag, builds and tests
the wheel through the ordinary wheel workflow, and publishes that exact
artifact with a PyPI provenance attestation. Publishing uses OIDC trusted
publishing; there is no repository token. The PyPI publisher is scoped to
project `covalence`, owner `imbrem`, repository `nucleus`, workflow
`publish-python.yml`, and GitHub environment `pypi`. PyPI versions and Git tags
are immutable: use a new development or alpha number rather than moving or
rebuilding a tag.

Successful `main` and pull-request runs of the **Python wheels** workflow build
an experimental snapshot for Linux x86-64. The wheel uses the CPython 3.11
stable ABI and the `manylinux_2_28_x86_64` platform tag: the same file supports
ordinary CPython 3.11 and later, but only on compatible Linux x86-64 systems.
Other operating systems, architectures, and free-threaded Python builds are not
currently produced.

Choose a commit, not merely the newest `main` run. In GitHub's web interface,
open **Actions**, select **Python wheels**, and select a successful run whose
commit is the one required. At the bottom of its summary, download
`covalence-linux-x86_64-<full-commit-SHA>`, unzip it, then verify and install it:

```sh
cd path/to/unzipped-artifact
sha256sum --check SHA256SUMS
WHEEL=$(find . -maxdepth 1 -type f \
  -name 'covalence-*-cp311-abi3-manylinux_2_28_x86_64.whl' -print -quit)
test -n "$WHEEL"
python3 -m venv .venv
. .venv/bin/activate
python -m pip install "$WHEEL"
python -c 'import covalence; print(covalence.__version__)'
```

Downloading an Actions artifact in the web interface generally requires a
GitHub login, including for a public repository. The GitHub CLI makes selection
by immutable source commit explicit. Substitute the required full commit SHA:

```sh
REPO=imbrem/nucleus
FULL_SHA=0123456789abcdef0123456789abcdef01234567
RUN_ID=$(gh run list --repo "$REPO" --workflow python-wheels.yml \
  --commit "$FULL_SHA" --status success --limit 1 \
  --json databaseId --jq '.[0].databaseId')
test -n "$RUN_ID"
gh run download "$RUN_ID" --repo "$REPO" \
  --name "covalence-linux-x86_64-$FULL_SHA" --dir wheels
sha256sum --check wheels/SHA256SUMS
WHEEL=$(find wheels -maxdepth 1 -type f \
  -name 'covalence-*-cp311-abi3-manylinux_2_28_x86_64.whl' -print -quit)
test -n "$WHEEL"
python3 -m venv .venv
. .venv/bin/activate
python -m pip install "$WHEEL"
python -c 'import covalence; print(covalence.__version__)'
```

Record the full commit SHA and the matching entry in `SHA256SUMS` when using a
snapshot as a dependency. `BUILD-METADATA.json` also records the source commit
and Actions run. Artifacts expire after 30 days, so retain the verified wheel
and checksum when reproducibility is needed for longer.

These snapshots are not releases, and Python API compatibility is not yet
guaranteed. A production consumer should ultimately depend on an immutable
package-index version or release asset with exact hashes rather than on a
finite-lived Actions artifact.
