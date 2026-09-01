# Nucleus Lexicons

Lexicon describes the portable shape of Nucleus leaf objects. Lexicon objects
are open, so the Nucleus strong validator additionally requires the matching
`$type` and rejects unknown fields. It also checks invariants Lexicon cannot
express: word-length divisibility, packed-word validity, root bounds, and the
intrusive allocator structure.

Classical arena `words` are concatenated big-endian `u64` values. Normal-form
objects use AT Protocol DRISL CBOR and a CIDv1 with the `dag-cbor` codec and a
SHA-256 multihash. BLAKE3-addressed CIDs are an explicit Nucleus extension, not
AT Protocol normal form.

See the AT Protocol [data model](https://atproto.com/specs/data-model) for
DRISL and CID rules, and the [Lexicon specification](https://atproto.com/specs/lexicon)
for the schema language.
