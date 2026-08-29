# CAS HTTP API

This crate exposes the transport-neutral `covalence_data_cas::CasService`
over HTTP and implements that same service for a remote HTTP endpoint. An HTTP
CAS can therefore be wrapped by another HTTP server without proxy-specific
code. Neither side is trusted: complete bytes must still be hashed before they
introduce a `CasFact`.

## Version-zero routes

All request and response bodies containing object data are
`application/octet-stream`.

| Method          | Path                 | Meaning                                                             |
| --------------- | -------------------- | ------------------------------------------------------------------- |
| `POST` or `PUT` | `/cas/upload`        | Stream bytes into the CAS and compute their BLAKE3 address.         |
| `PUT`           | `/cas/blake3/{hash}` | Stream bytes into the CAS only if they match `{hash}`.              |
| `GET` or `HEAD` | `/cas/blake3/{hash}` | Read the complete object, its length, or standard HTTP byte ranges. |
| `GET` or `HEAD` | `/cas/{hash}`        | Compatibility alias for the BLAKE3 route.                           |

`PUT /cas/upload` is idempotent in CAS terms: repeating a body admits the same
address. `POST` is also accepted because it is the conventional HTTP method
when the server computes the resource URI. `PUT /cas/blake3/{hash}` has the
strongest HTTP semantics because the request URI names the resource itself.

A successful upload returns `201 Created` for `/cas/upload` or `200 OK` for a
verified PUT, a canonical `Location`, and JSON of this shape:

```json
{
  "algorithm": "blake3",
  "hash": "<64 lowercase hexadecimal digits>",
  "bytes": 123,
  "index": 7
}
```

`index` is omitted when the provider does not expose a stable local index. It
is metadata, not part of the content address.

Range requests follow HTTP byte-range semantics. One satisfiable range returns
`206 Partial Content` with `Content-Range`; several ranges return standard
`multipart/byteranges` parts in request order. The transport bounds upload and
response sizes independently. A service implementation may stream to native
multipart storage while the body arrives; buffering is not part of the service
contract.

A `GET` or `HEAD` whose BLAKE3 hash segment is an unambiguous hexadecimal
prefix redirects with `307 Temporary Redirect` to the full canonical hash.
Prefix resolution is snapshot-relative because a mutable CAS can later gain a
colliding address, so redirects carry `Cache-Control: no-store`.
Prefixes currently require at least eight hexadecimal digits. Missing and
ambiguous prefixes are distinct outcomes. An ambiguous response may include a
bounded list of refining prefixes plus two independent backend claims: whether
the refinements cover every match, and whether every refinement covers at
least one match. These hints are only as trustworthy as the backend. Providers
may omit them or report prefix lookup as unsupported when enumeration would be
inefficient or contrary to policy. Verified `PUT` always requires the complete
hash.

Unknown algorithm routes such as `/cas/sha256/{hash}` return a structured
`501 Not Implemented` error. Malformed hashes, absent objects, hash mismatches,
unsatisfiable ranges, provider failures, and size limits have distinct status
codes and JSON error identifiers.

This is currently a network capability with no authentication layer. A host
must bind and expose it according to its own policy.
