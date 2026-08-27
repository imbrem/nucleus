# S3 CAS backend

This crate stores whole objects at `cas/{lowercase-blake3}`. It uses the AWS
SDK with configurable endpoint, signing region, credentials, and path-style
addressing, so the same code can target AWS S3, Cloudflare R2, Backblaze B2,
or a local S3-compatible server.

The ordinary test suite uses a loopback HTTP mock and requires no credentials.
Real-provider conformance is explicit and ignored by default:

```sh
NUCLEUS_S3_PROVIDER=AWS \
NUCLEUS_S3_AWS_BUCKET=example-bucket \
cargo test -p covalence-data-cas-s3 --test provider -- --ignored
```

AWS can use its standard region and credential provider chains. For another
provider, set the selected prefix's `ENDPOINT`, `REGION`, `ACCESS_KEY_ID`, and
`SECRET_ACCESS_KEY`; set `PATH_STYLE=1` if required. For example, selecting
`R2` reads `NUCLEUS_S3_R2_ENDPOINT`, `NUCLEUS_S3_R2_BUCKET`, and the analogous
R2-prefixed variables. The test never prints credential values.

The conformance test uploads one stable, harmless fixture and validates both
raw and checked lookup. Persistent test buckets retain that content-addressed
object; rerunning the test overwrites the same key.
