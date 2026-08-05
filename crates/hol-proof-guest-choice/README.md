# HOL choice proof guest

This untrusted no-WASI component emits the bounded recipe for
`|- (lambda x. x) (epsilon (lambda x. x))`. It receives only opaque
recipe-builder handles; the native kernel independently replays, persists,
exports, and signs the resulting HOL database.
