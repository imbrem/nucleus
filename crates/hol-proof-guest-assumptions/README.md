# HOL assumptions proof guest

This untrusted no-WASI component emits the bounded recipe for the checked
`{p} |- true` assumptions and equality-composition demonstration. It receives
only opaque recipe-builder handles; the native kernel independently replays,
persists, exports, and signs the resulting HOL database.
