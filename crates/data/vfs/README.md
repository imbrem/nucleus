# Virtual resource resolution

`covalence-data-vfs` is the small userspace boundary between logical resource
names and immutable bytes. It deliberately assigns no path, source-language,
database, or semantic meaning to either one.

Frontends, Wasm programs, database adapters, and content-addressed stores can
therefore share a resolver without depending on one another. A hash identifies
the returned bytes; any claim about what they mean still requires separate
checked evidence.
