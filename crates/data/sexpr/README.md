# S-expressions

`covalence-data-sexpr` provides an owned, logic-independent S-expression data
model. It is userspace syntax: parsing an expression grants no kernel
authority.

Documents contain zero or more proper-list expressions. Whitespace and `;`
line comments are trivia. Atoms are symbols, decoded strings, bytes, numbers,
keywords, and directives:

```lisp
(symbol "decoded\nstring" 123exact :keyword #directive
  b"printable\x00bytes")
```

A bare atom beginning with an ASCII digit is a number; its spelling is retained
verbatim. `:name` and `#name` are keywords and directives, with the sigil kept
out of the in-memory name. Empty names are rejected.

Bytes use `b"..."`. Printable ASCII may appear directly; `\\`, `\"`, `\n`,
`\r`, `\t`, `\0`, and exact two-digit `\xHH` escapes cover every byte.
Non-ASCII source characters and unescaped control bytes are rejected. In memory
byte atoms use `bytes::Bytes`, making slices and clones cheap.

The reader emits `Open`, `Atom`, and `Close` events without recursion or a
nesting limit. Building an AST from events and traversing an AST back into
events are also iterative. Resource limits belong to callers.

`Printer` renders the same event traversal through a width-aware Wadler-style
document. Lists stay flat when they fit and break with two-space indentation
by default. Printing validates externally constructed atom spellings so that
parsing the result retains every atom kind.
