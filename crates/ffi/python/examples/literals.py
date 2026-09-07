"""Run with `glu python crates/ffi/python/examples/literals.py`."""

from covalence.logic.literals import Context, Type

ctx = Context()
module_header = ctx.bytes(b"\x00asm\x01\x00\x00\x00")
version = module_header.read_word(4, Type.I32)
assert version.evaluate().value == 1

answer = (ctx.i32(20) + ctx.i32(22)).evaluate()
assert answer.value == 42
assert ctx.kernel.theorem(answer.theorem)[0] == []

# Python integers are mathematical Int, with no machine-width narrowing.
assert (ctx(2**256) + 1).evaluate().value == 2**256 + 1
assert ctx(-1).to_word(Type.I8, wrap=True).evaluate().value == 255

# Builtins are ordinary typed function terms and can be partially applied.
add = ctx.builtin_function("i32.add")
increment = add(ctx.i32(1))
assert increment(ctx.i32(41)).evaluate().value == 42

# Construction works with unknowns; evaluation requires a closed expression.
x = ctx.variable(1, Type.I32)
claim = (x + ctx.i32(0)) == x
assert claim.type is Type.BOOL
