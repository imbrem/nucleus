# Alethe proof component

This untrusted component parses solver output and drives the default
`nucleus:proof/alethe` checked-rule interface. The reusable command model,
strict parser, and native replay API live in `covalence-logic-alethe`; this
crate contains only component ABI and CAS/request glue.

The initial fixture is cvc5 QF_UF output. Unknown commands, attributes, sorts,
and rules are rejected. Solver identity, version, options, problem bytes,
proof bytes, and component identity are provenance, not proof authority.

`tests/fixtures/cvc5-qf-uflia` records one cvc5 QF_UFLIA proof, including its
`anchor`/`subproof` frames and rational literals. It is read-only evidence for
the frontend that lowers that fragment: `covalence-logic-alethe` reads it into
checked rows but proves nothing about it, because no HOL theory in this tree
states integer or rational arithmetic. The component ABI exposes only the
`QF_UF` refutation path.
