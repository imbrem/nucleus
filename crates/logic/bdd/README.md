# covalence-logic-bdd

Userspace binary decision diagrams for Covalence.

The crate keeps two representations distinct:

- `Diagram` is general shared decision syntax. It may be unordered, contain
  redundant branches, and repeat variables.
- `Bdd` is a reduced ordered canonical handle owned by a `Manager`. Variables
  are ordered by their positive numeric identifier.

`Manager::reduce` converts general syntax to a canonical BDD, and
`Manager::to_diagram` converts back to shared syntax. Canonical BDDs support
Boolean operations, conditionals, existential quantification, evaluation, and
CNF conversion.

CNF export uses a linear-size Tseitin encoding rather than enumerating paths.
It returns a `CnfEncoding` containing both the formula and the complete ordered
list of fresh variables. Existentially quantifying those variables recovers the
original Boolean function.

This crate is an optimization and interoperability tool. It is not part of the
trusted computing base.
