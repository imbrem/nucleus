//! Minimal checked operations over Ethane arena rows.
//!
//! The arena is the only syntax representation. The kernel accepts and
//! returns plain local references, validates their tags and classifiers on
//! every call, and records classifiers and equality classes in arena-level
//! dense columns. Concrete resolvers, caches, ergonomic typed objects, and
//! indexes over the union-find belong in userspace.

use std::{collections::BTreeMap, convert::Infallible, ops::Deref};

use covalence_lib_error::snafu::Snafu;
use smallvec::SmallVec;

use crate::{
    AmbPred, Arena, EqColumn, Import, ImportId, Link, Ref, ResolveError, Resolver, Sort, SynFactId,
    Tag,
    builtin::{Op1, Op2},
    init::Compiled,
    row::{Expr as Node, Row},
};

mod choice;
mod classical;
mod infinity;
mod logic;
mod subtype;
mod syn_facts;

pub use classical::{
    AbsThm, AntisymmThm, ApTerm, ApThm, ChoiceThm, ForallThm, ReflThm, TyForallThm,
};
pub use covalence_logic_classical::{
    CheckedArena, ClassicalArena, ClassicalKernel, ClassicalRules, Cnf, CnfId, Dnf, DnfId, Lit,
    LitError, LitVec, Refutation, ThmId, ThmRef,
};
pub use infinity::{AX_INF, INFINITY_BINDER_COUNT, InfinityAxiom, InfinityBinder};
pub use subtype::{AX_SUB, BINDER_COUNT, Binder, SubtypeAxiom};

/// A recoverable failure at the checked kernel boundary.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum KernelError<E = Infallible>
where
    E: std::error::Error + 'static,
{
    /// The dense definition index no longer fits in `Ref`.
    #[snafu(display("kernel has too many definitions"))]
    TooManyDefinitions,
    /// The import index no longer fits in `ImportId`.
    #[snafu(display("kernel has too many imports"))]
    TooManyImports,
    /// The ambient predicate index no longer fits in `Lit`.
    #[snafu(display("kernel has too many ambient predicates"))]
    TooManyAmbientPredicates,
    /// The syntactic-fact slot space no longer fits in `SynFactId`.
    #[snafu(display("kernel has too many syntactic facts"))]
    TooManySynFacts,
    /// The theorem slot space no longer fits in `ThmId`.
    #[snafu(display("kernel has too many theorem slots"))]
    TooManyTheorems,
    /// A theorem index is absent or has been removed.
    #[snafu(display("theorem {id:?} is absent"))]
    MissingTheorem {
        /// Missing one-based theorem slot.
        id: ThmId,
    },
    /// A checked sequent rule does not match its evidence.
    #[snafu(display("theorem evidence does not establish {rule}"))]
    InvalidTheoremRule {
        /// Name of the rejected rule.
        rule: &'static str,
    },
    /// A reference does not name a local row.
    #[snafu(display("reference {reference:?} does not name a kernel row"))]
    MissingDefinition {
        /// Missing local reference.
        reference: Ref,
    },
    /// A syntactic-fact slot is absent or has been removed.
    #[snafu(display("syntactic fact {id:?} is absent"))]
    MissingSynFact {
        /// Missing one-based fact slot.
        id: SynFactId,
    },
    /// Syntactic-fact evidence does not match the requested local rule.
    #[snafu(display("syntactic fact evidence does not establish {rule}"))]
    InvalidSynFact {
        /// Name of the rejected local rule.
        rule: &'static str,
    },
    /// A row belongs to another syntactic category.
    #[snafu(display("reference {reference:?} declares {actual:?}, but {expected:?} was required"))]
    WrongCategory {
        /// Reference being inspected.
        reference: Ref,
        /// Required category.
        expected: Sort,
        /// Category declared by the row tag.
        actual: Sort,
    },
    /// A type or term row has no classifier.
    #[snafu(display("reference {reference:?} has no sort member"))]
    MissingSort {
        /// Unclassified reference.
        reference: Ref,
    },
    /// A reachable syntax dependency is cyclic.
    #[snafu(display("syntax dependency cycle contains reference {reference:?}"))]
    CyclicSyntax {
        /// A member of the rejected cycle.
        reference: Ref,
    },
    /// A foreign proxy cannot be detached from its import.
    #[snafu(display("reference {reference:?} is an imported proxy"))]
    ImportedProxy {
        /// Proxy row encountered while traversing the copied syntax.
        reference: Ref,
    },
    /// Kernels do not share the same deterministic initialization prefix.
    #[snafu(display("kernel init prefixes do not match"))]
    InitPrefixMismatch,
    /// A constructor requires a particular row form.
    #[snafu(display("reference {reference:?} has tag {actual:?}, but {expected} was required"))]
    WrongForm {
        /// Reference being inspected.
        reference: Ref,
        /// Required constructor form.
        expected: &'static str,
        /// Actual row tag.
        actual: Tag,
    },
    /// Two classifiers are not members of the same equality class.
    #[snafu(display("classifier {actual:?} is not equal to expected {expected:?}"))]
    ClassifierMismatch {
        /// Required classifier.
        expected: Ref,
        /// Supplied classifier.
        actual: Ref,
    },
    /// A rule needed an axiom capability the arena does not carry.
    #[snafu(display("rule requires the {name} axiom capability, which the arena does not carry"))]
    MissingAxiom {
        /// The capability the rule needed.
        name: &'static str,
    },
    /// A derived construction ran out of free variable names.
    #[snafu(display("no free variable names remain above the terms in use"))]
    TooManyNames,
    /// The requested axiom capability is unavailable in Ethane.
    #[snafu(display("unsupported axiom capability {name}"))]
    UnsupportedAxiom {
        /// Requested capability name.
        name: String,
    },
    /// Import resolution failed.
    #[snafu(transparent)]
    Resolve {
        /// Checked resolver failure.
        source: ResolveError<E>,
    },
}

/// The complete source-to-destination correspondence from a term copy.
///
/// The map includes copied roots, ordinary syntax children, and classifiers.
/// It owns no references to either kernel.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CopyMap {
    nodes: BTreeMap<Ref, Ref>,
    roots: Vec<Ref>,
}

/// A checked compact alias for one opcode-free logical syntax tree.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LogicalAlias {
    /// Original opcode-free root.
    pub raw: Ref,
    /// Rebuilt root using compact logical opcodes where recognized.
    pub compact: Ref,
    /// Direct syntactic fact `raw = compact`.
    pub fact: SynFactId,
}

/// A checked opcode-free expansion of one compact logical syntax tree.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LogicalExpansion {
    /// Original root, which may contain logical opcodes.
    pub compact: Ref,
    /// Recursively expanded opcode-free root.
    pub raw: Ref,
    /// Direct syntactic fact `compact = raw`.
    pub fact: SynFactId,
}

/// An immutable arena snapshot known to have been assembled by a kernel.
///
/// A prefix carries no source manifest or naming authority. It is simply the
/// exact checked state from which compatible kernels can be forked while
/// retaining numerical identity for every resident reference.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CheckedPrefix {
    arena: Arena,
}

impl CheckedPrefix {
    /// Borrows the exact checked arena snapshot.
    #[must_use]
    pub const fn arena(&self) -> &Arena {
        &self.arena
    }

    /// Returns the exact content address of the frozen arena.
    #[must_use]
    pub fn addr(&self) -> crate::O256 {
        self.arena.addr()
    }

    /// Returns the number of resident definition rows in the prefix.
    #[must_use]
    pub fn len(&self) -> usize {
        self.arena.len()
    }

    /// Returns whether the prefix contains no definition rows.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.arena.is_empty()
    }

    /// Creates a kernel whose complete initial state is this prefix.
    #[must_use]
    pub fn kernel(&self) -> Kernel {
        Kernel::with_init_prefix(self.arena.clone())
    }
}

impl CopyMap {
    /// Returns the destination reference corresponding to `source`.
    #[must_use]
    pub fn get(&self, source: Ref) -> Option<Ref> {
        self.nodes.get(&source).copied()
    }

    /// Returns copied roots in the same order, including repetitions.
    #[must_use]
    pub fn roots(&self) -> &[Ref] {
        &self.roots
    }

    /// Iterates over every copied source row and its destination row.
    #[must_use]
    pub fn iter(&self) -> impl ExactSizeIterator<Item = (Ref, Ref)> + '_ {
        self.nodes
            .iter()
            .map(|(&source, &destination)| (source, destination))
    }

    /// Returns the number of distinct copied rows.
    #[must_use]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Returns whether no rows were copied.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
}

/// An Ethane arena assembled only through checked row operations.
///
/// `Kernel` is non-generic and stores no resolver. Imported rows accept an
/// untrusted mutable resolver only for the call which introduces their local
/// proxy.
#[derive(Debug, Default)]
pub struct Kernel {
    arena: Arena,
    init_prefix: Option<(crate::O256, usize)>,
}

struct ConvPath {
    root: Ref,
    classifier: Option<Ref>,
    members: SmallVec<[Ref; 8]>,
}

impl Deref for Kernel {
    type Target = Arena;

    fn deref(&self) -> &Self::Target {
        &self.arena
    }
}

impl Kernel {
    /// Creates the empty checked kernel.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            arena: Arena::empty(),
            init_prefix: None,
        }
    }

    /// Creates a checked kernel whose exact prefix is the compiled init table.
    #[must_use]
    pub fn with_init(init: &Compiled) -> Self {
        Self {
            arena: init.arena().clone(),
            init_prefix: Some((init.arena().addr(), init.arena().len())),
        }
    }

    /// Creates a checked kernel whose first rows are a compiled init prefix.
    pub(crate) fn with_init_prefix(arena: Arena) -> Self {
        let init_prefix = Some((arena.addr(), arena.len()));
        Self { arena, init_prefix }
    }

    /// Returns the compiled init-prefix address and row count, when present.
    #[must_use]
    pub const fn init_prefix(&self) -> Option<(crate::O256, usize)> {
        self.init_prefix
    }

    /// Borrows the underlying raw arena.
    #[must_use]
    pub const fn arena(&self) -> &Arena {
        &self.arena
    }

    /// Forks the complete checked state for transactional userspace work.
    ///
    /// The fork retains the exact init-prefix identity, definitions, proof
    /// rows, and caches. Mutating it has no effect on `self`; callers may
    /// replace the original only after a multi-step derived operation succeeds.
    #[must_use]
    pub fn fork(&self) -> Self {
        Self {
            arena: self.arena.clone(),
            init_prefix: self.init_prefix,
        }
    }

    /// Forgets checked construction and returns the raw arena.
    #[must_use]
    pub fn into_arena(self) -> Arena {
        self.arena
    }

    /// Freezes this checked state as an exact reusable kernel prefix.
    ///
    /// The operation adds no fact and performs no validation bypass: only a
    /// `Kernel`, whose state was assembled by checked operations, can create
    /// this handle. Forks retain all definitions, capabilities, contexts, and
    /// proof rows already present in the snapshot.
    #[must_use]
    pub fn into_checked_prefix(self) -> CheckedPrefix {
        CheckedPrefix { arena: self.arena }
    }

    /// Copies one reachable term DAG from an independent kernel.
    ///
    /// The copy preserves sharing, introduces no import, and retains no
    /// borrow of `source`. Equality, context, proof metadata, and syntactic
    /// facts are deliberately not copied. References in a matching compiled
    /// init prefix are identities and are never appended.
    ///
    /// # Errors
    ///
    /// Returns an error if the root is not a term or its reachable syntax is
    /// missing, cyclic, imported, or fails checked kinding or typing, or if
    /// the kernels have different init prefixes. The destination is unchanged
    /// on error.
    pub fn copy_term_from(&mut self, source: &Self, root: Ref) -> Result<CopyMap, KernelError> {
        self.copy_terms_from(source, &[root])
    }

    /// Copies one reachable term DAG while expanding every logical opcode.
    ///
    /// The source and destination must share `init` as their exact compiled
    /// prefix. Compact logical rows are replaced by checked applications of
    /// the corresponding opcode-free definitions; all other rows are copied
    /// as in [`copy_term_from`](Self::copy_term_from).
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as
    /// [`copy_terms_lowered_from`](Self::copy_terms_lowered_from).
    pub fn copy_term_lowered_from(
        &mut self,
        init: &Compiled,
        source: &Self,
        root: Ref,
    ) -> Result<CopyMap, KernelError> {
        self.copy_terms_lowered_from(init, source, &[root])
    }

    /// Copies one checked object of any syntactic category while recursively
    /// expanding logical opcodes in its reachable closure.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as
    /// [`copy_objects_lowered_from`](Self::copy_objects_lowered_from).
    pub fn copy_object_lowered_from(
        &mut self,
        init: &Compiled,
        source: &Self,
        root: Ref,
    ) -> Result<CopyMap, KernelError> {
        self.copy_objects_lowered_from(init, source, &[root])
    }

    /// Copies the union of several reachable term DAGs from another kernel.
    ///
    /// Roots retain their input order and repetitions, while every reachable
    /// source row is appended at most once. An empty root list is a no-op.
    /// No import row or provenance relationship is introduced.
    ///
    /// # Errors
    ///
    /// Returns an error if a root is not a term or reachable syntax is
    /// missing, cyclic, imported, or fails checked kinding or typing, or if
    /// the kernels have different init prefixes. All validation and capacity
    /// checks precede mutation, so failure is atomic.
    pub fn copy_terms_from(
        &mut self,
        source: &Self,
        roots: &[Ref],
    ) -> Result<CopyMap, KernelError> {
        if self.init_prefix != source.init_prefix {
            return Err(KernelError::InitPrefixMismatch);
        }
        for &root in roots {
            source.require_category::<Infallible>(root, Sort::Tm)?;
        }

        let (order, mut nodes) = source.copy_order(roots)?;

        let final_len = self
            .arena
            .len()
            .checked_add(order.len())
            .ok_or(KernelError::TooManyDefinitions)?;
        i32::try_from(final_len).map_err(|_| KernelError::TooManyDefinitions)?;

        for (offset, &source_ref) in order.iter().enumerate() {
            let value = self.arena.len() + offset + 1;
            let destination =
                Ref::new(i32::try_from(value).map_err(|_| KernelError::TooManyDefinitions)?)
                    .ok_or(KernelError::TooManyDefinitions)?;
            nodes.insert(source_ref, destination);
        }
        let mut staged = Self {
            arena: self.arena.clone(),
            init_prefix: self.init_prefix,
        };
        for &source_ref in &order {
            let row = source.row::<Infallible>(source_ref)?;
            let (copied, sort) = remap_row(row, source.sort(source_ref), &nodes);
            staged
                .arena
                .push_row(copied, sort)
                .ok_or(KernelError::TooManyDefinitions)?;
        }
        for &destination in nodes.values() {
            staged.validate_copy_row(destination)?;
        }
        let copied_roots = roots.iter().map(|root| nodes[root]).collect();
        self.arena = staged.arena;
        Ok(CopyMap {
            nodes,
            roots: copied_roots,
        })
    }

    /// Copies reachable term DAGs while recursively expanding logical opcodes.
    ///
    /// Expansion happens during the checked post-order copy, so opcodes nested
    /// under lambdas, applications, equality, choice, and type constructors do
    /// not survive in the destination closure. Shared source rows still map to
    /// one destination root, although a binary opcode expands to two ordinary
    /// application rows. The operation is transactional.
    ///
    /// # Errors
    ///
    /// Returns an error if `init` is not the exact shared compiled prefix, a
    /// root or reachable row is invalid or imported, a logical definition is
    /// absent, an expansion is ill-typed, or the destination reference space
    /// is exhausted. The destination is unchanged on error.
    pub fn copy_terms_lowered_from(
        &mut self,
        init: &Compiled,
        source: &Self,
        roots: &[Ref],
    ) -> Result<CopyMap, KernelError> {
        for &root in roots {
            source.require_category::<Infallible>(root, Sort::Tm)?;
        }
        self.copy_objects_lowered_from(init, source, roots)
    }

    /// Copies checked objects of any syntactic category while recursively
    /// expanding logical opcodes in their reachable closures.
    ///
    /// This is the representation-polymorphic form used by dictionary and
    /// init-slice projection: roots may be kinds, types, or terms, and retain
    /// their categories in the destination. Expansion affects only reachable
    /// term opcode rows. The operation is transactional.
    ///
    /// # Errors
    ///
    /// Returns an error if `init` is not the exact shared compiled prefix, a
    /// root or reachable row is absent, invalid, cyclic, or imported, a
    /// logical definition is absent, an expansion is ill-typed, or the
    /// destination reference space is exhausted. The destination is unchanged
    /// on error.
    pub fn copy_objects_lowered_from(
        &mut self,
        init: &Compiled,
        source: &Self,
        roots: &[Ref],
    ) -> Result<CopyMap, KernelError> {
        let expected_prefix = Some((init.arena().addr(), init.arena().len()));
        if self.init_prefix != expected_prefix || source.init_prefix != expected_prefix {
            return Err(KernelError::InitPrefixMismatch);
        }
        for &root in roots {
            source.category_as::<Infallible>(root)?;
        }

        let (order, mut nodes) = source.copy_order(roots)?;
        let mut staged = Self {
            arena: self.arena.clone(),
            init_prefix: self.init_prefix,
        };
        for &source_ref in &order {
            let syntax_root = source
                .find_path_in::<Infallible>(EqColumn::Syn, source_ref)?
                .0;
            if syntax_root != source_ref
                && let Some(&destination) = nodes.get(&syntax_root)
            {
                nodes.insert(source_ref, destination);
                continue;
            }
            let row = source.row::<Infallible>(source_ref)?;
            let destination = match *row.expr() {
                Node::Op1(op, operand) => {
                    let definition = init.get(op.name()).ok_or(KernelError::WrongForm {
                        reference: source_ref,
                        expected: "named logical init definition",
                        actual: row.tag(),
                    })?;
                    staged.app(definition, nodes[&operand])?
                }
                Node::Op2(op, left, right) => {
                    let definition = init.get(op.name()).ok_or(KernelError::WrongForm {
                        reference: source_ref,
                        expected: "named logical init definition",
                        actual: row.tag(),
                    })?;
                    let partial = staged.app(definition, nodes[&left])?;
                    staged.app(partial, nodes[&right])?
                }
                _ => {
                    let (copied, sort) = remap_row(row, source.sort(source_ref), &nodes);
                    staged
                        .arena
                        .push_row(copied, sort)
                        .ok_or(KernelError::TooManyDefinitions)?
                }
            };
            nodes.insert(source_ref, destination);
        }
        for &destination in nodes.values() {
            staged.validate_copy_row(destination)?;
        }
        let copied_roots = roots.iter().map(|root| nodes[root]).collect();
        self.arena = staged.arena;
        Ok(CopyMap {
            nodes,
            roots: copied_roots,
        })
    }

    /// Returns the syntactic category declared by a checked row.
    ///
    /// # Errors
    ///
    /// Returns an error if `reference` is absent.
    pub fn category(&self, reference: Ref) -> Result<Sort, KernelError> {
        self.category_as::<Infallible>(reference)
    }

    /// Returns the classifier recorded by a checked type or term row.
    ///
    /// # Errors
    ///
    /// Returns an error if `reference` is absent or has no classifier.
    pub fn classifier(&self, reference: Ref) -> Result<Ref, KernelError> {
        self.classifier_as::<Infallible>(reference)
    }

    /// Finds the canonical member of a row's equality class.
    ///
    /// An acyclic class is represented by its root. If raw input contains a
    /// cycle, the smallest member of that cycle is canonical. A cycle is not a
    /// logical error: every edge still asserts equality between its endpoints.
    ///
    /// # Errors
    ///
    /// Returns an error for a missing row or cross-category parent.
    pub fn find(&self, reference: Ref) -> Result<Ref, KernelError> {
        self.find_as::<Infallible>(reference)
    }

    /// Finds a canonical class member and compresses the traversed path.
    ///
    /// Cycles are normalized to a tree rooted at their smallest member.
    ///
    /// # Errors
    ///
    /// Returns an error for a missing row or cross-category parent.
    pub fn find_mut(&mut self, reference: Ref) -> Result<Ref, KernelError> {
        self.find_mut_as::<Infallible>(reference)
    }

    /// Compatibility name for immutable equality lookup.
    ///
    /// # Errors
    ///
    /// Returns an error for a missing row or cross-category parent.
    pub fn representative(&self, reference: Ref) -> Result<Ref, KernelError> {
        self.find(reference)
    }

    /// Tests membership in one row equality class.
    ///
    /// # Errors
    ///
    /// Returns an error if either reference or its parent chain is malformed.
    pub fn equivalent(&self, left: Ref, right: Ref) -> Result<bool, KernelError> {
        self.equivalent_as::<Infallible>(left, right)
    }

    /// Tests equality and compresses both traversed paths.
    ///
    /// # Errors
    ///
    /// Returns an error if either reference or parent chain is malformed.
    pub fn equivalent_mut(&mut self, left: Ref, right: Ref) -> Result<bool, KernelError> {
        self.equivalent_mut_as::<Infallible>(left, right)
    }

    /// Tests type equality using only the type-row union-find.
    ///
    /// # Errors
    ///
    /// Returns an error unless both references are checked type rows.
    pub fn ty_eq(&self, left: Ref, right: Ref) -> Result<bool, KernelError> {
        self.require_category::<Infallible>(left, Sort::Ty)?;
        self.require_category::<Infallible>(right, Sort::Ty)?;
        self.equivalent(left, right)
    }

    /// Tests type equality and compresses both type-row paths.
    ///
    /// # Errors
    ///
    /// Returns an error unless both references are checked type rows.
    pub fn ty_eq_mut(&mut self, left: Ref, right: Ref) -> Result<bool, KernelError> {
        self.require_category::<Infallible>(left, Sort::Ty)?;
        self.require_category::<Infallible>(right, Sort::Ty)?;
        self.equivalent_mut(left, right)
    }

    /// Tests term equality using only the term-row union-find.
    ///
    /// # Errors
    ///
    /// Returns an error unless both references are checked term rows.
    pub fn tm_eq(&self, left: Ref, right: Ref) -> Result<bool, KernelError> {
        self.require_category::<Infallible>(left, Sort::Tm)?;
        self.require_category::<Infallible>(right, Sort::Tm)?;
        self.equivalent(left, right)
    }

    /// Tests term equality and compresses both term-row paths.
    ///
    /// # Errors
    ///
    /// Returns an error unless both references are checked term rows.
    pub fn tm_eq_mut(&mut self, left: Ref, right: Ref) -> Result<bool, KernelError> {
        self.require_category::<Infallible>(left, Sort::Tm)?;
        self.require_category::<Infallible>(right, Sort::Tm)?;
        self.equivalent_mut(left, right)
    }

    /// Appends `kind.star`.
    ///
    /// # Errors
    ///
    /// Returns an error if the dense reference space is exhausted.
    pub fn star(&mut self) -> Result<Ref, KernelError> {
        self.push::<Infallible>(Row::new(Node::KindStar), None)
    }

    /// Appends a kind arrow.
    ///
    /// # Errors
    ///
    /// Returns an error unless both operands are local kind rows.
    pub fn kind_arr(&mut self, domain: Ref, codomain: Ref) -> Result<Ref, KernelError> {
        self.require_category::<Infallible>(domain, Sort::Kind)?;
        self.require_category::<Infallible>(codomain, Sort::Kind)?;
        self.push::<Infallible>(Row::new(Node::KindArr(domain, codomain)), None)
    }

    /// Appends the Boolean type.
    ///
    /// # Errors
    ///
    /// Returns an error unless `star` names `kind.star`.
    pub fn bool_ty(&mut self, star: Ref) -> Result<Ref, KernelError> {
        self.require_star::<Infallible>(star)?;
        self.push::<Infallible>(Row::new(Node::BoolTy), Some(star))
    }

    /// Appends a simple function type.
    ///
    /// # Errors
    ///
    /// Returns an error unless both operands are types of kind `star`.
    pub fn ty_arr(&mut self, domain: Ref, codomain: Ref) -> Result<Ref, KernelError> {
        let star = self.require_star_type::<Infallible>(domain)?;
        self.require_star_type::<Infallible>(codomain)?;
        self.push::<Infallible>(Row::new(Node::TyArr(domain, codomain)), Some(star))
    }

    /// Appends an intrinsically kinded free type variable.
    ///
    /// # Errors
    ///
    /// Returns an error unless `kind` is a local kind row.
    pub fn ty_fv(&mut self, name: u64, kind: Ref) -> Result<Ref, KernelError> {
        self.require_category::<Infallible>(kind, Sort::Kind)?;
        self.push::<Infallible>(Row::new(Node::TyFv { name, kind }), Some(kind))
    }

    /// Appends type-family application.
    ///
    /// Kinds are syntactic in Ethane, so the argument kind must be the exact
    /// domain reference of the function kind.
    ///
    /// # Errors
    ///
    /// Returns an error for non-type operands, a non-arrow function kind, or
    /// a kind mismatch.
    pub fn ty_app(&mut self, function: Ref, argument: Ref) -> Result<Ref, KernelError> {
        self.require_category::<Infallible>(function, Sort::Ty)?;
        self.require_category::<Infallible>(argument, Sort::Ty)?;
        let function_kind = self.classifier(function)?;
        let argument_kind = self.classifier(argument)?;
        let (domain, codomain) = self.kind_arrow::<Infallible>(function_kind)?;
        if argument_kind != domain {
            return Err(KernelError::ClassifierMismatch {
                expected: domain,
                actual: argument_kind,
            });
        }
        self.push::<Infallible>(Row::new(Node::TyApp(function, argument)), Some(codomain))
    }

    /// Appends a type-family abstraction and its arrow kind.
    ///
    /// # Errors
    ///
    /// Returns an error unless `binder` is a free type-variable row.
    pub fn ty_lam(&mut self, binder: Ref, body: Ref) -> Result<Ref, KernelError> {
        self.require_form::<Infallible>(binder, "ty.fv", |node| matches!(node, Node::TyFv { .. }))?;
        self.require_category::<Infallible>(body, Sort::Ty)?;
        let domain = self.classifier(binder)?;
        let codomain = self.classifier(body)?;
        let kind = self.push::<Infallible>(Row::new(Node::KindArr(domain, codomain)), None)?;
        self.push::<Infallible>(Row::new(Node::TyLam(binder, body)), Some(kind))
    }

    /// Appends a guarded model type.
    ///
    /// # Errors
    ///
    /// Returns an error unless `predicate` is a Boolean term.
    pub fn model(&mut self, name: u64, predicate: Ref) -> Result<Ref, KernelError> {
        let bool_ty = self.require_bool_term::<Infallible>(predicate)?;
        let star = self.classifier(bool_ty)?;
        self.require_star::<Infallible>(star)?;
        self.push::<Infallible>(Row::new(Node::Model { name, predicate }), Some(star))
    }

    /// Appends type-level existential quantification.
    ///
    /// # Errors
    ///
    /// Returns an error unless `predicate` is a Boolean term.
    pub fn ty_exists(&mut self, name: u64, predicate: Ref) -> Result<Ref, KernelError> {
        let bool_ty = self.require_bool_term::<Infallible>(predicate)?;
        self.push::<Infallible>(Row::new(Node::TyExists { name, predicate }), Some(bool_ty))
    }

    /// Appends type-level universal quantification.
    ///
    /// The dual of [`ty_exists`](Self::ty_exists), and identical in shape: the
    /// predicate is a Boolean term with the bound type variable free, and the
    /// result is the Boolean proposition that *every* type satisfies it.
    ///
    /// Universals are what characterise a type up to isomorphism — a
    /// coproduct's mediating map has to be unique for every target, and "every
    /// target" is this quantifier. An existential alone can say a type with
    /// some structure exists, never that it is *the* one.
    ///
    /// # Errors
    ///
    /// Returns an error unless `predicate` is a Boolean term.
    pub fn ty_forall(&mut self, name: u64, predicate: Ref) -> Result<Ref, KernelError> {
        let bool_ty = self.require_bool_term::<Infallible>(predicate)?;
        self.push::<Infallible>(Row::new(Node::TyForall { name, predicate }), Some(bool_ty))
    }

    /// Appends an intrinsically typed free term variable.
    ///
    /// # Errors
    ///
    /// Returns an error unless `ty` is a type of kind `star`.
    pub fn tm_fv(&mut self, name: u64, ty: Ref) -> Result<Ref, KernelError> {
        self.require_star_type::<Infallible>(ty)?;
        self.push::<Infallible>(Row::new(Node::TmFv { name, ty }), Some(ty))
    }

    /// Appends term application.
    ///
    /// The function type may be any member of an equality class containing a
    /// function type. Domain checking consults the same type union-find.
    ///
    /// # Errors
    ///
    /// Returns an error unless the function class contains an arrow and its
    /// domain is equal to the argument type.
    pub fn app(&mut self, function: Ref, argument: Ref) -> Result<Ref, KernelError> {
        self.require_category::<Infallible>(function, Sort::Tm)?;
        self.require_category::<Infallible>(argument, Sort::Tm)?;
        let function_ty = self.classifier(function)?;
        let argument_ty = self.classifier(argument)?;
        let (domain, codomain) = self.type_arrow_member::<Infallible>(function_ty)?;
        if !self.equivalent(domain, argument_ty)? {
            return Err(KernelError::ClassifierMismatch {
                expected: domain,
                actual: argument_ty,
            });
        }
        self.push::<Infallible>(Row::new(Node::App(function, argument)), Some(codomain))
    }

    /// Appends a term abstraction and its function type.
    ///
    /// # Errors
    ///
    /// Returns an error unless `binder` is a free term-variable row and both
    /// endpoint types have kind `star`.
    pub fn lam(&mut self, binder: Ref, body: Ref) -> Result<Ref, KernelError> {
        self.require_form::<Infallible>(binder, "tm.fv", |node| matches!(node, Node::TmFv { .. }))?;
        self.require_category::<Infallible>(body, Sort::Tm)?;
        let domain = self.classifier(binder)?;
        let codomain = self.classifier(body)?;
        let function_ty = self.ty_arr(domain, codomain)?;
        self.lam_at(function_ty, binder, body)
    }

    /// Appends a term abstraction at an existing function type.
    ///
    /// This avoids manufacturing a duplicate arrow row when a deterministic
    /// prefix already names the required function type.
    ///
    /// # Errors
    ///
    /// Returns an error unless `binder` is a free term-variable row and
    /// `function_ty` is an arrow whose endpoints equal the binder and body
    /// types.
    pub fn lam_at(&mut self, function_ty: Ref, binder: Ref, body: Ref) -> Result<Ref, KernelError> {
        self.require_form::<Infallible>(binder, "tm.fv", |node| matches!(node, Node::TmFv { .. }))?;
        self.require_category::<Infallible>(body, Sort::Tm)?;
        let (domain, codomain) = self.type_arrow_member::<Infallible>(function_ty)?;
        let binder_ty = self.classifier(binder)?;
        if !self.equivalent(domain, binder_ty)? {
            return Err(KernelError::ClassifierMismatch {
                expected: domain,
                actual: binder_ty,
            });
        }
        let body_ty = self.classifier(body)?;
        if !self.equivalent(codomain, body_ty)? {
            return Err(KernelError::ClassifierMismatch {
                expected: codomain,
                actual: body_ty,
            });
        }
        self.push::<Infallible>(Row::new(Node::Lam(binder, body)), Some(function_ty))
    }

    /// Appends a Boolean literal.
    ///
    /// # Errors
    ///
    /// Returns an error unless `bool_ty` names a Boolean type row.
    pub fn bool(&mut self, bool_ty: Ref, value: bool) -> Result<Ref, KernelError> {
        self.require_bool_type::<Infallible>(bool_ty)?;
        self.push::<Infallible>(Row::new(Node::Bool(value)), Some(bool_ty))
    }

    /// Appends a checked unary Boolean builtin.
    ///
    /// # Errors
    ///
    /// Returns an error unless the operand is a Boolean term.
    pub fn op1(&mut self, op: Op1, operand: Ref) -> Result<Ref, KernelError> {
        let bool_ty = self.require_bool_term::<Infallible>(operand)?;
        self.push::<Infallible>(Row::new(Node::Op1(op, operand)), Some(bool_ty))
    }

    /// Appends a checked binary Boolean builtin.
    ///
    /// # Errors
    ///
    /// Returns an error unless both operands are Boolean terms.
    pub fn op2(&mut self, op: Op2, left: Ref, right: Ref) -> Result<Ref, KernelError> {
        let bool_ty = self.require_bool_term::<Infallible>(left)?;
        let right_ty = self.require_bool_term::<Infallible>(right)?;
        if !self.equivalent(bool_ty, right_ty)? {
            return Err(KernelError::ClassifierMismatch {
                expected: bool_ty,
                actual: right_ty,
            });
        }
        self.push::<Infallible>(Row::new(Node::Op2(op, left, right)), Some(bool_ty))
    }

    /// Canonically lowers one compact logical row through its named init definition.
    ///
    /// The kernel must have been created with [`Kernel::with_init`], and `init`
    /// must be that same prefix. Lowering is ordinary checked application, so
    /// the resulting raw term is identical to direct construction from the
    /// authoritative opcode-free definition.
    ///
    /// # Errors
    ///
    /// Returns an error if `reference` is not an opcode row, the init prefix
    /// is absent/mismatched, or checked application rejects an operand.
    pub fn lower_logical(&mut self, init: &Compiled, reference: Ref) -> Result<Ref, KernelError> {
        if !self.arena.has_definition_prefix(init.arena()) {
            return Err(KernelError::InitPrefixMismatch);
        }
        let row = self.row::<Infallible>(reference)?;
        let actual = row.tag();
        let node = *row.expr();
        match node {
            Node::Op1(op, operand) => {
                let definition = init.get(op.name()).ok_or(KernelError::WrongForm {
                    reference,
                    expected: "named logical init definition",
                    actual,
                })?;
                self.app(definition, operand)
            }
            Node::Op2(op, left, right) => {
                let definition = init.get(op.name()).ok_or(KernelError::WrongForm {
                    reference,
                    expected: "named logical init definition",
                    actual,
                })?;
                let partial = self.app(definition, left)?;
                self.app(partial, right)
            }
            _ => Err(KernelError::WrongForm {
                reference,
                expected: "tm.op1.v1 or tm.op2.v1",
                actual,
            }),
        }
    }

    /// Recursively expands logical opcodes in one resident syntax DAG.
    ///
    /// Every surrounding constructor is rebuilt around expanded children and
    /// related by the ordinary checked congruence and logical-lowering rules.
    /// The operation is transactional and leaves the original rows resident.
    ///
    /// # Errors
    ///
    /// Returns an error unless the exact logical init prefix is installed and
    /// every reachable local row can be rebuilt by checked constructors.
    pub fn lower_logical_tree(
        &mut self,
        init: &Compiled,
        root: Ref,
    ) -> Result<LogicalExpansion, KernelError> {
        self.lower_logical_trees(init, &[root])
            .map(|expansions| expansions[0])
    }

    /// Recursively expands several logical syntax DAGs with shared output.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as
    /// [`lower_logical_tree`](Self::lower_logical_tree). An empty root slice is
    /// a no-op.
    pub fn lower_logical_trees(
        &mut self,
        init: &Compiled,
        roots: &[Ref],
    ) -> Result<Vec<LogicalExpansion>, KernelError> {
        for &root in roots {
            self.category_as::<Infallible>(root)?;
        }
        if !self.arena.has_definition_prefix(init.arena()) {
            return Err(KernelError::InitPrefixMismatch);
        }
        let mut staged = self.fork();
        let mut memo = BTreeMap::new();
        let mut expansions = Vec::with_capacity(roots.len());
        for &compact in roots {
            let (raw, fact) = staged.lower_logical_visit(init, compact, &mut memo)?;
            staged.union_syn_fact(fact)?;
            expansions.push(LogicalExpansion { compact, raw, fact });
        }
        *self = staged;
        Ok(expansions)
    }

    fn lower_logical_visit(
        &mut self,
        init: &Compiled,
        input: Ref,
        memo: &mut BTreeMap<Ref, (Ref, SynFactId)>,
    ) -> Result<(Ref, SynFactId), KernelError> {
        if let Some(&result) = memo.get(&input) {
            return Ok(result);
        }
        let row = self.row::<Infallible>(input)?.clone();
        if matches!(*row.expr(), Node::TmFv { .. } | Node::TyFv { .. }) {
            let fact = self.syn_refl(None, crate::SynRel::Syn, input)?;
            memo.insert(input, (input, fact));
            return Ok((input, fact));
        }
        let children = row.expr().children();
        let mut remapped = BTreeMap::new();
        let mut child_facts = Vec::with_capacity(children.len());
        for child in children {
            let (output, fact) = self.lower_logical_visit(init, child, memo)?;
            remapped.insert(child, output);
            child_facts.push(fact);
        }
        for &fact in &child_facts {
            self.union_syn_fact(fact)?;
        }
        let changed = remapped.iter().any(|(input, output)| input != output);
        let (generic, generic_fact) =
            self.rebuild_logical_container(init, input, &row, &remapped, &child_facts, changed)?;
        let result = if matches!(
            *self.row::<Infallible>(generic)?.expr(),
            Node::Op1(..) | Node::Op2(..)
        ) {
            let lowering = self.logical_lower_fact(None, init, generic)?;
            let raw = self.syn_fact(lowering)?.output();
            (raw, self.syn_trans(None, generic_fact, lowering)?)
        } else {
            (generic, generic_fact)
        };
        memo.insert(input, result);
        Ok(result)
    }

    /// Rebuilds one raw syntax tree with compact logical opcode aliases.
    ///
    /// Applications of the canonical `not`, `and`, `or`, and `imp`
    /// definitions are replaced recursively by their compact rows. Every
    /// other constructor is retained or rebuilt around compact children. The
    /// returned fact and equality columns certify the compact root as direct
    /// syntactic sugar for `raw`; callers may freely discard the scratch
    /// suffix after proof construction.
    ///
    /// The operation is transactional: malformed or unsupported syntax leaves
    /// the kernel unchanged.
    ///
    /// # Errors
    ///
    /// Returns an error unless `raw` is a resident local object under the init
    /// prefix and every rebuilt constructor and syntactic fact is accepted.
    pub fn compact_logical_tree(
        &mut self,
        init: &Compiled,
        raw: Ref,
    ) -> Result<LogicalAlias, KernelError> {
        self.compact_logical_trees(init, &[raw])
            .map(|aliases| aliases[0])
    }

    /// Rebuilds several raw syntax DAGs with shared compact logical aliases.
    ///
    /// All roots are constructed before any resulting equality is installed,
    /// so overlapping declaration packages cannot perturb later constructor
    /// checks. The complete operation is transactional and shares rebuilt
    /// descendants across roots.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as
    /// [`compact_logical_tree`](Self::compact_logical_tree). An empty root
    /// slice is a no-op.
    pub fn compact_logical_trees(
        &mut self,
        init: &Compiled,
        roots: &[Ref],
    ) -> Result<Vec<LogicalAlias>, KernelError> {
        for &raw in roots {
            self.category_as::<Infallible>(raw)?;
        }
        if !self.arena.has_definition_prefix(init.arena()) {
            return Err(KernelError::InitPrefixMismatch);
        }
        let mut staged = Self {
            arena: self.arena.clone(),
            init_prefix: self.init_prefix,
        };
        let mut memo = BTreeMap::new();
        let mut aliases = Vec::with_capacity(roots.len());
        for &raw in roots {
            let (compact, fact) = staged.compact_logical_visit(init, raw, &mut memo)?;
            aliases.push(LogicalAlias { raw, compact, fact });
        }
        for alias in &aliases {
            staged.union_syn_fact(alias.fact)?;
        }
        self.arena = staged.arena;
        Ok(aliases)
    }

    fn compact_logical_visit(
        &mut self,
        init: &Compiled,
        input: Ref,
        memo: &mut BTreeMap<Ref, (Ref, SynFactId)>,
    ) -> Result<(Ref, SynFactId), KernelError> {
        if let Some(&result) = memo.get(&input) {
            return Ok(result);
        }
        let row = self.row::<Infallible>(input)?.clone();
        let node = *row.expr();
        if matches!(
            node,
            Node::TmRef { .. } | Node::TyRef { .. } | Node::KindRef { .. }
        ) {
            return Err(KernelError::WrongForm {
                reference: input,
                expected: "local logical syntax",
                actual: row.tag(),
            });
        }
        // A named variable's annotation is part of its identity. Keep that
        // row exact; equality of a rebuilt surrounding classifier is enough
        // for checked applications, while manufacturing a parallel variable
        // would turn ordinary congruence into alpha-renaming.
        if matches!(node, Node::TmFv { .. } | Node::TyFv { .. }) {
            let fact = self.syn_refl(None, crate::SynRel::Syn, input)?;
            memo.insert(input, (input, fact));
            return Ok((input, fact));
        }
        let children = node.children();
        let mut remapped = BTreeMap::new();
        let mut child_facts = Vec::with_capacity(children.len());
        for child in children {
            let (output, fact) = self.compact_logical_visit(init, child, memo)?;
            remapped.insert(child, output);
            child_facts.push(fact);
        }
        for &fact in &child_facts {
            self.union_syn_fact(fact)?;
        }
        let changed = remapped.iter().any(|(input, output)| input != output);
        let (generic, generic_fact) =
            self.rebuild_logical_container(init, input, &row, &remapped, &child_facts, changed)?;
        let result = if let Some(compact) =
            self.recognize_logical_application(init, node, &remapped, memo)?
        {
            let lowering = self.logical_lower_fact_to(None, init, compact, generic)?;
            let lowering = self.syn_symm(None, lowering)?;
            let fact = self.syn_trans(None, generic_fact, lowering)?;
            (compact, fact)
        } else {
            (generic, generic_fact)
        };
        memo.insert(input, result);
        Ok(result)
    }

    fn rebuild_logical_container(
        &mut self,
        init: &Compiled,
        input: Ref,
        row: &Row,
        remapped: &BTreeMap<Ref, Ref>,
        child_facts: &[SynFactId],
        changed: bool,
    ) -> Result<(Ref, SynFactId), KernelError> {
        if !changed {
            return Ok((input, self.syn_refl(None, crate::SynRel::Syn, input)?));
        }
        let node = *row.expr();
        let output = self.rebuild_logical_node(input, row, node, remapped)?;
        let fact = match node {
            Node::Model { name, .. }
            | Node::TyExists { name, .. }
            | Node::TyForall { name, .. } => {
                let star = init.get("star").ok_or(KernelError::WrongForm {
                    reference: input,
                    expected: "named init kind star",
                    actual: row.tag(),
                })?;
                let binder = self.ty_fv(name, star)?;
                self.syn_implicit_binder_congr(
                    None,
                    crate::SynRel::Syn,
                    None,
                    None,
                    input,
                    output,
                    binder,
                    child_facts[0],
                )?
            }
            Node::Lam(..) | Node::TyLam(..) => self.syn_binder_congr(
                None,
                crate::SynRel::Syn,
                None,
                None,
                input,
                output,
                child_facts[0],
                child_facts[1],
            )?,
            _ => self.syn_congr(
                None,
                crate::SynRel::Syn,
                None,
                None,
                input,
                output,
                child_facts,
            )?,
        };
        Ok((output, fact))
    }

    fn rebuild_logical_node(
        &mut self,
        input: Ref,
        row: &Row,
        node: Node,
        remapped: &BTreeMap<Ref, Ref>,
    ) -> Result<Ref, KernelError> {
        let child = |reference| {
            remapped
                .get(&reference)
                .copied()
                .ok_or(KernelError::MissingDefinition { reference })
        };
        match node {
            Node::KindArr(left, right) => self.kind_arr(child(left)?, child(right)?),
            Node::TyArr(left, right) => self.ty_arr(child(left)?, child(right)?),
            Node::TyApp(function, argument) => self.ty_app(child(function)?, child(argument)?),
            Node::TyLam(binder, body) => self.ty_lam(child(binder)?, child(body)?),
            Node::TyFv { name, kind } => self.ty_fv(name, child(kind)?),
            Node::TyExists { name, predicate } => self.ty_exists(name, child(predicate)?),
            Node::TyForall { name, predicate } => self.ty_forall(name, child(predicate)?),
            Node::Model { name, predicate } => self.model(name, child(predicate)?),
            Node::TmFv { name, ty } => self.tm_fv(name, child(ty)?),
            Node::App(function, argument) => self.app(child(function)?, child(argument)?),
            Node::Lam(binder, body) => {
                self.lam_at(self.classifier(input)?, child(binder)?, child(body)?)
            }
            Node::Op1(op, operand) => self.op1(op, child(operand)?),
            Node::Op2(op, left, right) => self.op2(op, child(left)?, child(right)?),
            Node::Eq(ty, left, right) => {
                let bool_ty = self.classifier(input)?;
                self.eq_at(bool_ty, child(ty)?, child(left)?, child(right)?)
            }
            Node::Eps { ty, predicate } => self.eps(child(ty)?, child(predicate)?),
            Node::KindStar
            | Node::BoolTy
            | Node::Bool(_)
            | Node::TmRef { .. }
            | Node::TyRef { .. }
            | Node::KindRef { .. } => Err(KernelError::WrongForm {
                reference: input,
                expected: "logical syntax with remapped children",
                actual: row.tag(),
            }),
        }
    }

    fn recognize_logical_application(
        &mut self,
        init: &Compiled,
        node: Node,
        remapped: &BTreeMap<Ref, Ref>,
        memo: &BTreeMap<Ref, (Ref, SynFactId)>,
    ) -> Result<Option<Ref>, KernelError> {
        let Node::App(function, right) = node else {
            return Ok(None);
        };
        let right = remapped
            .get(&right)
            .copied()
            .ok_or(KernelError::MissingDefinition { reference: right })?;
        if init.get(Op1::Not.name()) == Some(function) {
            return self.op1(Op1::Not, right).map(Some);
        }
        let Node::App(definition, left) = *self.row::<Infallible>(function)?.expr() else {
            return Ok(None);
        };
        let op = [Op2::And, Op2::Or, Op2::Imp]
            .into_iter()
            .find(|op| init.get(op.name()) == Some(definition));
        let Some(op) = op else {
            return Ok(None);
        };
        let left = memo
            .get(&left)
            .map(|&(output, _)| output)
            .ok_or(KernelError::MissingDefinition { reference: left })?;
        self.op2(op, left, right).map(Some)
    }

    /// Appends object-language equality.
    ///
    /// # Errors
    ///
    /// Returns an error unless both operand types occupy one union-find class
    /// and `bool_ty` is Boolean.
    pub fn eq(&mut self, bool_ty: Ref, left: Ref, right: Ref) -> Result<Ref, KernelError> {
        let ty = self.classifier(left)?;
        self.eq_at(bool_ty, ty, left, right)
    }

    /// Appends object-language equality with an exact stored operand type.
    ///
    /// This allocation-target form is useful to checked elaborators which
    /// have already transported a type row and need the resulting syntax to
    /// retain that row rather than an equivalent operand classifier.
    ///
    /// # Errors
    ///
    /// Returns an error unless `ty` is a type, both operands have classifiers
    /// equivalent to `ty`, and `bool_ty` is Boolean.
    pub fn eq_at(
        &mut self,
        bool_ty: Ref,
        ty: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Ref, KernelError> {
        self.require_bool_type::<Infallible>(bool_ty)?;
        self.require_star_type::<Infallible>(ty)?;
        self.require_category::<Infallible>(left, Sort::Tm)?;
        self.require_category::<Infallible>(right, Sort::Tm)?;
        let left_ty = self.classifier(left)?;
        let right_ty = self.classifier(right)?;
        if !self.equivalent(ty, left_ty)? {
            return Err(KernelError::ClassifierMismatch {
                expected: ty,
                actual: left_ty,
            });
        }
        if !self.equivalent(ty, right_ty)? {
            return Err(KernelError::ClassifierMismatch {
                expected: ty,
                actual: right_ty,
            });
        }
        self.push::<Infallible>(Row::new(Node::Eq(ty, left, right)), Some(bool_ty))
    }

    /// Appends Hilbert choice.
    ///
    /// # Errors
    ///
    /// Returns an error unless the predicate type class contains `ty → bool`.
    pub fn eps(&mut self, ty: Ref, predicate: Ref) -> Result<Ref, KernelError> {
        self.require_star_type::<Infallible>(ty)?;
        self.require_category::<Infallible>(predicate, Sort::Tm)?;
        let predicate_ty = self.classifier(predicate)?;
        let (domain, codomain) = self.type_arrow_member::<Infallible>(predicate_ty)?;
        if !self.equivalent(domain, ty)? {
            return Err(KernelError::ClassifierMismatch {
                expected: ty,
                actual: domain,
            });
        }
        self.require_bool_type::<Infallible>(codomain)?;
        self.push::<Infallible>(Row::new(Node::Eps { ty, predicate }), Some(ty))
    }

    /// Appends a literal arena import without asserting anything about it.
    ///
    /// # Errors
    ///
    /// Returns an error if the import reference space is exhausted.
    pub fn import_literal(&mut self, arena: Arena) -> Result<ImportId, KernelError> {
        self.push_import::<Infallible>(Import::Literal(Box::new(arena)))
    }

    /// Appends a lazy content-addressed import without resolving it.
    ///
    /// # Errors
    ///
    /// Returns an error if the import reference space is exhausted.
    pub fn import_link(&mut self, link: Link) -> Result<ImportId, KernelError> {
        self.push_import::<Infallible>(Import::Link(link))
    }

    /// Appends a kind proxy under an explicit imported-validity premise.
    ///
    /// # Errors
    ///
    /// Returns an error if resolution fails or the resolved row is not a kind.
    pub fn kind_ref<R: Resolver + ?Sized>(
        &mut self,
        resolver: &mut R,
        source: ImportId,
        foreign: Ref,
    ) -> Result<Ref, KernelError<R::Error>> {
        let target = self.resolve_foreign(resolver, source, foreign)?;
        if target != Sort::Kind {
            return Err(KernelError::WrongCategory {
                reference: foreign,
                expected: Sort::Kind,
                actual: target,
            });
        }
        if !self.arena.has_definition_capacity() {
            return Err(KernelError::TooManyDefinitions);
        }
        if !self
            .arena
            .push_ambient_context(AmbPred::ArenaOk { src: source })
        {
            return Err(KernelError::TooManyAmbientPredicates);
        }
        self.push::<R::Error>(
            Row::new(Node::KindRef {
                src: source,
                ix: foreign,
            }),
            None,
        )
    }

    /// Appends a type proxy under an explicit foreign-kinding premise.
    ///
    /// # Errors
    ///
    /// Returns an error if the local kind is invalid, resolution fails, or the
    /// resolved row is not a type.
    pub fn ty_ref<R: Resolver + ?Sized>(
        &mut self,
        resolver: &mut R,
        source: ImportId,
        foreign: Ref,
        kind: Ref,
    ) -> Result<Ref, KernelError<R::Error>> {
        self.require_category::<R::Error>(kind, Sort::Kind)?;
        let target = self.resolve_foreign(resolver, source, foreign)?;
        if target != Sort::Ty {
            return Err(KernelError::WrongCategory {
                reference: foreign,
                expected: Sort::Ty,
                actual: target,
            });
        }
        if !self.arena.has_definition_capacity() {
            return Err(KernelError::TooManyDefinitions);
        }
        if !self.arena.push_ambient_context(AmbPred::HolSort {
            src: source,
            ix: foreign,
            sort: kind,
        }) {
            return Err(KernelError::TooManyAmbientPredicates);
        }
        self.push::<R::Error>(
            Row::new(Node::TyRef {
                src: source,
                ix: foreign,
            }),
            Some(kind),
        )
    }

    /// Appends a term proxy under an explicit foreign-typing premise.
    ///
    /// # Errors
    ///
    /// Returns an error if the local type is invalid, resolution fails, or the
    /// resolved row is not a term.
    pub fn tm_ref<R: Resolver + ?Sized>(
        &mut self,
        resolver: &mut R,
        source: ImportId,
        foreign: Ref,
        ty: Ref,
    ) -> Result<Ref, KernelError<R::Error>> {
        self.require_star_type::<R::Error>(ty)?;
        let target = self.resolve_foreign(resolver, source, foreign)?;
        if target != Sort::Tm {
            return Err(KernelError::WrongCategory {
                reference: foreign,
                expected: Sort::Tm,
                actual: target,
            });
        }
        if !self.arena.has_definition_capacity() {
            return Err(KernelError::TooManyDefinitions);
        }
        if !self.arena.push_ambient_context(AmbPred::HolSort {
            src: source,
            ix: foreign,
            sort: ty,
        }) {
            return Err(KernelError::TooManyAmbientPredicates);
        }
        self.push::<R::Error>(
            Row::new(Node::TmRef {
                src: source,
                ix: foreign,
            }),
            Some(ty),
        )
    }

    /// Adds a checked Boolean term to the logical context.
    ///
    /// # Errors
    ///
    /// Returns an error unless `proposition` is a Boolean term.
    pub fn add_context(&mut self, proposition: Ref) -> Result<(), KernelError> {
        self.require_bool_term::<Infallible>(proposition)?;
        self.arena.insert_context(proposition);
        Ok(())
    }

    /// Enables one Ethane axiom capability.
    ///
    /// `ax.inf` is the axiom of infinity and `ax.sub` the guarded
    /// subtype-package sentence ([`Kernel::sub_exists`]). Recording a
    /// capability is how an arena declares, auditably, which object-logic
    /// assumptions its conclusions may rest on.
    ///
    /// # Errors
    ///
    /// Returns an error for every currently unsupported name.
    pub fn add_axiom(&mut self, name: &str) -> Result<(), KernelError> {
        if !matches!(name, infinity::AX_INF | subtype::AX_SUB) {
            return Err(KernelError::UnsupportedAxiom {
                name: name.to_owned(),
            });
        }
        self.arena.insert_axiom(name);
        Ok(())
    }

    fn resolve_foreign<R: Resolver + ?Sized>(
        &self,
        resolver: &mut R,
        source: ImportId,
        foreign: Ref,
    ) -> Result<Sort, KernelError<R::Error>> {
        self.arena
            .resolve_foreign(resolver, source, foreign)
            .map(|expression| expression.tag().sort())
            .map_err(|source| KernelError::Resolve { source })
    }

    #[allow(clippy::too_many_lines)]
    fn validate_copy_row(&self, reference: Ref) -> Result<(), KernelError> {
        let row = self.row::<Infallible>(reference)?;
        let row_sort = self.arena.sort(reference);
        let expected_sort = match *row.expr() {
            Node::KindStar => None,
            Node::KindArr(domain, codomain) => {
                self.require_category::<Infallible>(domain, Sort::Kind)?;
                self.require_category::<Infallible>(codomain, Sort::Kind)?;
                None
            }
            Node::BoolTy => {
                let sort = row_sort.ok_or(KernelError::MissingSort { reference })?;
                self.require_star::<Infallible>(sort)?;
                Some(sort)
            }
            Node::TyArr(domain, codomain) => {
                let star = self.require_star_type::<Infallible>(domain)?;
                self.require_star_type::<Infallible>(codomain)?;
                Some(star)
            }
            Node::TyFv { kind, .. } => {
                self.require_category::<Infallible>(kind, Sort::Kind)?;
                Some(kind)
            }
            Node::TyApp(function, argument) => {
                self.require_category::<Infallible>(function, Sort::Ty)?;
                self.require_category::<Infallible>(argument, Sort::Ty)?;
                let (domain, codomain) =
                    self.kind_arrow::<Infallible>(self.classifier(function)?)?;
                let actual = self.classifier(argument)?;
                if actual != domain {
                    return Err(KernelError::ClassifierMismatch {
                        expected: domain,
                        actual,
                    });
                }
                Some(codomain)
            }
            Node::TyLam(binder, body) => {
                self.require_form::<Infallible>(binder, "ty.fv", |node| {
                    matches!(node, Node::TyFv { .. })
                })?;
                self.require_category::<Infallible>(body, Sort::Ty)?;
                let sort = row_sort.ok_or(KernelError::MissingSort { reference })?;
                let (domain, codomain) = self.kind_arrow::<Infallible>(sort)?;
                if domain != self.classifier(binder)? || codomain != self.classifier(body)? {
                    return Err(KernelError::ClassifierMismatch {
                        expected: self.classifier(body)?,
                        actual: codomain,
                    });
                }
                Some(sort)
            }
            Node::Model { predicate, .. } => {
                let bool_ty = self.require_bool_term::<Infallible>(predicate)?;
                Some(self.classifier(bool_ty)?)
            }
            Node::TyExists { predicate, .. } | Node::TyForall { predicate, .. } => {
                Some(self.require_bool_term::<Infallible>(predicate)?)
            }
            Node::TmFv { ty, .. } => {
                self.require_star_type::<Infallible>(ty)?;
                Some(ty)
            }
            Node::App(function, argument) => {
                self.require_category::<Infallible>(function, Sort::Tm)?;
                self.require_category::<Infallible>(argument, Sort::Tm)?;
                let (domain, codomain) =
                    self.type_arrow_member::<Infallible>(self.classifier(function)?)?;
                let actual = self.classifier(argument)?;
                if domain != actual {
                    return Err(KernelError::ClassifierMismatch {
                        expected: domain,
                        actual,
                    });
                }
                Some(codomain)
            }
            Node::Lam(binder, body) => {
                self.require_form::<Infallible>(binder, "tm.fv", |node| {
                    matches!(node, Node::TmFv { .. })
                })?;
                self.require_category::<Infallible>(body, Sort::Tm)?;
                let sort = row_sort.ok_or(KernelError::MissingSort { reference })?;
                let (domain, codomain) = self.type_arrow_member::<Infallible>(sort)?;
                if domain != self.classifier(binder)? || codomain != self.classifier(body)? {
                    return Err(KernelError::ClassifierMismatch {
                        expected: self.classifier(body)?,
                        actual: codomain,
                    });
                }
                Some(sort)
            }
            Node::Bool(_) => {
                let sort = row_sort.ok_or(KernelError::MissingSort { reference })?;
                self.require_bool_type::<Infallible>(sort)?;
                Some(sort)
            }
            Node::Op1(_, operand) => Some(self.require_bool_term::<Infallible>(operand)?),
            Node::Op2(_, left, right) => {
                let bool_ty = self.require_bool_term::<Infallible>(left)?;
                let right_ty = self.require_bool_term::<Infallible>(right)?;
                if !self.equivalent(bool_ty, right_ty)? {
                    return Err(KernelError::ClassifierMismatch {
                        expected: bool_ty,
                        actual: right_ty,
                    });
                }
                Some(bool_ty)
            }
            Node::Eq(ty, left, right) => {
                self.require_category::<Infallible>(ty, Sort::Ty)?;
                self.require_category::<Infallible>(left, Sort::Tm)?;
                self.require_category::<Infallible>(right, Sort::Tm)?;
                let left_ty = self.classifier(left)?;
                let right_ty = self.classifier(right)?;
                if !self.equivalent(ty, left_ty)? {
                    return Err(KernelError::ClassifierMismatch {
                        expected: left_ty,
                        actual: ty,
                    });
                }
                if !self.equivalent(left_ty, right_ty)? {
                    return Err(KernelError::ClassifierMismatch {
                        expected: left_ty,
                        actual: right_ty,
                    });
                }
                let sort = row_sort.ok_or(KernelError::MissingSort { reference })?;
                self.require_bool_type::<Infallible>(sort)?;
                Some(sort)
            }
            Node::Eps { ty, predicate } => {
                self.require_star_type::<Infallible>(ty)?;
                let (domain, codomain) =
                    self.type_arrow_member::<Infallible>(self.classifier(predicate)?)?;
                if domain != ty {
                    return Err(KernelError::ClassifierMismatch {
                        expected: ty,
                        actual: domain,
                    });
                }
                self.require_bool_type::<Infallible>(codomain)?;
                Some(ty)
            }
            Node::TmRef { .. } | Node::TyRef { .. } | Node::KindRef { .. } => {
                return Err(KernelError::ImportedProxy { reference });
            }
        };
        if row_sort != expected_sort {
            return match (expected_sort, row_sort) {
                (Some(expected), Some(actual)) => {
                    Err(KernelError::ClassifierMismatch { expected, actual })
                }
                _ => Err(KernelError::MissingSort { reference }),
            };
        }
        Ok(())
    }

    fn copy_order(&self, roots: &[Ref]) -> Result<(Vec<Ref>, BTreeMap<Ref, Ref>), KernelError> {
        let mut state = BTreeMap::<Ref, bool>::new();
        let mut order = Vec::new();
        let mut nodes = BTreeMap::new();
        let prefix_len = self.init_prefix.map_or(0, |(_, len)| len);
        for &root in roots {
            let mut stack = vec![(root, false)];
            while let Some((reference, expanded)) = stack.pop() {
                let reference_index = usize::try_from(reference.get())
                    .map_err(|_| KernelError::TooManyDefinitions)?;
                if reference_index <= prefix_len {
                    state.insert(reference, true);
                    nodes.insert(reference, reference);
                    continue;
                }
                if expanded {
                    state.insert(reference, true);
                    order.push(reference);
                    continue;
                }
                match state.get(&reference) {
                    Some(true) => continue,
                    Some(false) => return Err(KernelError::CyclicSyntax { reference }),
                    None => {}
                }
                state.insert(reference, false);
                let row = self.row::<Infallible>(reference)?;
                if matches!(
                    row.expr(),
                    Node::TmRef { .. } | Node::TyRef { .. } | Node::KindRef { .. }
                ) {
                    return Err(KernelError::ImportedProxy { reference });
                }
                stack.push((reference, true));
                let mut dependencies = row.expr().children();
                if row.tag().sort() != Sort::Kind {
                    dependencies.push(self.classifier_as::<Infallible>(reference)?);
                }
                let syntax_root = self.find_path_in::<Infallible>(EqColumn::Syn, reference)?.0;
                if syntax_root != reference {
                    dependencies.push(syntax_root);
                }
                for dependency in dependencies.into_iter().rev() {
                    stack.push((dependency, false));
                }
            }
        }
        Ok((order, nodes))
    }

    fn push<E>(&mut self, row: Row, sort: Option<Ref>) -> Result<Ref, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.arena
            .push_row(row, sort)
            .ok_or(KernelError::TooManyDefinitions)
    }

    fn push_import<E>(&mut self, import: Import) -> Result<ImportId, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.arena
            .push_import(import)
            .ok_or(KernelError::TooManyImports)
    }

    fn row<E>(&self, reference: Ref) -> Result<&Row, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.arena
            .row(reference)
            .ok_or(KernelError::MissingDefinition { reference })
    }

    fn category_as<E>(&self, reference: Ref) -> Result<Sort, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.arena
            .tag(reference)
            .map(Tag::sort)
            .ok_or(KernelError::MissingDefinition { reference })
    }

    fn classifier_as<E>(&self, reference: Ref) -> Result<Ref, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.conv_path::<E>(reference)?
            .classifier
            .ok_or(KernelError::MissingSort { reference })
    }

    fn require_category<E>(&self, reference: Ref, expected: Sort) -> Result<(), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let actual = self.category_as::<E>(reference)?;
        if actual == expected {
            Ok(())
        } else {
            Err(KernelError::WrongCategory {
                reference,
                expected,
                actual,
            })
        }
    }

    fn require_form<E>(
        &self,
        reference: Ref,
        expected: &'static str,
        predicate: impl FnOnce(&Node) -> bool,
    ) -> Result<(), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let row = self.row::<E>(reference)?;
        if predicate(row.expr()) {
            Ok(())
        } else {
            Err(KernelError::WrongForm {
                reference,
                expected,
                actual: row.tag(),
            })
        }
    }

    fn require_star<E>(&self, reference: Ref) -> Result<(), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.require_form(reference, "kind.star", |node| {
            matches!(node, Node::KindStar)
        })
    }

    fn require_star_type<E>(&self, reference: Ref) -> Result<Ref, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.require_category(reference, Sort::Ty)?;
        let kind = self.classifier_as::<E>(reference)?;
        self.require_star(kind)?;
        Ok(kind)
    }

    fn require_bool_type<E>(&self, reference: Ref) -> Result<(), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.require_star_type(reference)?;
        let representative = self.find_as::<E>(reference)?;
        for candidate in self.references::<E>()? {
            if self.find_as::<E>(candidate)? == representative
                && matches!(self.row::<E>(candidate)?.expr(), Node::BoolTy)
            {
                return Ok(());
            }
        }
        Err(KernelError::WrongForm {
            reference,
            expected: "a type class containing ty.bool",
            actual: self.row::<E>(reference)?.tag(),
        })
    }

    fn require_bool_term<E>(&self, reference: Ref) -> Result<Ref, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.require_category(reference, Sort::Tm)?;
        let ty = self.classifier_as::<E>(reference)?;
        self.require_bool_type(ty)?;
        Ok(ty)
    }

    fn kind_arrow<E>(&self, reference: Ref) -> Result<(Ref, Ref), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let row = self.row::<E>(reference)?;
        if let Node::KindArr(domain, codomain) = *row.expr() {
            Ok((domain, codomain))
        } else {
            Err(KernelError::WrongForm {
                reference,
                expected: "kind.arr",
                actual: row.tag(),
            })
        }
    }

    fn type_arrow_member<E>(&self, reference: Ref) -> Result<(Ref, Ref), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.require_category(reference, Sort::Ty)?;
        let representative = self.find_as::<E>(reference)?;
        for candidate in self.references::<E>()? {
            if self.category_as::<E>(candidate)? == Sort::Ty
                && self.find_as::<E>(candidate)? == representative
                && let Node::TyArr(domain, codomain) = *self.row::<E>(candidate)?.expr()
            {
                return Ok((domain, codomain));
            }
        }
        Err(KernelError::WrongForm {
            reference,
            expected: "a type class containing ty.arr",
            actual: self.row::<E>(reference)?.tag(),
        })
    }

    fn find_path<E>(&self, reference: Ref) -> Result<(Ref, SmallVec<[Ref; 8]>), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.find_path_in(EqColumn::Semantic, reference)
    }

    fn find_as<E>(&self, reference: Ref) -> Result<Ref, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.find_path(reference)
            .map(|(representative, _)| representative)
    }

    fn find_mut_as<E>(&mut self, reference: Ref) -> Result<Ref, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.find_mut_in(EqColumn::Semantic, reference)
    }

    fn equivalent_as<E>(&self, left: Ref, right: Ref) -> Result<bool, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        if self.category_as::<E>(left)? != self.category_as::<E>(right)? {
            return Ok(false);
        }
        Ok(self.find_as::<E>(left)? == self.find_as::<E>(right)?)
    }

    fn equivalent_mut_as<E>(&mut self, left: Ref, right: Ref) -> Result<bool, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        if self.category_as::<E>(left)? != self.category_as::<E>(right)? {
            return Ok(false);
        }
        Ok(self.find_mut_as::<E>(left)? == self.find_mut_as::<E>(right)?)
    }

    fn union<E>(&mut self, left: Ref, right: Ref) -> Result<(), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.union_in(EqColumn::Semantic, left, right)
    }

    fn find_path_in<E>(
        &self,
        column: EqColumn,
        reference: Ref,
    ) -> Result<(Ref, SmallVec<[Ref; 8]>), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let category = self.category_as::<E>(reference)?;
        let mut path = SmallVec::<[Ref; 8]>::new();
        let mut current = reference;
        loop {
            if let Some(cycle_start) = path.iter().position(|member| *member == current) {
                let representative = path[cycle_start..]
                    .iter()
                    .copied()
                    .min()
                    .expect("a repeated member starts a nonempty cycle");
                return Ok((representative, path));
            }
            path.push(current);
            let Some(parent) = self.arena.eq_column(column, current) else {
                return Ok((current, path));
            };
            let parent_category = self.category_as::<E>(parent)?;
            if parent_category != category {
                return Err(KernelError::WrongCategory {
                    reference: parent,
                    expected: category,
                    actual: parent_category,
                });
            }
            current = parent;
        }
    }

    fn union_in<E>(&mut self, column: EqColumn, left: Ref, right: Ref) -> Result<(), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        if column == EqColumn::Conv {
            return self.union_conv::<E>(left, right);
        }
        // Preflight both paths before compressing either one. Any preflight
        // error is therefore transactional even for malformed private state.
        let (left_root, left_path) = self.find_path_in::<E>(column, left)?;
        let _ = self.find_path_in::<E>(column, right)?;
        self.compress_path_in(column, left_root, left_path);
        // Recompute after left compression so the successful path certificate
        // describes the current forest. Every preflight failure above is
        // transactional; failure here is unreachable for a checked kernel.
        let (right_root, right_path) = self.find_path_in::<E>(column, right)?;
        self.compress_path_in(column, right_root, right_path);
        if left_root == right_root {
            return Ok(());
        }
        let (child, parent) = if left_root > right_root {
            (left_root, right_root)
        } else {
            (right_root, left_root)
        };
        let recorded = self.arena.set_eq_column(column, child, Some(parent));
        debug_assert!(recorded, "union roots name resident rows");
        Ok(())
    }

    fn find_mut_in<E>(&mut self, column: EqColumn, reference: Ref) -> Result<Ref, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        if column == EqColumn::Conv {
            return self.find_conv_mut::<E>(reference);
        }
        let (representative, path) = self.find_path_in(column, reference)?;
        self.compress_path_in(column, representative, path);
        Ok(representative)
    }

    fn compress_path_in(
        &mut self,
        column: EqColumn,
        representative: Ref,
        path: SmallVec<[Ref; 8]>,
    ) {
        for member in path {
            let parent = (member != representative).then_some(representative);
            let recorded = self.arena.set_eq_column(column, member, parent);
            debug_assert!(recorded, "find path contains only resident rows");
        }
    }

    /// Follows the fused conversion/classifier column.
    ///
    /// Same-category edges belong to the conversion forest.  Its root may
    /// carry one cross-category edge encoding the class classifier.
    fn conv_path<E>(&self, reference: Ref) -> Result<ConvPath, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let category = self.category_as::<E>(reference)?;
        let classifier_category = match category {
            Sort::Kind => None,
            Sort::Ty => Some(Sort::Kind),
            Sort::Tm => Some(Sort::Ty),
        };
        let mut path = SmallVec::<[Ref; 8]>::new();
        let mut current = reference;
        loop {
            if let Some(cycle_start) = path.iter().position(|member| *member == current) {
                let representative = path[cycle_start..]
                    .iter()
                    .copied()
                    .min()
                    .expect("a repeated member starts a nonempty cycle");
                return Ok(ConvPath {
                    root: representative,
                    classifier: None,
                    members: path,
                });
            }
            path.push(current);
            let Some(parent) = self.arena.conv(current) else {
                return Ok(ConvPath {
                    root: current,
                    classifier: None,
                    members: path,
                });
            };
            let parent_category = self.category_as::<E>(parent)?;
            if parent_category == category {
                current = parent;
                continue;
            }
            let Some(expected) = classifier_category else {
                return Err(KernelError::WrongCategory {
                    reference: parent,
                    expected: category,
                    actual: parent_category,
                });
            };
            if parent_category != expected {
                return Err(KernelError::WrongCategory {
                    reference: parent,
                    expected,
                    actual: parent_category,
                });
            }
            return Ok(ConvPath {
                root: current,
                classifier: Some(parent),
                members: path,
            });
        }
    }

    fn find_conv_mut<E>(&mut self, reference: Ref) -> Result<Ref, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let path = self.conv_path::<E>(reference)?;
        let root = path.root;
        self.compress_conv_path(path);
        Ok(root)
    }

    fn compress_conv_path(&mut self, path: ConvPath) {
        for member in path.members {
            let parent = if member == path.root {
                path.classifier
            } else {
                Some(path.root)
            };
            let recorded = self.arena.set_eq_column(EqColumn::Conv, member, parent);
            debug_assert!(recorded, "conversion path contains only resident rows");
        }
    }

    fn union_conv<E>(&mut self, left: Ref, right: Ref) -> Result<(), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let left_category = self.category_as::<E>(left)?;
        let right_category = self.category_as::<E>(right)?;
        if left_category != right_category {
            return Err(KernelError::WrongCategory {
                reference: right,
                expected: left_category,
                actual: right_category,
            });
        }
        if left_category != Sort::Kind {
            let left_classifier = self.classifier_as::<E>(left)?;
            let right_classifier = self.classifier_as::<E>(right)?;
            if !self.equivalent_as::<E>(left_classifier, right_classifier)? {
                return Err(KernelError::ClassifierMismatch {
                    expected: left_classifier,
                    actual: right_classifier,
                });
            }
        }
        // As for ordinary equality, validate both paths before mutating
        // either. Every preflight error is transactional. Failure while
        // recomputing the right path below is unreachable for a checked
        // kernel, but malformed private state may already have had its left
        // path compressed when that defensive error is returned.
        let left_path = self.conv_path::<E>(left)?;
        let _right_path = self.conv_path::<E>(right)?;
        let left_root = left_path.root;
        self.compress_conv_path(left_path);
        // Re-read the right path from the state produced by the first
        // compression. The preservation theorem shows that this cannot fail
        // after both preflights succeed on a valid kernel.
        let right_path = self.conv_path::<E>(right)?;
        let right_root = right_path.root;
        self.compress_conv_path(right_path);
        if left_root == right_root {
            return Ok(());
        }
        let (child, parent) = if left_root > right_root {
            (left_root, right_root)
        } else {
            (right_root, left_root)
        };
        let recorded = self
            .arena
            .set_eq_column(EqColumn::Conv, child, Some(parent));
        debug_assert!(recorded, "conversion roots name resident rows");
        Ok(())
    }

    fn references<E>(&self) -> Result<Vec<Ref>, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        (1..=self.arena.len())
            .map(|position| {
                i32::try_from(position)
                    .ok()
                    .and_then(Ref::new)
                    .ok_or(KernelError::TooManyDefinitions)
            })
            .collect()
    }
}

fn remap_row(row: &Row, sort: Option<Ref>, map: &BTreeMap<Ref, Ref>) -> (Row, Option<Ref>) {
    let remap = |reference: Ref| map[&reference];
    let expr = match *row.expr() {
        Node::KindStar => Node::KindStar,
        Node::KindArr(a, b) => Node::KindArr(remap(a), remap(b)),
        Node::BoolTy => Node::BoolTy,
        Node::TyArr(a, b) => Node::TyArr(remap(a), remap(b)),
        Node::TyApp(a, b) => Node::TyApp(remap(a), remap(b)),
        Node::TyLam(a, b) => Node::TyLam(remap(a), remap(b)),
        Node::TyFv { name, kind } => Node::TyFv {
            name,
            kind: remap(kind),
        },
        Node::TyForall { name, predicate } => Node::TyForall {
            name,
            predicate: remap(predicate),
        },
        Node::TyExists { name, predicate } => Node::TyExists {
            name,
            predicate: remap(predicate),
        },
        Node::Model { name, predicate } => Node::Model {
            name,
            predicate: remap(predicate),
        },
        Node::TmFv { name, ty } => Node::TmFv {
            name,
            ty: remap(ty),
        },
        Node::App(a, b) => Node::App(remap(a), remap(b)),
        Node::Lam(a, b) => Node::Lam(remap(a), remap(b)),
        Node::Bool(value) => Node::Bool(value),
        Node::Op1(op, operand) => Node::Op1(op, remap(operand)),
        Node::Op2(op, left, right) => Node::Op2(op, remap(left), remap(right)),
        Node::Eq(ty, a, b) => Node::Eq(remap(ty), remap(a), remap(b)),
        Node::Eps { ty, predicate } => Node::Eps {
            ty: remap(ty),
            predicate: remap(predicate),
        },
        Node::TmRef { .. } | Node::TyRef { .. } | Node::KindRef { .. } => {
            unreachable!("imported proxies are rejected before copying")
        }
    };
    (Row::new(expr), sort.map(remap))
}

#[cfg(test)]
mod tests {
    use std::convert::Infallible;

    use super::*;
    use crate::{KindTag, LinkFormat, SynRel, Table, TmTag, TyTag, init};
    use covalence_lib_json::serde_json;

    #[cfg(not(feature = "buck-test-fixtures"))]
    const INIT_FIXTURE: &str = include_str!("../../../../theories/init-boolean.checked.json");
    #[cfg(feature = "buck-test-fixtures")]
    const INIT_FIXTURE: &str = include_str!("../theories/init-boolean.checked.json");

    struct OneTable(Table);

    impl Resolver for OneTable {
        type Error = Infallible;

        fn resolve(&mut self, _: &Link) -> Result<Table, Self::Error> {
            Ok(self.0.clone())
        }
    }

    #[test]
    fn constructs_typed_rows_using_only_local_references() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let variable = kernel.tm_fv(0, bool_ty).unwrap();
        let identity = kernel.lam(variable, variable).unwrap();
        let truth = kernel.bool(bool_ty, true).unwrap();
        let application = kernel.app(identity, truth).unwrap();
        let equation = kernel.eq(bool_ty, application, truth).unwrap();
        kernel.add_context(equation).unwrap();

        assert_eq!(kernel.classifier(application).unwrap(), bool_ty);
        assert_eq!(kernel.arena().tag(identity), Some(Tag::Tm(TmTag::Lam)));
        assert_eq!(kernel.arena().context().collect::<Vec<_>>(), [equation]);
    }

    #[test]
    fn logical_rows_are_boolean_checked_and_lower_canonically() {
        let manifest: init::Manifest = serde_json::from_str(INIT_FIXTURE).unwrap();
        let init = init::compile(&manifest).unwrap();
        let bool_ty = init.get("bool").unwrap();
        let truth = init.get("true").unwrap();
        let falsehood = init.get("false").unwrap();

        for operand in [falsehood, truth] {
            let op = Op1::Not;
            let mut lowered = Kernel::with_init(&init);
            let compact = lowered.op1(op, operand).unwrap();
            assert_eq!(lowered.arena().op1(compact), Some(op));
            let result = lowered.lower_logical(&init, compact).unwrap();

            let mut direct = Kernel::with_init(&init);
            let direct_compact = direct.op1(op, operand).unwrap();
            assert_eq!(direct_compact, compact);
            let expected = direct.app(init.get(op.name()).unwrap(), operand).unwrap();
            assert_eq!(result, expected);
            assert_eq!(lowered.into_arena(), direct.into_arena());
        }

        for op in [Op2::And, Op2::Or, Op2::Imp] {
            for left in [falsehood, truth] {
                for right in [falsehood, truth] {
                    let mut lowered = Kernel::with_init(&init);
                    let compact = lowered.op2(op, left, right).unwrap();
                    assert_eq!(lowered.arena().op2(compact), Some(op));
                    let result = lowered.lower_logical(&init, compact).unwrap();

                    let mut direct = Kernel::with_init(&init);
                    let direct_compact = direct.op2(op, left, right).unwrap();
                    assert_eq!(direct_compact, compact);
                    let partial = direct.app(init.get(op.name()).unwrap(), left).unwrap();
                    let expected = direct.app(partial, right).unwrap();
                    assert_eq!(result, expected);
                    assert_eq!(lowered.into_arena(), direct.into_arena());
                }
            }
        }

        let mut wrong = Kernel::new();
        let star = wrong.star().unwrap();
        let wrong_bool = wrong.bool_ty(star).unwrap();
        assert!(wrong.op1(Op1::Not, wrong_bool).is_err());
        assert!(wrong.op2(Op2::And, wrong_bool, wrong_bool).is_err());
        let raw_compact = wrong.arena.push_op1(Op1::Not, wrong_bool).unwrap();
        assert!(matches!(
            wrong.lower_logical(&init, raw_compact),
            Err(KernelError::InitPrefixMismatch)
        ));
        assert_eq!(init.get("bool"), Some(bool_ty));
    }

    #[test]
    fn logical_lowering_produces_checked_direct_syntactic_facts() {
        let manifest: init::Manifest = serde_json::from_str(INIT_FIXTURE).unwrap();
        let init = init::compile(&manifest).unwrap();
        let truth = init.get("true").unwrap();

        let mut unary = Kernel::with_init(&init);
        let compact = unary.op1(Op1::Not, truth).unwrap();
        let id = unary.logical_lower_fact(None, &init, compact).unwrap();
        let fact = unary.syn_fact(id).unwrap();
        assert_eq!(fact.rel(), SynRel::Syn);
        assert_eq!(fact.input(), compact);
        assert_eq!(fact.var(), None);
        assert_eq!(fact.val(), None);

        let mut unary_direct = Kernel::with_init(&init);
        let direct_compact = unary_direct.op1(Op1::Not, truth).unwrap();
        let direct_expansion = unary_direct.lower_logical(&init, direct_compact).unwrap();
        assert_eq!(fact.output(), direct_expansion);
        unary.union_syn_fact(id).unwrap();
        assert!(unary.equivalent(compact, fact.output()).unwrap());

        for op in [Op2::And, Op2::Or, Op2::Imp] {
            let mut binary = Kernel::with_init(&init);
            let compact = binary.op2(op, truth, truth).unwrap();
            let id = binary.logical_lower_fact(None, &init, compact).unwrap();
            let fact = binary.syn_fact(id).unwrap();

            let mut direct = Kernel::with_init(&init);
            let direct_compact = direct.op2(op, truth, truth).unwrap();
            let direct_expansion = direct.lower_logical(&init, direct_compact).unwrap();
            assert_eq!(fact.rel(), SynRel::Syn);
            assert_eq!(fact.input(), compact);
            assert_eq!(fact.output(), direct_expansion);
        }

        let mut initialized = Kernel::with_init(&init);
        assert!(initialized.logical_lower_fact(None, &init, truth).is_err());
        assert_eq!(initialized.syn_fact_len(), 0);

        let mut bare = Kernel::new();
        let star = bare.star().unwrap();
        let bool_ty = bare.bool_ty(star).unwrap();
        let bare_truth = bare.bool(bool_ty, true).unwrap();
        let compact = bare.op1(Op1::Not, bare_truth).unwrap();
        assert!(matches!(
            bare.logical_lower_fact(None, &init, compact),
            Err(KernelError::InitPrefixMismatch)
        ));
        assert_eq!(bare.syn_fact_len(), 0);
    }

    #[test]
    fn abstraction_can_reuse_a_named_function_type() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let function_ty = kernel.ty_arr(bool_ty, bool_ty).unwrap();
        let variable = kernel.tm_fv(0, bool_ty).unwrap();
        let abstraction = kernel.lam_at(function_ty, variable, variable).unwrap();

        assert_eq!(kernel.classifier(abstraction).unwrap(), function_ty);
        assert!(matches!(
            kernel.lam_at(bool_ty, variable, variable),
            Err(KernelError::WrongForm { .. })
        ));
    }

    #[test]
    fn raw_logical_trees_gain_checked_compact_proof_aliases() {
        let manifest: init::Manifest = serde_json::from_str(INIT_FIXTURE).unwrap();
        let init = init::compile(&manifest).unwrap();
        let mut kernel = Kernel::with_init(&init);
        let truth = init.get("true").unwrap();
        let apply1 = |kernel: &mut Kernel, name: &str, argument| {
            kernel.app(init.get(name).unwrap(), argument).unwrap()
        };
        let apply2 = |kernel: &mut Kernel, name: &str, left, right| {
            let partial = kernel.app(init.get(name).unwrap(), left).unwrap();
            kernel.app(partial, right).unwrap()
        };
        let negated = apply1(&mut kernel, "not", truth);
        let conjunction = apply2(&mut kernel, "and", negated, truth);
        let raw = apply2(&mut kernel, "imp", conjunction, truth);
        let before = kernel.arena.len();

        let alias = kernel.compact_logical_tree(&init, raw).unwrap();
        assert_eq!(alias.raw, raw);
        assert_eq!(kernel.arena.op2(alias.compact), Some(Op2::Imp));
        let [left, right] = kernel
            .row::<Infallible>(alias.compact)
            .unwrap()
            .expr()
            .children()[..]
        else {
            panic!("binary alias")
        };
        assert_eq!(right, truth);
        assert_eq!(kernel.arena.op2(left), Some(Op2::And));
        let negated = kernel.row::<Infallible>(left).unwrap().expr().children()[0];
        assert_eq!(kernel.arena.op1(negated), Some(Op1::Not));
        let fact = kernel.syn_fact(alias.fact).unwrap();
        assert_eq!(fact.input(), raw);
        assert_eq!(fact.output(), alias.compact);
        assert!(kernel.equivalent(raw, alias.compact).unwrap());
        assert!(
            kernel.arena.len() > before,
            "aliases are a disposable suffix"
        );
    }

    #[test]
    fn compact_logical_tree_is_transactional_on_bad_input() {
        let manifest: init::Manifest = serde_json::from_str(INIT_FIXTURE).unwrap();
        let init = init::compile(&manifest).unwrap();
        let mut kernel = Kernel::with_init(&init);
        let before = kernel.arena.clone();
        let missing = Ref::new(i32::try_from(kernel.arena.len() + 1).unwrap()).unwrap();
        assert!(kernel.compact_logical_tree(&init, missing).is_err());
        assert_eq!(kernel.arena, before);
    }

    #[test]
    fn constructs_higher_kinded_rows() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let arrow = kernel.kind_arr(star, star).unwrap();
        let family = kernel.ty_fv(0, arrow).unwrap();
        let argument = kernel.ty_fv(1, star).unwrap();
        let application = kernel.ty_app(family, argument).unwrap();
        let abstraction = kernel.ty_lam(argument, application).unwrap();

        assert_eq!(kernel.classifier(application).unwrap(), star);
        assert_eq!(kernel.arena().tag(abstraction), Some(Tag::Ty(TyTag::Lam)));
        assert_eq!(
            kernel.arena().tag(kernel.classifier(abstraction).unwrap()),
            Some(Tag::Kind(KindTag::Arr))
        );
    }

    #[test]
    fn equality_cycles_have_a_canonical_member_and_can_be_compressed() {
        let mut kernel = Kernel::new();
        let left = kernel.star().unwrap();
        let right = kernel.star().unwrap();
        assert!(
            kernel
                .arena
                .set_eq_column(EqColumn::Semantic, left, Some(right))
        );
        assert!(
            kernel
                .arena
                .set_eq_column(EqColumn::Semantic, right, Some(left))
        );

        assert_eq!(kernel.find(left).unwrap(), left);
        assert_eq!(kernel.find(right).unwrap(), left);
        assert_eq!(kernel.find_mut(right).unwrap(), left);
        assert_eq!(kernel.arena.eq(left), None);
        assert_eq!(kernel.arena.eq(right), Some(left));
    }

    #[test]
    fn conversion_compression_preserves_the_root_classifier() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let left = kernel.bool_ty(star).unwrap();
        let middle = kernel.bool_ty(star).unwrap();
        let right = kernel.bool_ty(star).unwrap();

        kernel
            .union_in::<Infallible>(EqColumn::Conv, middle, right)
            .unwrap();
        kernel
            .union_in::<Infallible>(EqColumn::Conv, left, middle)
            .unwrap();

        for reference in [left, middle, right] {
            assert_eq!(kernel.classifier(reference).unwrap(), star);
            assert_eq!(kernel.find_conv_mut::<Infallible>(reference).unwrap(), left);
            assert_eq!(kernel.classifier(reference).unwrap(), star);
        }
        assert_eq!(kernel.arena.conv(left), Some(star));
        assert_eq!(kernel.arena.conv(middle), Some(left));
        assert_eq!(kernel.arena.conv(right), Some(left));
    }

    #[test]
    fn conversion_union_replaces_an_equivalent_distinct_classifier_atomically() {
        let mut kernel = Kernel::new();
        let first_star = kernel.star().unwrap();
        let second_star = kernel.star().unwrap();
        kernel
            .union_in::<Infallible>(EqColumn::Semantic, first_star, second_star)
            .unwrap();

        let left = kernel.bool_ty(first_star).unwrap();
        let right = kernel.bool_ty(second_star).unwrap();
        kernel
            .union_in::<Infallible>(EqColumn::Conv, left, right)
            .unwrap();

        for reference in [left, right] {
            assert_eq!(kernel.classifier(reference).unwrap(), first_star);
            assert_eq!(kernel.find_conv_mut::<Infallible>(reference).unwrap(), left);
            assert_eq!(kernel.classifier(reference).unwrap(), first_star);
        }
        assert_eq!(kernel.arena.conv(left), Some(first_star));
        assert_eq!(kernel.arena.conv(right), Some(left));
        kernel
            .bool(right, true)
            .expect("the inherited type remains usable");

        let mut bytes = Vec::new();
        crate::wire::serialize(kernel.arena(), &mut bytes).unwrap();
        let decoded = crate::wire::deserialize(bytes.as_slice()).unwrap();
        assert_eq!(decoded.sort(left), Some(first_star));
        assert_eq!(decoded.sort(right), Some(first_star));

        let unrelated_kind = kernel.kind_arr(first_star, first_star).unwrap();
        let incompatible = kernel.ty_fv(0, unrelated_kind).unwrap();
        let before = kernel.arena.clone();
        assert!(matches!(
            kernel.union_in::<Infallible>(EqColumn::Conv, left, incompatible),
            Err(KernelError::ClassifierMismatch { .. })
        ));
        assert_eq!(kernel.arena, before, "a rejected union mutated the arena");
    }

    #[test]
    fn equality_union_preflights_both_paths_before_compression() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let first = kernel.bool_ty(star).unwrap();
        let first_parent = kernel.bool_ty(star).unwrap();
        let second = kernel.bool_ty(star).unwrap();
        let boolean = kernel.bool(first, true).unwrap();

        assert!(
            kernel
                .arena
                .set_eq_column(EqColumn::Semantic, first, Some(first_parent))
        );
        assert!(
            kernel
                .arena
                .set_eq_column(EqColumn::Semantic, second, Some(boolean))
        );
        let before = kernel.arena.clone();

        assert!(
            kernel
                .union_in::<Infallible>(EqColumn::Semantic, first, second)
                .is_err()
        );
        assert_eq!(kernel.arena, before);
    }

    #[test]
    fn equality_union_recomputes_the_right_path_and_keeps_the_least_root() {
        let mut kernel = Kernel::new();
        let root = kernel.star().unwrap();
        let middle = kernel.star().unwrap();
        let leaf = kernel.star().unwrap();

        assert!(
            kernel
                .arena
                .set_eq_column(EqColumn::Semantic, leaf, Some(middle))
        );
        assert!(
            kernel
                .arena
                .set_eq_column(EqColumn::Semantic, middle, Some(root))
        );

        kernel
            .union_in::<Infallible>(EqColumn::Semantic, leaf, middle)
            .unwrap();
        for reference in [root, middle, leaf] {
            assert_eq!(kernel.find_mut(reference).unwrap(), root);
        }
        assert_eq!(kernel.arena.eq(root), None);
        assert_eq!(kernel.arena.eq(middle), Some(root));
        assert_eq!(kernel.arena.eq(leaf), Some(root));
    }

    #[test]
    fn kind_conversion_union_preflights_both_paths_before_compression() {
        let mut kernel = Kernel::new();
        let first = kernel.star().unwrap();
        let first_parent = kernel.star().unwrap();
        let second = kernel.star().unwrap();
        let ty = kernel.bool_ty(first).unwrap();

        assert!(
            kernel
                .arena
                .set_eq_column(EqColumn::Conv, first, Some(first_parent))
        );
        assert!(kernel.arena.set_eq_column(EqColumn::Conv, second, Some(ty)));
        let before = kernel.arena.clone();

        assert!(
            kernel
                .union_in::<Infallible>(EqColumn::Conv, first, second)
                .is_err()
        );
        assert_eq!(kernel.arena, before);
    }

    #[test]
    fn imported_rows_are_local_proxies_with_explicit_premises() {
        let mut imported = Kernel::new();
        let imported_star = imported.star().unwrap();
        let imported_bool_ty = imported.bool_ty(imported_star).unwrap();
        let imported_truth = imported.bool(imported_bool_ty, true).unwrap();
        let table = Table::from_arena(imported.into_arena()).unwrap();

        let mut owner = Kernel::new();
        let star = owner.star().unwrap();
        let bool_ty = owner.bool_ty(star).unwrap();
        let source = owner
            .import_link(Link {
                format: LinkFormat::Cbor,
                blake3: table.addr(),
            })
            .unwrap();
        let mut resolver = OneTable(table);
        let proxy = owner
            .tm_ref(&mut resolver, source, imported_truth, bool_ty)
            .unwrap();

        assert_eq!(owner.arena().tag(proxy), Some(Tag::Tm(TmTag::Ref)));
        assert_eq!(
            owner.arena().ambient_context().to_rows(),
            vec![LitVec::from_slice(&[Lit::positive(1)])]
        );
        assert_eq!(
            owner.arena().ambient_predicates(),
            &[AmbPred::HolSort {
                src: source,
                ix: imported_truth,
                sort: bool_ty,
            }]
        );
    }

    #[test]
    fn copies_empty_and_repeated_roots_without_imports() {
        let mut source = Kernel::new();
        let star = source.star().unwrap();
        let bool_ty = source.bool_ty(star).unwrap();
        let truth = source.bool(bool_ty, true).unwrap();
        let mut destination = Kernel::new();

        assert!(
            destination
                .copy_terms_from(&source, &[])
                .unwrap()
                .is_empty()
        );
        let copied = destination
            .copy_terms_from(&source, &[truth, truth])
            .unwrap();

        assert_eq!(copied.len(), 3);
        assert_eq!(copied.roots(), &[copied.get(truth).unwrap(); 2]);
        assert!(destination.imports().is_empty());
        assert_eq!(destination.len(), 3);
    }

    #[test]
    fn copies_the_union_of_diamonds_and_preserves_sharing() {
        let mut source = Kernel::new();
        let star = source.star().unwrap();
        let bool_ty = source.bool_ty(star).unwrap();
        let variable = source.tm_fv(7, bool_ty).unwrap();
        let left = source.eq(bool_ty, variable, variable).unwrap();
        let right = source.eq(bool_ty, variable, variable).unwrap();
        let mut destination = Kernel::new();

        let copied = destination
            .copy_terms_from(&source, &[left, right])
            .unwrap();
        let copied_variable = copied.get(variable).unwrap();
        let copied_bool_ty = copied.get(bool_ty).unwrap();
        let left_children = destination
            .children(copied.get(left).unwrap())
            .unwrap()
            .collect::<Vec<_>>();
        let right_children = destination
            .children(copied.get(right).unwrap())
            .unwrap()
            .collect::<Vec<_>>();

        assert_eq!(
            left_children,
            [copied_bool_ty, copied_variable, copied_variable]
        );
        assert_eq!(
            right_children,
            [copied_bool_ty, copied_variable, copied_variable]
        );
        assert_eq!(copied.len(), 5);
        drop(source);
        assert_eq!(destination.category(copied.roots()[0]).unwrap(), Sort::Tm);
    }

    #[test]
    fn copies_compact_logical_opcodes_between_kernels() {
        let mut source = Kernel::new();
        let star = source.star().unwrap();
        let bool_ty = source.bool_ty(star).unwrap();
        let p = source.tm_fv(1, bool_ty).unwrap();
        let q = source.tm_fv(2, bool_ty).unwrap();
        let not_p = source.op1(Op1::Not, p).unwrap();
        let implication = source.op2(Op2::Imp, not_p, q).unwrap();
        let mut destination = Kernel::new();

        let copied = destination.copy_term_from(&source, implication).unwrap();
        let copied_not_p = copied.get(not_p).unwrap();
        let copied_implication = copied.get(implication).unwrap();

        assert_eq!(destination.arena().op1(copied_not_p), Some(Op1::Not));
        assert_eq!(destination.arena().op2(copied_implication), Some(Op2::Imp));
        assert_eq!(
            destination
                .children(copied_implication)
                .unwrap()
                .collect::<Vec<_>>(),
            [copied_not_p, copied.get(q).unwrap()]
        );
    }

    #[test]
    fn lowered_copy_recursively_removes_logical_opcodes_and_preserves_sharing() {
        let manifest: init::Manifest = serde_json::from_str(INIT_FIXTURE).unwrap();
        let init = init::compile(&manifest).unwrap();
        let bool_ty = init.get("bool").unwrap();
        let mut source = Kernel::with_init(&init);
        let p = source.tm_fv(21, bool_ty).unwrap();
        let not_p = source.op1(Op1::Not, p).unwrap();
        let repeated = source.op2(Op2::And, not_p, not_p).unwrap();
        let implication = source.op2(Op2::Imp, repeated, not_p).unwrap();
        let equation = source.eq(bool_ty, implication, implication).unwrap();
        let mut destination = Kernel::with_init(&init);

        let copied = destination
            .copy_term_lowered_from(&init, &source, equation)
            .unwrap();
        let copied_not = copied.get(not_p).unwrap();
        let not_definition = init.get(Op1::Not.name()).unwrap();
        assert_eq!(
            destination
                .children(copied_not)
                .unwrap()
                .collect::<Vec<_>>(),
            [not_definition, copied.get(p).unwrap()]
        );
        let copied_repeated = copied.get(repeated).unwrap();
        let repeated_children = destination
            .children(copied_repeated)
            .unwrap()
            .collect::<Vec<_>>();
        assert_eq!(repeated_children[1], copied_not);

        for position in (init.arena().len() + 1)..=destination.len() {
            let reference = Ref::new(i32::try_from(position).unwrap()).unwrap();
            assert!(!matches!(
                destination.tag(reference),
                Some(Tag::Tm(TmTag::Op1 | TmTag::Op2))
            ));
        }
        assert_eq!(destination.category(copied.roots()[0]).unwrap(), Sort::Tm);
    }

    #[test]
    fn lowered_copy_requires_the_exact_shared_prefix_transactionally() {
        let manifest: init::Manifest = serde_json::from_str(INIT_FIXTURE).unwrap();
        let init = init::compile(&manifest).unwrap();
        let truth = init.get("true").unwrap();
        let mut source = Kernel::with_init(&init);
        let compact = source.op1(Op1::Not, truth).unwrap();
        let mut destination = Kernel::new();
        let existing = destination.star().unwrap();
        let before = destination.arena().clone();

        assert!(matches!(
            destination.copy_term_lowered_from(&init, &source, compact),
            Err(KernelError::InitPrefixMismatch)
        ));
        assert_eq!(destination.arena(), &before);
        assert_eq!(destination.category(existing).unwrap(), Sort::Kind);
    }

    #[test]
    fn lowered_object_copy_accepts_kind_type_and_term_roots_together() {
        let manifest: init::Manifest = serde_json::from_str(INIT_FIXTURE).unwrap();
        let init = init::compile(&manifest).unwrap();
        let star = init.get("star").unwrap();
        let bool_ty = init.get("bool").unwrap();
        let mut source = Kernel::with_init(&init);
        let kind = source.kind_arr(star, star).unwrap();
        let family = source.ty_fv(31, kind).unwrap();
        let truth = source.bool(bool_ty, true).unwrap();
        let mut destination = Kernel::with_init(&init);

        let copied = destination
            .copy_objects_lowered_from(&init, &source, &[kind, family, truth])
            .unwrap();
        assert_eq!(
            copied
                .roots()
                .iter()
                .map(|reference| destination.category(*reference).unwrap())
                .collect::<Vec<_>>(),
            [Sort::Kind, Sort::Ty, Sort::Tm]
        );
    }

    #[test]
    fn checked_prefix_forks_preserve_the_complete_snapshot_identity() {
        let mut original = Kernel::new();
        let star = original.star().unwrap();
        let bool_ty = original.bool_ty(star).unwrap();
        let truth = original.bool(bool_ty, true).unwrap();
        original.add_axiom(AX_INF).unwrap();
        original.add_context(truth).unwrap();
        let prefix = original.into_checked_prefix();
        let mut left = prefix.kernel();
        let right = prefix.kernel();

        assert_eq!(left.arena(), prefix.arena());
        assert_eq!(right.arena(), prefix.arena());
        assert_eq!(
            left.init_prefix(),
            Some((prefix.arena().addr(), prefix.arena().len()))
        );
        assert_eq!(left.copy_term_from(&right, truth).unwrap().roots(), [truth]);
        assert_eq!(left.arena(), prefix.arena());
    }

    #[test]
    fn copy_rejects_bad_reachable_syntax_atomically() {
        let mut source = Kernel::new();
        let star = source.star().unwrap();
        let bool_ty = source.bool_ty(star).unwrap();
        let self_ref = Ref::new(3).unwrap();
        source
            .arena
            .push_row(Row::new(Node::App(self_ref, self_ref)), Some(bool_ty));
        let mut destination = Kernel::new();
        let existing = destination.star().unwrap();
        let before = destination.len();

        assert!(matches!(
            destination.copy_term_from(&source, self_ref),
            Err(KernelError::CyclicSyntax { .. })
        ));
        assert_eq!(destination.len(), before);
        assert_eq!(destination.category(existing).unwrap(), Sort::Kind);
    }

    #[test]
    fn copy_rejects_dangling_sort_invalid_and_imported_rows_atomically() {
        let mut destination = Kernel::new();

        let mut dangling = Kernel::new();
        let missing = Ref::new(2).unwrap();
        let root = dangling
            .arena
            .push_row(Row::new(Node::Bool(true)), Some(missing))
            .unwrap();
        assert!(matches!(
            destination.copy_term_from(&dangling, root),
            Err(KernelError::MissingDefinition { .. })
        ));

        let mut invalid = Kernel::new();
        let star = invalid.star().unwrap();
        let root = invalid
            .arena
            .push_row(Row::new(Node::Bool(true)), Some(star))
            .unwrap();
        assert!(matches!(
            destination.copy_term_from(&invalid, root),
            Err(KernelError::WrongCategory { .. })
        ));

        let mut mistyped_equality = Kernel::new();
        let star = mistyped_equality.star().unwrap();
        let bool_ty = mistyped_equality.bool_ty(star).unwrap();
        let other_ty = mistyped_equality.ty_fv(1, star).unwrap();
        let operand = mistyped_equality.tm_fv(2, bool_ty).unwrap();
        let root = mistyped_equality
            .arena
            .push_row(
                Row::new(Node::Eq(other_ty, operand, operand)),
                Some(bool_ty),
            )
            .unwrap();
        assert!(matches!(
            destination.copy_term_from(&mistyped_equality, root),
            Err(KernelError::ClassifierMismatch { .. })
        ));

        let mut imported = Kernel::new();
        let source_id = imported.import_literal(Arena::empty()).unwrap();
        let root = imported
            .arena
            .push_row(
                Row::new(Node::TmRef {
                    src: source_id,
                    ix: Ref::new(1).unwrap(),
                }),
                None,
            )
            .unwrap();
        assert!(matches!(
            destination.copy_term_from(&imported, root),
            Err(KernelError::ImportedProxy { .. })
        ));
        assert!(destination.is_empty());
    }
}
