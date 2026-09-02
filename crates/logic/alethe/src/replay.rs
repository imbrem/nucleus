//! Proof-producing replay of `QF_UF` Alethe proofs through checked HOL
//! operations, plus a checked-but-unproving lowering of `QF_UFLIA` input.
//!
//! # The `QF_UFLIA` lowering states no arithmetic
//!
//! This tree has no HOL integer theory: `crates/logic/hol` and
//! `crates/logic/hol-derived` know Peano naturals with addition and
//! multiplication, no order relation, and no subtraction, and `theories/`
//! holds only the checked Boolean init package. So `Int` and `Real` lower to
//! ordinary uninterpreted type constants, numerals lower to fresh
//! uninterpreted term constants interned on their exact spelling, and the
//! arithmetic operators lower to monomorphic uninterpreted function constants.
//! Nothing relates them, which is why every arithmetic Alethe rule fails
//! closed with [`Error::ArithmeticTheoryMissing`] and why [`lower_qf_uflia`]
//! returns a [`Lowering`] that deliberately exposes no theorem. Issue 1208
//! tracks the checked arithmetic that would change this.
//!
//! # The frontend performs no arithmetic normalization
//!
//! Every syntactic distinction cvc5 draws survives lowering: `-3` and `(- 3)`
//! are different rows, `5` and `5/1` are different rows in different sorts,
//! `(> a b)` is not rewritten to `(< b a)`, and nothing is constant-folded.
//! cvc5 relates those spellings with its own `evaluate` and `arith-elim-*`
//! steps, so identifying them here would silently assume the arithmetic facts
//! those steps are supposed to justify. For the same reason a non-reduced
//! rational spelling such as `2/4` interns as its own constant instead of
//! being reduced: that can only cause a false rejection, never a false
//! acceptance, and reducing it would need bignum arithmetic this crate does
//! not carry.
//!
//! # Subproof scoping diverges from the Alethe specification
//!
//! Alethe Definition 6.1 forbids a subproof step from citing a premise
//! outside its own subproof. cvc5 1.3.4 emits such references constantly, so
//! this replayer permits them; that is sound in a sequent setting because the
//! outer premise's own antecedent merges into the frame's and survives
//! discharge. The opposite direction, an outer step citing a step inside a
//! closed frame, is rejected with [`Error::OutOfScopePremise`].
//!
//! # This module adds no assumption, capability, or wire commitment
//!
//! The rows it emits are `ty.fv`, `ty.arr`, `tm.fv`, `tm.app`, `tm.eq`,
//! `tm.op1` and `tm.op2`: pre-existing v1 tags the `QF_UF` path already
//! emitted. No compact literal row, no builtin-table entry, no new function on
//! the `arena` or `kernel` resources, no change to the checked init package,
//! no new crate dependency, and nothing added to the trusted computing base.
//! Replacing the uninterpreted numeric vocabulary with a real integer theory
//! is three body swaps inside private `Replayer` methods, so the migration is
//! wire-free.

use std::collections::{BTreeSet, HashMap, HashSet};

use covalence_data_sexpr::{Atom, Expr, ExprKind, Repr, SpannedRepr};
use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{
    AmbPred, Kernel, KernelError, Lit, Ref, SynRel, Tag, ThmId, TmTag,
    builtin::{Op1, Op2},
    init,
};
use covalence_logic_hol_derived::{
    Conditional, ConditionalError, EqualityError, SyntaxError, conditional, conditional_when_false,
    conditional_when_true, equality_symmetry, equality_transitivity, join_same_syntax,
};

use crate::{AletheCommand, AletheProof, SmtCommand, SmtProblem};

/// One SMT-LIB logic this crate reads.
///
/// The allowlist is exact: input naming any other logic fails closed, and each
/// entry has its own entry point, so widening one never widens another.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Logic {
    /// Quantifier-free uninterpreted functions, replayed to a refutation.
    QfUf,
    /// Quantifier-free linear integer arithmetic with uninterpreted functions,
    /// lowered but never certified. See [`lower_qf_uflia`].
    QfUflia,
}

impl Logic {
    /// Returns the logic named by an SMT-LIB `set-logic` argument.
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "QF_UF" => Some(Self::QfUf),
            "QF_UFLIA" => Some(Self::QfUflia),
            _ => None,
        }
    }

    /// Returns the SMT-LIB spelling of this logic.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::QfUf => "QF_UF",
            Self::QfUflia => "QF_UFLIA",
        }
    }
}

/// A checked refutation bound to one exact normalized SMT assertion set.
#[derive(Debug)]
pub struct Refutation {
    kernel: Kernel,
    logic: Logic,
    theorem: ThmId,
    assertions: Vec<Lit>,
}

/// The first arithmetic Alethe rule that stopped a `QF_UFLIA` lowering.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArithmeticGap {
    step: String,
    rule: String,
    domain: String,
}

impl ArithmeticGap {
    /// Returns the Alethe step index that could not be checked.
    #[must_use]
    pub fn step(&self) -> &str {
        &self.step
    }

    /// Returns the Alethe rule name that needs arithmetic.
    #[must_use]
    pub fn rule(&self) -> &str {
        &self.rule
    }

    /// Returns the arithmetic domain that rule reasons in.
    #[must_use]
    pub fn domain(&self) -> &str {
        &self.domain
    }
}

/// A checked lowering of a `QF_UFLIA` problem and proof that proves nothing.
///
/// This type has no theorem accessor and no conversion into a [`Refutation`],
/// on purpose. The lowering is faithful, but no HOL theory in this tree
/// relates the constants it emits, so the proof always stops at an arithmetic
/// rule; [`Self::arithmetic_gap`] names the first one. Issue 1208 tracks the
/// checked arithmetic that would let this become a refutation.
#[derive(Debug)]
pub struct Lowering {
    kernel: Kernel,
    logic: Logic,
    assertions: Vec<Lit>,
    steps: usize,
    gap: ArithmeticGap,
}

impl Lowering {
    /// Returns the kernel holding every lowered term and checked step.
    #[must_use]
    pub const fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// Returns the logic this lowering was accepted under.
    #[must_use]
    pub const fn logic(&self) -> Logic {
        self.logic
    }

    /// Returns the lowered problem assertions in source order.
    #[must_use]
    pub fn assertions(&self) -> &[Lit] {
        &self.assertions
    }

    /// Returns how many Alethe assumptions and steps were checked before the
    /// arithmetic gap.
    #[must_use]
    pub const fn steps(&self) -> usize {
        self.steps
    }

    /// Returns the first arithmetic rule this build cannot check.
    #[must_use]
    pub const fn arithmetic_gap(&self) -> &ArithmeticGap {
        &self.gap
    }
}

/// Checked context offered to a user-defined handler for an unknown rule.
///
/// Terms and clauses have already been lowered into `kernel`'s arena. The
/// replay engine independently checks the returned theorem against `clause`.
pub struct RuleRequest<'a> {
    /// Kernel containing all lowered terms and premise theorems.
    pub kernel: &'a mut Kernel,
    /// Kernel Boolean type.
    pub bool_ty: Ref,
    /// Alethe rule name not implemented by the default replayer.
    pub rule: &'a str,
    /// Lowered expected conclusion clause.
    pub clause: &'a [Lit],
    /// Checked premise theorem indices.
    pub premises: &'a [ThmId],
    /// Untrusted rule arguments from the parsed proof.
    ///
    /// For `rule == "rare_rewrite"`, `args[0]` is the RARE rewrite name and
    /// the rest are its untrusted operands. Read the terms a handler needs off
    /// `clause` and `premises`, never by rebuilding them from these.
    pub args: &'a [Expr],
}

/// Optional userspace fallback for Alethe rules outside the default set.
pub trait RuleHandler {
    /// Attempts to derive the requested clause with ordinary checked kernel
    /// operations. Returning `None` preserves the default unsupported-rule
    /// error.
    ///
    /// # Errors
    ///
    /// Returns [`Error`] when the handler recognizes the rule but rejects its
    /// arguments or cannot construct checked evidence.
    fn apply(&mut self, request: RuleRequest<'_>) -> Result<Option<ThmId>, Error>;
}

struct RejectUnknownRules;

impl RuleHandler for RejectUnknownRules {
    fn apply(&mut self, _request: RuleRequest<'_>) -> Result<Option<ThmId>, Error> {
        Ok(None)
    }
}

impl Refutation {
    /// Returns the checked kernel containing the refutation theorem.
    #[must_use]
    pub const fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// Returns the logic this refutation was accepted under.
    #[must_use]
    pub const fn logic(&self) -> Logic {
        self.logic
    }

    /// Returns the theorem whose premises are exactly the normalized problem
    /// assertions and whose conclusion is empty.
    #[must_use]
    pub const fn theorem(&self) -> ThmId {
        self.theorem
    }

    /// Returns the translated assertions in source order.
    #[must_use]
    pub fn assertions(&self) -> &[Lit] {
        &self.assertions
    }

    /// Consumes the result and returns its checked kernel.
    #[must_use]
    pub fn into_kernel(self) -> Kernel {
        self.kernel
    }
}

/// Why a `QF_UF` problem or Alethe derivation was rejected.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum Error {
    /// The embedded checked Boolean init manifest was invalid JSON.
    #[snafu(display("could not decode the checked Boolean init manifest: {source}"))]
    InitJson {
        source: covalence_lib_json::serde_json::Error,
    },
    /// The embedded checked Boolean init manifest was rejected.
    #[snafu(display("could not compile the checked Boolean init manifest: {source}"))]
    Init { source: init::CompileError },
    /// A checked HOL operation rejected the derivation.
    #[snafu(transparent)]
    Kernel { source: KernelError },
    /// A userspace-derived equality rule was rejected.
    #[snafu(transparent)]
    Equality { source: EqualityError },
    /// A structural syntax certificate was rejected.
    #[snafu(transparent)]
    Syntax { source: SyntaxError },
    /// A userspace-derived polymorphic conditional was rejected.
    #[snafu(transparent)]
    Conditional { source: ConditionalError },
    /// Input uses a command, rule, sort, or term this replayer does not read.
    #[snafu(display("unsupported SMT-LIB or Alethe input: {message}"))]
    Unsupported { message: String },
    /// Input is structurally inconsistent or names absent data.
    #[snafu(display("malformed SMT-LIB or Alethe input: {message}"))]
    Malformed { message: String },
    /// A proof assumption is not one of the requested problem assertions.
    #[snafu(display("Alethe assumption is not asserted by the requested problem"))]
    UnassertedAssumption,
    /// A checked rule derived a clause other than the one stated by Alethe.
    #[snafu(display("Alethe step {step:?} derived clause {actual:?}, expected {expected:?}"))]
    ClauseMismatch {
        step: String,
        actual: Vec<Lit>,
        expected: Vec<Lit>,
    },
    /// The proof ended without an empty clause.
    #[snafu(display("Alethe proof does not derive the empty clause"))]
    NoRefutation,
    /// A rule states arithmetic that no HOL theory in this tree provides.
    ///
    /// This is deliberately distinct from [`Error::Unsupported`]: it means the
    /// rule is understood and its requirement is precisely known, and that
    /// this build cannot meet it. Issue 1208 tracks the checked arithmetic.
    #[snafu(display(
        "Alethe step {step:?} rule {rule:?} needs checked {domain} arithmetic, which no HOL theory in this tree provides; issue 1208 tracks it"
    ))]
    ArithmeticTheoryMissing {
        /// Alethe step index that stated the rule.
        step: String,
        /// Alethe rule or rare-rewrite name.
        rule: String,
        /// Arithmetic domain the rule reasons in.
        domain: String,
    },
    /// A `QF_UFLIA` proof replayed to its end, which this build must not
    /// certify because it has no checked arithmetic to have used.
    #[snafu(display(
        "QF_UFLIA lowering reached the end of the proof without an arithmetic gap, which this build must not certify; issue 1208 tracks it"
    ))]
    NoArithmeticGap,
    /// A subproof frame is structurally inconsistent.
    #[snafu(display("Alethe subproof frame {frame:?} is malformed: {message}"))]
    Frame {
        /// Anchor step index naming the frame.
        frame: String,
        /// What was inconsistent about it.
        message: String,
    },
    /// A step names a premise whose subproof frame has already closed.
    #[snafu(display(
        "Alethe step {step:?} names premise {premise:?} from a closed subproof frame"
    ))]
    OutOfScopePremise {
        /// Step naming the premise.
        step: String,
        /// Premise index that has left scope.
        premise: String,
    },
    /// A term nests more deeply than the replayer lowers.
    #[snafu(display("term nesting exceeds the replay budget of {limit} levels"))]
    TermTooDeep {
        /// Greatest nesting depth the replayer lowers.
        limit: usize,
    },
}

/// Greatest term nesting depth `Replayer` lowers.
///
/// Lowering recurses once per nesting level over untrusted problem and proof
/// text, so the budget keeps a deeply nested term a rejected input rather than
/// an aborted process.
const MAX_TERM_DEPTH: usize = 256;

#[derive(Clone, Copy, Debug)]
struct Term {
    reference: Ref,
    literal: Lit,
}

impl Term {
    fn positive(reference: Ref) -> Self {
        Self {
            reference,
            literal: Lit::positive(reference.get()),
        }
    }

    fn literal(self) -> Lit {
        self.literal
    }
}

/// Which reader is lowering a term.
///
/// Integer lexing is identical in both: cvc5 1.3.4 accepts a bare `-3` as
/// SMT-LIB input by default and treats it as an integer token, so the only
/// competing reading is "undeclared symbol", which is an error rather than a
/// different value. The genuine dialect difference is that the Alethe printer
/// emits rational literals and `Real`-sorted terms that `QF_UFLIA` input
/// cannot contain.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Dialect {
    /// The SMT-LIB problem, which has no rationals.
    SmtLib,
    /// The Alethe proof, which has rationals.
    Alethe,
}

/// Which numeral grammar an atom spelling matches.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NumeralKind {
    /// `-?(0|[1-9][0-9]*)`.
    Integer,
    /// `-?(0|[1-9][0-9]*)/[1-9][0-9]*`.
    Rational,
}

/// One of the two numeric sorts an arithmetic operand may carry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NumericSort {
    Int,
    Real,
}

/// The monomorphic arithmetic operator constants of one numeric sort.
///
/// The kernel gives `tm_fv` one fixed type, and cvc5 uses `+`, `-` and `*` at
/// both `Int` and `Real` inside a single proof, so there is one set per sort
/// rather than a polymorphic head.
#[derive(Clone, Copy, Debug)]
struct Operators {
    add: Ref,
    sub: Ref,
    neg: Ref,
    mul: Ref,
    lt: Ref,
    le: Ref,
    gt: Ref,
    ge: Ref,
}

/// The uninterpreted vocabulary that stands in for arithmetic.
///
/// Numerals are interned on their exact accepted spelling, so two occurrences
/// of one spelling are literally the same row and join by reflexivity, while
/// two spellings get distinct `tm.fv` names that both `require_same_syntax`
/// and `join_same_syntax` discriminate. The name always comes from the
/// freshness counter and never from the value: deriving it from the value is
/// the one way two different numerals could become the same row.
struct Numeric {
    int_ty: Ref,
    real_ty: Ref,
    int: Operators,
    real: Operators,
    to_real: Ref,
    to_int: Ref,
    int_numerals: HashMap<String, Ref>,
    rational_numerals: HashMap<String, Ref>,
}

/// One open `anchor` scope and the assumptions it must discharge.
struct Frame {
    /// The anchor's `:step` index. Only a step with this index closes it.
    id: String,
    /// Frame-local assumptions in introduction order.
    assumptions: Vec<(String, Lit)>,
    /// Every index bound while this frame was open, dropped on close.
    bound: Vec<String>,
    /// Theorem of the last direct child step, the frame's conclusion.
    last: Option<ThmId>,
    /// Set by the first child step; further `assume` commands then fail.
    sealed: bool,
}

struct Replayer {
    kernel: Kernel,
    init: init::Compiled,
    star: Ref,
    bool_ty: Ref,
    logic: Logic,
    /// Ambient predicates present right after `Kernel::with_init`.
    ///
    /// `check_exact_goal` inspects only the refutation's own sequent, so a
    /// rule handler holding `&mut Kernel` could otherwise reach `tm_ref` or
    /// `import_literal`, assume an unchecked `hol.sort` predicate, and pass
    /// every other gate. Requiring this snapshot unchanged closes that.
    ambient: Vec<AmbPred>,
    numeric: Option<Numeric>,
    dialect: Dialect,
    next_name: u64,
    sorts: HashMap<String, Ref>,
    functions: HashMap<String, Term>,
    locals: Vec<HashMap<String, Term>>,
    conditionals: Vec<(Ref, Ref, Ref, Conditional)>,
    named: HashMap<String, Term>,
    assertions: Vec<Lit>,
    assertion_terms: Vec<Term>,
    assertion_transports: Vec<(Ref, Ref)>,
    steps: HashMap<String, ThmId>,
    frames: Vec<Frame>,
    /// Every index ever bound, never pruned, so uniqueness outlives a frame.
    seen: HashSet<String>,
}

impl Replayer {
    fn new(logic: Logic) -> Result<Self, Error> {
        const MANIFEST: &str = include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../../theories/init-boolean.checked.json"
        ));
        let manifest = covalence_lib_json::serde_json::from_str(MANIFEST)
            .map_err(|source| Error::InitJson { source })?;
        let init = init::compile(&manifest).map_err(|source| Error::Init { source })?;
        let kernel = Kernel::with_init(&init);
        let star = init.get("star").ok_or_else(|| Error::Malformed {
            message: "Boolean init has no star definition".to_owned(),
        })?;
        let bool_ty = init.get("bool").ok_or_else(|| Error::Malformed {
            message: "Boolean init has no bool definition".to_owned(),
        })?;
        let ambient = kernel.arena().ambient_predicates().to_vec();
        Ok(Self {
            kernel,
            init,
            star,
            bool_ty,
            logic,
            ambient,
            numeric: None,
            dialect: Dialect::SmtLib,
            next_name: 0,
            sorts: HashMap::new(),
            functions: HashMap::new(),
            locals: Vec::new(),
            conditionals: Vec::new(),
            named: HashMap::new(),
            assertions: Vec::new(),
            assertion_terms: Vec::new(),
            assertion_transports: Vec::new(),
            steps: HashMap::new(),
            frames: Vec::new(),
            seen: HashSet::new(),
        })
    }

    /// Returns the numeric vocabulary, which only `QF_UFLIA` allocates.
    fn numeric(&self) -> Result<&Numeric, Error> {
        self.numeric.as_ref().ok_or_else(|| Error::Unsupported {
            message: format!(
                "arithmetic sorts and terms require QF_UFLIA, not {}",
                self.logic.name()
            ),
        })
    }

    fn fresh_constant(&mut self, ty: Ref) -> Result<Ref, Error> {
        let name = self.name()?;
        Ok(self.kernel.tm_fv(name, ty)?)
    }

    fn binary_ty(&mut self, domain: Ref, codomain: Ref) -> Result<Ref, Error> {
        let inner = self.kernel.ty_arr(domain, codomain)?;
        Ok(self.kernel.ty_arr(domain, inner)?)
    }

    fn allocate_operators(&mut self, sort: Ref) -> Result<Operators, Error> {
        let binary = self.binary_ty(sort, sort)?;
        let unary = self.kernel.ty_arr(sort, sort)?;
        let relation = self.binary_ty(sort, self.bool_ty)?;
        // Allocation order is part of the arena layout; see `allocate_numeric`.
        let add = self.fresh_constant(binary)?;
        let sub = self.fresh_constant(binary)?;
        let neg = self.fresh_constant(unary)?;
        let mul = self.fresh_constant(binary)?;
        let lt = self.fresh_constant(relation)?;
        let le = self.fresh_constant(relation)?;
        let gt = self.fresh_constant(relation)?;
        let ge = self.fresh_constant(relation)?;
        Ok(Operators {
            add,
            sub,
            neg,
            mul,
            lt,
            le,
            gt,
            ge,
        })
    }

    /// Allocates the `QF_UFLIA` numeric vocabulary in one fixed order.
    ///
    /// The order is index-stable on purpose: allocating eagerly in the
    /// `set-logic` arm makes every arena row index a function of the accepted
    /// logic alone, so a `QF_UF` arena is byte-identical to one built before
    /// this vocabulary existed. Reordering these calls changes every row index
    /// a test pins.
    fn allocate_numeric(&mut self) -> Result<(), Error> {
        if self.numeric.is_some() {
            return Err(Error::Malformed {
                message: "duplicate set-logic command".to_owned(),
            });
        }
        // `Int` and `Real` are built exactly like `(declare-sort U 0)`: an
        // uninterpreted type constant, needing no new kernel capability, no
        // new row tag and no init-package entry.
        let int_name = self.name()?;
        let int_ty = self.kernel.ty_fv(int_name, self.star)?;
        let real_name = self.name()?;
        let real_ty = self.kernel.ty_fv(real_name, self.star)?;
        let int = self.allocate_operators(int_ty)?;
        let real = self.allocate_operators(real_ty)?;
        let to_real_ty = self.kernel.ty_arr(int_ty, real_ty)?;
        let to_real = self.fresh_constant(to_real_ty)?;
        let to_int_ty = self.kernel.ty_arr(real_ty, int_ty)?;
        let to_int = self.fresh_constant(to_int_ty)?;
        self.numeric = Some(Numeric {
            int_ty,
            real_ty,
            int,
            real,
            to_real,
            to_int,
            int_numerals: HashMap::new(),
            rational_numerals: HashMap::new(),
        });
        Ok(())
    }

    /// Interns one accepted integer spelling as a fresh uninterpreted
    /// constant, returning the same row for every later occurrence.
    fn int_numeral(&mut self, spelling: &str) -> Result<Ref, Error> {
        let int_ty = self.numeric()?.int_ty;
        if let Some(reference) = self.numeric()?.int_numerals.get(spelling).copied() {
            return Ok(reference);
        }
        let reference = self.fresh_constant(int_ty)?;
        self.numeric
            .as_mut()
            .expect("the numeric vocabulary was read above")
            .int_numerals
            .insert(spelling.to_owned(), reference);
        Ok(reference)
    }

    /// Interns one accepted rational spelling as a fresh uninterpreted
    /// constant. Spellings are not reduced, so `2/4` and `1/2` stay distinct.
    fn rational_numeral(&mut self, spelling: &str) -> Result<Ref, Error> {
        let real_ty = self.numeric()?.real_ty;
        if let Some(reference) = self.numeric()?.rational_numerals.get(spelling).copied() {
            return Ok(reference);
        }
        let reference = self.fresh_constant(real_ty)?;
        self.numeric
            .as_mut()
            .expect("the numeric vocabulary was read above")
            .rational_numerals
            .insert(spelling.to_owned(), reference);
        Ok(reference)
    }

    /// Lowers one numeral atom under the current dialect.
    ///
    /// A spelling outside the canonical grammar is rejected rather than
    /// normalized, so `007`, `-0`, `+3`, `1.5` and `1/0` all fail closed.
    fn numeral_term(&mut self, spelling: &str) -> Result<Term, Error> {
        match numeral_kind(spelling) {
            Some(NumeralKind::Integer) => self.int_numeral(spelling).map(Term::positive),
            Some(NumeralKind::Rational) if self.dialect == Dialect::Alethe => {
                self.rational_numeral(spelling).map(Term::positive)
            }
            Some(NumeralKind::Rational) => Err(Error::Malformed {
                message: format!("rational literal {spelling:?} is not QF_UFLIA input syntax"),
            }),
            None => Err(Error::Malformed {
                message: format!("numeral {spelling:?} is not a canonical spelling"),
            }),
        }
    }

    /// Reads the numeric sort of one lowered operand.
    fn numeric_sort(&self, operator: &str, term: Ref) -> Result<NumericSort, Error> {
        let classifier = self.kernel.classifier(term)?;
        let numeric = self.numeric()?;
        if self.kernel.equivalent(classifier, numeric.int_ty)? {
            return Ok(NumericSort::Int);
        }
        if self.kernel.equivalent(classifier, numeric.real_ty)? {
            return Ok(NumericSort::Real);
        }
        Err(Error::Malformed {
            message: format!("{operator} operands must be Int or Real"),
        })
    }

    fn numeric_operators(&self, sort: NumericSort) -> Result<Operators, Error> {
        let numeric = self.numeric()?;
        Ok(match sort {
            NumericSort::Int => numeric.int,
            NumericSort::Real => numeric.real,
        })
    }

    /// Lowers an arithmetic application as an uninterpreted function spine.
    ///
    /// SMT-LIB Ints declares `+`, `-` and `*` `:left-assoc`, and cvc5 1.3.4
    /// emits `+` at arities two through twelve, `-` at one and two, `*` at two
    /// and the four order relations at two only. The chainable comparison form
    /// is rejected rather than guessed, because an untested association is
    /// exactly the bug class a right-associative `=>` already produced once.
    fn arithmetic(
        &mut self,
        operator: &str,
        arguments: &[Expr],
        depth: usize,
    ) -> Result<Term, Error> {
        // Operands lower first and in source order, so `:named` registration
        // and `ite` binder names still follow the printed order.
        let operands = arguments
            .iter()
            .map(|argument| self.term_at(argument, depth).map(|term| term.reference))
            .collect::<Result<Vec<_>, _>>()?;
        let (first, rest) = operands.split_first().ok_or_else(|| Error::Malformed {
            message: format!("{operator} requires at least one argument"),
        })?;
        // Sorts are inferred from the first operand and then required of every
        // other one; over 147 measured cvc5 problem and proof pairs this check
        // never fires, so it bounds the lowering rather than restricting it.
        let sort = self.numeric_sort(operator, *first)?;
        for &operand in rest {
            if self.numeric_sort(operator, operand)? != sort {
                return Err(Error::Malformed {
                    message: format!(
                        "{operator} operands have different sorts, {:?} and {:?}",
                        self.kernel.classifier(*first)?,
                        self.kernel.classifier(operand)?
                    ),
                });
            }
        }
        let operators = self.numeric_operators(sort)?;
        if operator == "-" && rest.is_empty() {
            let applied = self.kernel.app(operators.neg, *first)?;
            return Ok(Term::positive(applied));
        }
        if matches!(operator, "<" | "<=" | ">" | ">=") && operands.len() != 2 {
            return Err(Error::Unsupported {
                message: format!(
                    "chainable {operator} at arity {}, where cvc5 emits only the binary form",
                    operands.len()
                ),
            });
        }
        if rest.is_empty() {
            return Err(Error::Malformed {
                message: format!("{operator} requires at least two arguments, got 1"),
            });
        }
        let head = match operator {
            "+" => operators.add,
            "-" => operators.sub,
            "*" => operators.mul,
            "<" => operators.lt,
            "<=" => operators.le,
            ">" => operators.gt,
            ">=" => operators.ge,
            _ => unreachable!("the caller limits arithmetic operators"),
        };
        let mut result = *first;
        for &operand in rest {
            result = self.kernel.app(head, result)?;
            result = self.kernel.app(result, operand)?;
        }
        Ok(Term::positive(result))
    }

    /// Lowers `to_real` or `to_int` as an uninterpreted coercion constant.
    fn coercion(&mut self, operator: &str, argument: &Expr, depth: usize) -> Result<Term, Error> {
        let operand = self.term_at(argument, depth)?.reference;
        let head = if operator == "to_real" {
            self.numeric()?.to_real
        } else {
            self.numeric()?.to_int
        };
        // `Kernel::app` raises a classifier mismatch itself, so the operand
        // sort needs no separate check.
        let applied = self.kernel.app(head, operand)?;
        Ok(Term::positive(applied))
    }

    /// Rejects a declared name this reader would otherwise read as a numeral
    /// or a builtin sort.
    ///
    /// cvc5 forecloses the numeral case itself, rejecting `(declare-const -3
    /// Int)` as a parse error, so refusing it here costs nothing and makes the
    /// two readers agree on one reading per spelling.
    fn require_declarable_name(name: &str) -> Result<(), Error> {
        if matches!(name, "Bool" | "Int" | "Real") {
            return Err(Error::Malformed {
                message: format!("declared name {name:?} is a builtin sort"),
            });
        }
        if numeral_kind(name).is_some() {
            return Err(Error::Malformed {
                message: format!("declared symbol {name:?} is spelled as a numeral"),
            });
        }
        Ok(())
    }

    fn name(&mut self) -> Result<u64, Error> {
        let name = self.next_name;
        self.next_name = self
            .next_name
            .checked_add(1)
            .ok_or_else(|| Error::Malformed {
                message: "symbol name space is exhausted".to_owned(),
            })?;
        Ok(name)
    }

    fn ingest_problem(&mut self, problem: &SmtProblem) -> Result<(), Error> {
        self.dialect = Dialect::SmtLib;
        let mut logic = None;
        for command in problem.commands() {
            match command {
                SmtCommand::SetLogic(value) => {
                    let declared = Logic::from_name(value);
                    if logic.replace(value.as_str()).is_some() || declared != Some(self.logic) {
                        return Err(Error::Unsupported {
                            message: format!("logic {value:?}"),
                        });
                    }
                    if self.logic == Logic::QfUflia {
                        self.allocate_numeric()?;
                    }
                }
                SmtCommand::DeclareSort { name, arity: 0 } => {
                    Self::require_declarable_name(name)?;
                    if self.sorts.contains_key(name) {
                        return Err(Error::Malformed {
                            message: format!("duplicate sort {name:?}"),
                        });
                    }
                    let symbol = self.name()?;
                    let ty = self.kernel.ty_fv(symbol, self.star)?;
                    self.sorts.insert(name.clone(), ty);
                }
                SmtCommand::DeclareSort { name, arity } => {
                    return Err(Error::Unsupported {
                        message: format!("parametric sort {name:?}/{arity}"),
                    });
                }
                SmtCommand::DeclareFun {
                    name,
                    parameters,
                    result,
                } => self.declare_function(name, parameters, result)?,
                SmtCommand::Assert(expression) => {
                    let term = self.term(expression)?;
                    self.assertions.push(Lit::positive(term.reference.get()));
                    self.assertion_terms.push(term);
                }
            }
        }
        if logic.and_then(Logic::from_name) != Some(self.logic) {
            return Err(Error::Unsupported {
                message: format!("problem must declare {}", self.logic.name()),
            });
        }
        Ok(())
    }

    fn declare_function(
        &mut self,
        name: &str,
        parameters: &[Expr],
        result: &Expr,
    ) -> Result<(), Error> {
        Self::require_declarable_name(name)?;
        if self.functions.contains_key(name) {
            return Err(Error::Malformed {
                message: format!("duplicate function {name:?}"),
            });
        }
        // `@` spellings name Alethe `:named` terms, which `term_at` resolves
        // ahead of declared functions, so such a declaration is unreachable.
        if name.starts_with('@') {
            return Err(Error::Unsupported {
                message: format!("declared function {name:?} uses the reserved @ namespace"),
            });
        }
        if self.named.contains_key(name) {
            return Err(Error::Malformed {
                message: format!("function {name:?} collides with a named term"),
            });
        }
        let mut ty = self.sort(result)?;
        for parameter in parameters.iter().rev() {
            let domain = self.sort(parameter)?;
            ty = self.kernel.ty_arr(domain, ty)?;
        }
        let symbol = self.name()?;
        let term = self.kernel.tm_fv(symbol, ty)?;
        self.functions.insert(name.to_owned(), Term::positive(term));
        Ok(())
    }

    /// Resolves an SMT-LIB sort name.
    ///
    /// `Real` is deliberately absent: `QF_UFLIA` input has no `Real` sort, and
    /// the numeric vocabulary's `real_ty` exists only to lower proof terms.
    fn sort(&self, expression: &Expr) -> Result<Ref, Error> {
        let name = symbol(expression)?;
        if name == "Bool" {
            return Ok(self.bool_ty);
        }
        if name == "Int" {
            return Ok(self.numeric()?.int_ty);
        }
        self.sorts
            .get(name)
            .copied()
            .ok_or_else(|| Error::Unsupported {
                message: format!("sort {name:?}"),
            })
    }

    fn term(&mut self, expression: &Expr) -> Result<Term, Error> {
        self.term_at(expression, 0)
    }

    fn term_at(&mut self, expression: &Expr, depth: usize) -> Result<Term, Error> {
        if depth >= MAX_TERM_DEPTH {
            return Err(Error::TermTooDeep {
                limit: MAX_TERM_DEPTH,
            });
        }
        let depth = depth + 1;
        match expression.node() {
            ExprKind::Atom(node) => match SpannedRepr::atom(node) {
                Atom::Symbol(value) => {
                    // SMT-LIB 2.6 s3.6.1: a `let` binder shadows any function
                    // symbol of the same name, `true`, `false` and `:named`
                    // spellings included, so locals are scanned first.
                    if let Some(term) = self
                        .locals
                        .iter()
                        .rev()
                        .find_map(|scope| scope.get(value.as_str()))
                    {
                        return Ok(*term);
                    }
                    // Numerals are consulted after the `let` scan and before
                    // the constants, `@` names and declared functions, and
                    // only when the logic allocated a numeric vocabulary, so a
                    // QF_UF arena reads exactly as it did before.
                    if self.numeric.is_some() && signed_numeral_spelling(value) {
                        return self.numeral_term(value);
                    }
                    if value == "true" {
                        return Ok(Term::positive(self.kernel.bool(self.bool_ty, true)?));
                    }
                    if value == "false" {
                        return Ok(Term::positive(self.kernel.bool(self.bool_ty, false)?));
                    }
                    if value.starts_with('@') {
                        return self
                            .named
                            .get(value.as_str())
                            .copied()
                            .map(|term| Term::positive(term.reference))
                            .ok_or_else(|| Error::Malformed {
                                message: format!("unknown named term {value:?}"),
                            });
                    }
                    // A `:named` label and a declared function never share a
                    // spelling, so the two lookups cannot disagree.
                    if let Some(term) = self.functions.get(value.as_str()).copied() {
                        return Ok(term);
                    }
                    self.named
                        .get(value.as_str())
                        .copied()
                        .map(|term| Term::positive(term.reference))
                        .ok_or_else(|| Error::Malformed {
                            message: format!("unknown function {value:?}"),
                        })
                }
                // The reader classifies an atom as a number only when its
                // first byte is a digit, so `10` and `1/1` arrive here while
                // `-3` and `-1/3` arrive as symbols. Both must be handled.
                Atom::Number(value) if self.numeric.is_some() => self.numeral_term(value),
                other => Err(Error::Unsupported {
                    message: format!("term atom {other:?}"),
                }),
            },
            ExprKind::List(node) => {
                let items = SpannedRepr::list_items(node);
                let head = items.first().ok_or_else(|| Error::Malformed {
                    message: "empty term".to_owned(),
                })?;
                match symbol(head)? {
                    "!" => self.annotation(items, depth),
                    "not" if items.len() == 2 => {
                        let inner = self.term_at(&items[1], depth)?;
                        let reference = self.kernel.op1(Op1::Not, inner.reference)?;
                        Ok(Term {
                            reference,
                            literal: inner.literal.negated(),
                        })
                    }
                    "=" if items.len() >= 3 => self.chain_equality(&items[1..], depth),
                    "distinct" if items.len() >= 3 => self.distinct(&items[1..], depth),
                    "xor" if items.len() >= 3 => self.fold_xor(&items[1..], depth),
                    "ite" if items.len() == 4 => self.ite(&items[1], &items[2], &items[3], depth),
                    "let" if items.len() == 3 => self.let_term(&items[1], &items[2], depth),
                    "and" | "or" => self.fold_boolean(symbol(head)?, &items[1..], depth),
                    "=>" => self.fold_implication(&items[1..], depth),
                    operator @ ("+" | "-" | "*" | "<" | "<=" | ">" | ">=")
                        if self.numeric.is_some() =>
                    {
                        self.arithmetic(operator, &items[1..], depth)
                    }
                    operator @ ("to_real" | "to_int")
                        if self.numeric.is_some() && items.len() == 2 =>
                    {
                        self.coercion(operator, &items[1], depth)
                    }
                    _ => {
                        let mut function = self.term_at(head, depth)?.reference;
                        for argument in &items[1..] {
                            let argument = self.term_at(argument, depth)?.reference;
                            function = self.kernel.app(function, argument)?;
                        }
                        Ok(Term::positive(function))
                    }
                }
            }
        }
    }

    fn fold_xor(&mut self, arguments: &[Expr], depth: usize) -> Result<Term, Error> {
        let (first, rest) = arguments.split_first().ok_or_else(|| Error::Malformed {
            message: "xor requires at least two arguments".to_owned(),
        })?;
        let mut result = self.term_at(first, depth)?.reference;
        // `xor` lowers to a chain of Boolean disequalities, and `Kernel::eq`
        // reads the operand sort off its left argument, so the Boolean sort of
        // both operands is required here rather than inferred.
        self.require_boolean(result, "xor")?;
        for argument in rest {
            let right = self.term_at(argument, depth)?.reference;
            self.require_boolean(right, "xor")?;
            let equality = self.kernel.eq(self.bool_ty, result, right)?;
            result = self.kernel.op1(Op1::Not, equality)?;
        }
        Ok(Term::positive(result))
    }

    fn require_boolean(&self, term: Ref, operator: &str) -> Result<(), Error> {
        if self
            .kernel
            .equivalent(self.kernel.classifier(term)?, self.bool_ty)?
        {
            return Ok(());
        }
        Err(Error::Malformed {
            message: format!("{operator} operands must be Boolean"),
        })
    }

    fn chain_equality(&mut self, arguments: &[Expr], depth: usize) -> Result<Term, Error> {
        let mut terms = arguments.iter();
        let mut left = self
            .term_at(
                terms.next().expect("the caller requires two arguments"),
                depth,
            )?
            .reference;
        let mut equalities = Vec::new();
        for argument in terms {
            let right = self.term_at(argument, depth)?.reference;
            equalities.push(self.kernel.eq(self.bool_ty, left, right)?);
            left = right;
        }
        let (first, rest) = equalities
            .split_first()
            .expect("two terms produce at least one equality");
        let mut result = *first;
        for &equality in rest {
            result = self.kernel.op2(Op2::And, result, equality)?;
        }
        Ok(Term::positive(result))
    }

    fn distinct(&mut self, arguments: &[Expr], depth: usize) -> Result<Term, Error> {
        let terms = arguments
            .iter()
            .map(|argument| self.term_at(argument, depth).map(|term| term.reference))
            .collect::<Result<Vec<_>, _>>()?;
        let mut inequalities = Vec::new();
        for (index, &left) in terms.iter().enumerate() {
            for &right in &terms[index + 1..] {
                let equality = self.kernel.eq(self.bool_ty, left, right)?;
                inequalities.push(self.kernel.op1(Op1::Not, equality)?);
            }
        }
        let (first, rest) = inequalities.split_first().ok_or_else(|| Error::Malformed {
            message: "distinct requires at least two arguments".to_owned(),
        })?;
        let mut result = *first;
        for &inequality in rest {
            result = self.kernel.op2(Op2::And, result, inequality)?;
        }
        Ok(Term::positive(result))
    }

    fn ite(
        &mut self,
        condition: &Expr,
        then_: &Expr,
        else_: &Expr,
        depth: usize,
    ) -> Result<Term, Error> {
        let condition = self.term_at(condition, depth)?.reference;
        let then_ = self.term_at(then_, depth)?.reference;
        let else_ = self.term_at(else_, depth)?.reference;
        let result_ty = self.kernel.classifier(then_)?;
        if !self
            .kernel
            .equivalent(result_ty, self.kernel.classifier(else_)?)?
        {
            return Err(Error::Malformed {
                message: "ite branches have different sorts".to_owned(),
            });
        }
        for &(cached_condition, cached_then, cached_else, conditional) in &self.conditionals {
            if join_same_syntax(&mut self.kernel, cached_condition, condition).is_ok()
                && join_same_syntax(&mut self.kernel, cached_then, then_).is_ok()
                && join_same_syntax(&mut self.kernel, cached_else, else_).is_ok()
            {
                return Ok(Term::positive(conditional.term));
            }
        }
        let binder_name = self.name()?;
        let binder = self.kernel.tm_fv(binder_name, result_ty)?;
        let result = conditional(
            &mut self.kernel,
            self.bool_ty,
            result_ty,
            binder,
            condition,
            then_,
            else_,
        )?;
        self.conditionals.push((condition, then_, else_, result));
        Ok(Term::positive(result.term))
    }

    fn let_term(&mut self, bindings: &Expr, body: &Expr, depth: usize) -> Result<Term, Error> {
        let ExprKind::List(node) = bindings.node() else {
            return Err(Error::Malformed {
                message: "let bindings must be a list".to_owned(),
            });
        };
        let mut scope = HashMap::new();
        for binding in SpannedRepr::list_items(node) {
            let ExprKind::List(node) = binding.node() else {
                return Err(Error::Malformed {
                    message: "let binding must be a pair".to_owned(),
                });
            };
            let pair = SpannedRepr::list_items(node);
            let [name, value] = pair else {
                return Err(Error::Malformed {
                    message: "let binding must be a pair".to_owned(),
                });
            };
            let name = symbol(name)?;
            if numeral_kind(name).is_some() {
                return Err(Error::Malformed {
                    message: format!("let binder {name:?} is spelled as a numeral"),
                });
            }
            if scope.contains_key(name) {
                return Err(Error::Malformed {
                    message: format!("duplicate let binding {name:?}"),
                });
            }
            let value = self.term_at(value, depth)?;
            scope.insert(name.to_owned(), value);
        }
        self.locals.push(scope);
        let result = self.term_at(body, depth);
        self.locals.pop();
        result
    }

    fn annotation(&mut self, items: &[Expr], depth: usize) -> Result<Term, Error> {
        if items.len() < 4 || !items.len().is_multiple_of(2) {
            return Err(Error::Malformed {
                message: "annotation requires attribute-value pairs".to_owned(),
            });
        }
        let value = self.term_at(&items[1], depth)?;
        for pair in items[2..].chunks_exact(2) {
            if keyword(&pair[0])? != "named" {
                return Err(Error::Unsupported {
                    message: format!("term attribute :{}", keyword(&pair[0])?),
                });
            }
            let name = symbol(&pair[1])?;
            // `named` is one flat map shared by the problem and the proof, so a
            // name that also denotes a declared function is rejected rather
            // than silently preferred over it.
            if self.functions.contains_key(name) {
                return Err(Error::Malformed {
                    message: format!("named term {name:?} collides with a declared function"),
                });
            }
            if self.named.insert(name.to_owned(), value).is_some() {
                return Err(Error::Malformed {
                    message: format!("duplicate named term {name:?}"),
                });
            }
        }
        Ok(value)
    }

    /// Lowers `:left-assoc` `and` and `or` by folding their arguments left.
    fn fold_boolean(
        &mut self,
        operator: &str,
        arguments: &[Expr],
        depth: usize,
    ) -> Result<Term, Error> {
        let (first, rest) = arity_at_least_two(operator, arguments)?;
        let mut result = self.term_at(first, depth)?.reference;
        for argument in rest {
            let right = self.term_at(argument, depth)?.reference;
            result = match operator {
                "and" => self.kernel.op2(Op2::And, result, right)?,
                "or" => self.kernel.op2(Op2::Or, result, right)?,
                _ => unreachable!("caller limits Boolean operators"),
            };
        }
        Ok(Term::positive(result))
    }

    /// Lowers `=>`, which SMT-LIB Core declares `:right-assoc`, so that
    /// `(=> a b c)` denotes `a -> (b -> c)` rather than `(a -> b) -> c`.
    fn fold_implication(&mut self, arguments: &[Expr], depth: usize) -> Result<Term, Error> {
        arity_at_least_two("=>", arguments)?;
        // Lower left to right, so `:named` registration and `ite` binder names
        // still follow source order, then fold the lowered rows right.
        let rows = arguments
            .iter()
            .map(|argument| self.term_at(argument, depth).map(|term| term.reference))
            .collect::<Result<Vec<_>, _>>()?;
        let (last, rest) = rows
            .split_last()
            .expect("two arguments produce two lowered rows");
        let mut result = *last;
        for &antecedent in rest.iter().rev() {
            result = self.kernel.op2(Op2::Imp, antecedent, result)?;
        }
        Ok(Term::positive(result))
    }

    #[allow(clippy::too_many_lines)]
    fn run_proof(
        &mut self,
        proof: &AletheProof,
        handler: &mut impl RuleHandler,
    ) -> Result<ThmId, Error> {
        self.dialect = Dialect::Alethe;
        let mut refutation = None;
        for command in proof.commands() {
            match command {
                AletheCommand::Assume { id, term } => {
                    let term = self.term(term)?;
                    let formula = Lit::positive(term.reference.get());
                    match self.frames.last() {
                        // An outermost assumption must be one of the problem
                        // assertions. A frame-local one must not be checked
                        // against them: it is a subformula, and 3 of 490
                        // measured frames assume an assertion's negation.
                        None => self.match_assertion(formula)?,
                        Some(frame) if frame.sealed => {
                            return Err(Error::Frame {
                                frame: frame.id.clone(),
                                message: format!("assume {id:?} follows the frame's first step"),
                            });
                        }
                        Some(_) => {}
                    }
                    let theorem = self.kernel.identity(formula)?;
                    self.bind_step(id, theorem, false)?;
                    if let Some(frame) = self.frames.last_mut() {
                        frame.assumptions.push((id.clone(), formula));
                    }
                }
                AletheCommand::Step {
                    id,
                    clause,
                    rule,
                    premises,
                    args,
                    discharge,
                } => {
                    if self.frames.last().is_some_and(|frame| frame.id == *id) {
                        self.close_frame(id, clause, rule, premises, args, discharge)?;
                        continue;
                    }
                    let built_in_rejects_args = !args.is_empty()
                        && matches!(
                            rule.as_str(),
                            "resolution"
                                | "th_resolution"
                                | "refl"
                                | "symm"
                                | "trans"
                                | "cong"
                                | "equiv_pos2"
                                | "implies"
                                | "or_pos"
                                | "xor1"
                                | "xor2"
                                | "xor_pos2"
                                | "not_symm"
                                | "distinct_elim"
                                | "evaluate"
                                | "false"
                        );
                    // Only `subproof`, dispatched above, discharges anything.
                    if !discharge.is_empty() || built_in_rejects_args {
                        return Err(Error::Unsupported {
                            message: format!("{rule} attributes"),
                        });
                    }
                    let clause = self.lower_clause(clause)?;
                    let premises = premises
                        .iter()
                        .map(|name| self.resolve_premise(id, name))
                        .collect::<Result<Vec<_>, _>>()?;
                    let theorem = self
                        .apply_rule(rule, &clause, &premises, args, handler)
                        .map_err(|error| error.at_step(id))?;
                    let theorem = self.check_clause(id, theorem, &clause)?;
                    self.bind_step(id, theorem, true)?;
                    // Alethe Definition 7.2 puts the empty clause in the
                    // outermost proof, and an inner `(cl)` is a frame-local
                    // contradiction under frame-local assumptions.
                    if clause.is_empty() && self.frames.is_empty() {
                        refutation = Some(theorem);
                    }
                }
                AletheCommand::Anchor { step, args } => {
                    if !args.is_empty() {
                        return Err(Error::Unsupported {
                            message: "anchor context arguments, which bind, sko_ex, sko_forall, let and onepoint need and this replayer has no substitution model for".to_owned(),
                        });
                    }
                    if self.seen.contains(step) {
                        return Err(Error::Malformed {
                            message: format!("duplicate step {step:?}"),
                        });
                    }
                    self.frames.push(Frame {
                        id: step.clone(),
                        assumptions: Vec::new(),
                        bound: Vec::new(),
                        last: None,
                        sealed: false,
                    });
                }
                AletheCommand::DefineFun { .. } => {
                    return Err(Error::Unsupported {
                        message: "define-fun".to_owned(),
                    });
                }
            }
        }
        if let Some(frame) = self.frames.last() {
            return Err(Error::Frame {
                frame: frame.id.clone(),
                message: "anchor is never closed".to_owned(),
            });
        }
        let theorem = refutation.ok_or(Error::NoRefutation)?;
        for &(source, target) in &self.assertion_transports {
            self.kernel.convert_theorem(theorem, source, target)?;
        }
        self.kernel.weaken(theorem, &self.assertions, &[])?;
        self.kernel.contract_theorem(theorem)?;
        self.check_exact_goal(theorem)?;
        Ok(theorem)
    }

    fn ingest_proof(
        mut self,
        proof: &AletheProof,
        handler: &mut impl RuleHandler,
    ) -> Result<Refutation, Error> {
        let theorem = self.run_proof(proof, handler)?;
        Ok(Refutation {
            kernel: self.kernel,
            logic: self.logic,
            theorem,
            assertions: self.assertions,
        })
    }

    /// Lowers a `QF_UFLIA` proof up to its first arithmetic rule.
    ///
    /// Reaching the end without one is itself an error: this build has no
    /// checked arithmetic it could have used, so a proof that needed none is
    /// evidence the lowering, not the proof, is wrong.
    fn lower_proof(mut self, proof: &AletheProof) -> Result<Lowering, Error> {
        match self.run_proof(proof, &mut RejectUnknownRules) {
            Ok(_) => Err(Error::NoArithmeticGap),
            Err(Error::ArithmeticTheoryMissing { step, rule, domain }) => Ok(Lowering {
                kernel: self.kernel,
                logic: self.logic,
                assertions: self.assertions,
                steps: self.seen.len(),
                gap: ArithmeticGap { step, rule, domain },
            }),
            Err(other) => Err(other),
        }
    }

    fn lower_clause(&mut self, clause: &[Expr]) -> Result<Vec<Lit>, Error> {
        clause
            .iter()
            .map(|term| self.term(term).map(Term::literal))
            .collect()
    }

    /// Closes the innermost frame with its `subproof` step.
    fn close_frame(
        &mut self,
        id: &str,
        clause: &[Expr],
        rule: &str,
        premises: &[String],
        args: &[Expr],
        discharge: &[String],
    ) -> Result<(), Error> {
        if rule != "subproof" {
            return Err(Error::Frame {
                frame: id.to_owned(),
                message: format!(
                    "closed by rule {rule:?}; only subproof concludes a frame in this replayer"
                ),
            });
        }
        if !premises.is_empty() || !args.is_empty() {
            return Err(Error::Frame {
                frame: id.to_owned(),
                message: "subproof takes neither premises nor args".to_owned(),
            });
        }
        let clause = self.lower_clause(clause)?;
        let frame = self.frames.pop().expect("the caller matched an open frame");
        // Frame-local indices leave scope with the frame, so no later step can
        // name an inner theorem at all. The theorems themselves are retained:
        // `Kernel::remove_theorem` reuses slots, so a stale handle would alias
        // a different theorem.
        for bound in &frame.bound {
            self.steps.remove(bound);
        }
        let theorem = self.subproof(&frame, &clause, discharge)?;
        let theorem = self.check_clause(id, theorem, &clause)?;
        self.bind_step(id, theorem, true)
    }

    /// Discharges a frame's assumptions into the clause Alethe states.
    ///
    /// Alethe Rule 10 concludes `not phi_1, ..., not phi_n, psi` from a
    /// frame's assumptions and its last step. In this multi-conclusion sequent
    /// kernel that is `not_right` applied once per assumption; the rest
    /// reconciles the sequent-level polarity with the object-level `tm.not`
    /// row the clause names, and checks well-formedness.
    ///
    /// A lying `:discharge` list cannot be unsound: `weaken` then `not_right`
    /// on a literal absent from the antecedent composes to plain right
    /// weakening. What keeps a frame-local assumption out of the refutation is
    /// that assumptions enter only through `Kernel::identity`, so they sit in
    /// the antecedent and leave it only by discharge or proof, and
    /// `check_exact_goal` requires the final antecedent to be the assertion
    /// set exactly.
    fn subproof(
        &mut self,
        frame: &Frame,
        clause: &[Lit],
        discharge: &[String],
    ) -> Result<ThmId, Error> {
        let ids = frame
            .assumptions
            .iter()
            .map(|(id, _)| id.as_str())
            .collect::<Vec<_>>();
        if discharge.len() != ids.len() || discharge.iter().zip(&ids).any(|(named, id)| named != id)
        {
            return Err(Error::Frame {
                frame: frame.id.clone(),
                message: format!(
                    "discharge {discharge:?} does not name the frame assumptions {ids:?} in order"
                ),
            });
        }
        if clause.len() < ids.len() {
            return Err(Error::Frame {
                frame: frame.id.clone(),
                message: format!(
                    "clause has {} literals, fewer than the {} discharged assumptions",
                    clause.len(),
                    ids.len()
                ),
            });
        }
        let last = frame.last.ok_or_else(|| Error::Frame {
            frame: frame.id.clone(),
            message: "frame has no step to conclude".to_owned(),
        })?;
        // `resolution` returns a single premise unchanged, so a frame's last
        // theorem can alias an earlier step's, and the discharge below mutates
        // in place. The copy is mandatory, not hygiene.
        let mut theorem = self.kernel.copy_theorem(last)?;
        self.kernel.contract_theorem(theorem)?;
        for (index, &(_, assumption)) in frame.assumptions.iter().enumerate() {
            let stated = clause[index];
            // The clause literal must be the negation of this assumption and
            // nothing else. Without this precheck a stated literal such as
            // `(or (not a) x)` would fold soundly but would consume `x` from
            // the frame's own conclusion, which is not what Alethe means.
            if strip_negations(&self.kernel, stated)?
                != strip_negations(&self.kernel, assumption.negated())?
            {
                return Err(Error::Frame {
                    frame: frame.id.clone(),
                    message: format!(
                        "clause literal {index} is not the negation of discharged assumption {:?}",
                        ids[index]
                    ),
                });
            }
            // Weaken only when the assumption is absent, because `not_right`
            // removes exactly one antecedent occurrence; weakening an already
            // present literal would leave the original undischarged.
            if !has_unit_premise(&self.kernel, theorem, assumption)? {
                self.kernel.weaken(theorem, &[assumption], &[])?;
            }
            self.kernel.not_right(theorem, assumption)?;
            if stated != assumption.negated() {
                // `not_right` leaves the sequent-level negative literal on the
                // assumption's own row, and the clause spells the same literal
                // as a different row. Folding reaches it directly when that
                // row's leaves are the sequent-level literal; when the
                // assumption is itself a negation, which 419 of 1368 measured
                // discharged assumptions are, the leaves lie one level deeper
                // and the conclusion must be flattened to them first.
                theorem = if let Ok(folded) = self.kernel.fold_conclusion(theorem, stated) {
                    folded
                } else {
                    let flattened = self
                        .kernel
                        .flatten_conclusion(theorem, assumption.negated())?;
                    self.kernel.fold_conclusion(flattened, stated)?
                };
            }
        }
        self.kernel.contract_theorem(theorem)?;
        Ok(theorem)
    }

    /// Resolves one premise index in the current scope.
    fn resolve_premise(&self, step: &str, premise: &str) -> Result<ThmId, Error> {
        if let Some(theorem) = self.steps.get(premise).copied() {
            return Ok(theorem);
        }
        if self.seen.contains(premise) {
            return Err(Error::OutOfScopePremise {
                step: step.to_owned(),
                premise: premise.to_owned(),
            });
        }
        Err(Error::Malformed {
            message: format!("unknown premise {premise:?}"),
        })
    }

    /// Binds one Alethe index to a checked theorem in the current scope.
    fn bind_step(&mut self, id: &str, theorem: ThmId, is_step: bool) -> Result<(), Error> {
        // Indices are globally unique in Alethe, and `seen` is never pruned,
        // so uniqueness still holds after a frame drops its bindings.
        if !self.seen.insert(id.to_owned()) {
            return Err(Error::Malformed {
                message: format!("duplicate step {id:?}"),
            });
        }
        self.steps.insert(id.to_owned(), theorem);
        if let Some(frame) = self.frames.last_mut() {
            frame.bound.push(id.to_owned());
            if is_step {
                frame.last = Some(theorem);
                frame.sealed = true;
            }
        }
        Ok(())
    }

    fn match_assertion(&mut self, literal: Lit) -> Result<(), Error> {
        let candidate = reference(literal.magnitude())?;
        let assertions = self.assertion_terms.clone();
        for assertion in assertions {
            let target = assertion.reference;
            if join_same_syntax(&mut self.kernel, candidate, target).is_ok() {
                self.assertion_transports.push((candidate, target));
                return Ok(());
            }
        }
        Err(Error::UnassertedAssumption)
    }

    fn apply_rule(
        &mut self,
        rule: &str,
        clause: &[Lit],
        premises: &[ThmId],
        args: &[Expr],
        handler: &mut impl RuleHandler,
    ) -> Result<ThmId, Error> {
        // Arithmetic rules are refused before any argument is inspected, and
        // with their own error, so that "this build has no arithmetic" is a
        // machine-checkable property rather than an unwritten handler.
        if let Some(domain) = arithmetic_rule_domain(rule) {
            return Err(Error::ArithmeticTheoryMissing {
                step: String::new(),
                rule: rule.to_owned(),
                domain: domain.to_owned(),
            });
        }
        match rule {
            "resolution" | "th_resolution" => self.resolution(premises),
            "refl" | "distinct_elim" => self.reflexivity(clause),
            "symm" => self.symmetry(clause, premises),
            "trans" => self.transitivity(clause, premises),
            "cong" => self.congruence(clause, premises),
            "equiv_pos2" => self.equiv_pos2(clause),
            "implies" => self.implies(premises),
            "or_pos" => self.or_pos(clause),
            "and" => self.and_elimination(clause, premises, args),
            "xor1" => self.xor_one(clause, premises),
            "xor2" => self.xor_two(clause, premises),
            "xor_pos2" => self.xor_positive_two(clause, premises),
            "not_symm" => self.not_symmetry(clause, premises),
            "rare_rewrite" => self.rare_rewrite(clause, premises, args, handler),
            "evaluate" => self.evaluate(clause),
            "false" => self.false_rule(clause),
            // A `hole` step is a solver trust placeholder carrying no checked
            // content, so it is rejected before any handler can accept it.
            "hole" => Err(Error::Unsupported {
                message: "rule \"hole\" states an unchecked solver step".to_owned(),
            }),
            other => handler
                .apply(RuleRequest {
                    kernel: &mut self.kernel,
                    bool_ty: self.bool_ty,
                    rule: other,
                    clause,
                    premises,
                    args,
                })?
                .ok_or_else(|| Error::Unsupported {
                    message: format!("rule {other:?}"),
                }),
        }
    }

    fn or_pos(&mut self, clause: &[Lit]) -> Result<ThmId, Error> {
        let Some(negated_disjunction) = clause.first().copied() else {
            return Err(Error::Malformed {
                message: "or_pos requires a clause".to_owned(),
            });
        };
        if negated_disjunction.is_positive() {
            return Err(Error::Malformed {
                message: "or_pos requires a negative disjunction".to_owned(),
            });
        }
        let disjunction = reference(negated_disjunction.magnitude())?;
        let theorem = self.kernel.identity(Lit::positive(disjunction.get()))?;
        let mut theorem =
            self.kernel
                .expand_conclusion(theorem, Lit::positive(disjunction.get()), None)?;
        // The lowered disjunction is a binary tree, so a stated clause wider
        // than two disjuncts needs further expansion. Expansion is directed by
        // the stated clause, which keeps a disjunct that Alethe states as one
        // literal, such as the left operand of `(or (or a b) c)`, intact.
        let stated = clause[1..]
            .iter()
            .map(|literal| canonical_clause_literal(&self.kernel, *literal))
            .collect::<Result<BTreeSet<_>, _>>()?;
        loop {
            let mut expandable = None;
            for literal in conclusion_literals(&self.kernel, theorem)? {
                if !literal.is_positive() || stated.contains(&literal) {
                    continue;
                }
                let formula = reference(literal.magnitude())?;
                if self.kernel.arena().op2(formula) == Some(Op2::Or) {
                    expandable = Some(literal);
                    break;
                }
            }
            let Some(literal) = expandable else {
                break;
            };
            theorem = self.kernel.expand_conclusion(theorem, literal, None)?;
        }
        self.kernel
            .not_right(theorem, Lit::positive(disjunction.get()))?;
        self.kernel.contract_theorem(theorem)?;
        Ok(theorem)
    }

    fn and_elimination(
        &mut self,
        clause: &[Lit],
        premises: &[ThmId],
        args: &[Expr],
    ) -> Result<ThmId, Error> {
        let [premise] = premises else {
            return Err(Error::Malformed {
                message: "and requires one premise".to_owned(),
            });
        };
        let [argument] = args else {
            return Err(Error::Malformed {
                message: "and requires one index".to_owned(),
            });
        };
        let index = number_value(argument)?
            .parse::<usize>()
            .map_err(|_| Error::Malformed {
                message: "and index is not a natural number".to_owned(),
            })?;
        let conclusions = conclusion_literals(&self.kernel, *premise)?;
        let [source] = conclusions.as_slice() else {
            return Err(Error::Malformed {
                message: "and premise must have one conclusion".to_owned(),
            });
        };
        if !source.is_positive() {
            return Err(Error::Malformed {
                message: "and premise must conclude a conjunction".to_owned(),
            });
        }
        let conjunction = reference(source.magnitude())?;
        let (selected, theorem) = self.and_projection(conjunction, index)?;
        let theorem = self.kernel.cut(*premise, theorem, *source)?;
        self.convert_equality(theorem, selected, positive_unit(clause, "and")?)
    }

    fn and_projection(&mut self, conjunction: Ref, index: usize) -> Result<(Ref, ThmId), Error> {
        let Some((left, right)) = self.kernel.arena().op2(conjunction).and_then(|operator| {
            (operator == Op2::And).then(|| {
                let mut children = self
                    .kernel
                    .arena()
                    .children(conjunction)
                    .expect("a checked binary operator has children");
                (
                    children
                        .next()
                        .expect("a binary operator has a left operand"),
                    children
                        .next()
                        .expect("a binary operator has a right operand"),
                )
            })
        }) else {
            if index != 0 {
                return Err(Error::Malformed {
                    message: "and index is outside the conjunction".to_owned(),
                });
            }
            return Ok((
                conjunction,
                self.kernel.identity(Lit::positive(conjunction.get()))?,
            ));
        };
        let left_arity = conjunction_arity(&self.kernel, left);
        let (selected, theorem, other) = if index < left_arity {
            let (selected, theorem) = self.and_projection(left, index)?;
            (selected, theorem, right)
        } else {
            let (selected, theorem) = self.and_projection(right, index - left_arity)?;
            (selected, theorem, left)
        };
        self.kernel
            .weaken(theorem, &[Lit::positive(other.get())], &[])?;
        let theorem = self
            .kernel
            .and_left(theorem, Lit::positive(conjunction.get()))?;
        Ok((selected, theorem))
    }

    /// Derives `(cl (not a) b)` from an `(=> a b)` premise.
    ///
    /// Exactly one implication is expanded per literal, so a right-nested
    /// consequent such as `(=> p (=> q r))` keeps its inner implication
    /// instead of flattening into `(cl (not p) (not q) r)`.
    fn implies(&mut self, premises: &[ThmId]) -> Result<ThmId, Error> {
        let [premise] = premises else {
            return Err(Error::Malformed {
                message: "implies requires one premise".to_owned(),
            });
        };
        let formulas = conclusion_literals(&self.kernel, *premise)?;
        let mut result = *premise;
        let mut expanded = false;
        for formula in formulas {
            if !formula.is_positive() {
                continue;
            }
            let reference = reference(formula.magnitude())?;
            if self.kernel.arena().op2(reference) != Some(Op2::Imp) {
                continue;
            }
            result = self.kernel.expand_conclusion(result, formula, None)?;
            expanded = true;
        }
        if !expanded {
            return Err(Error::Malformed {
                message: "implies premise must conclude an implication".to_owned(),
            });
        }
        self.kernel.contract_theorem(result)?;
        Ok(result)
    }

    /// Applies one RARE rewrite named by `args[0]`.
    ///
    /// cvc5 states `:premises` before `:args` on some rewrites, so premises
    /// are threaded through and every premise-free name asserts an empty list
    /// rather than dropping one silently. An unrecognized name reaches the
    /// user handler: the name set is producer-version dependent, and a
    /// built-in arm that shadowed the whole rule would leave no userspace
    /// remedy for a cvc5 upgrade.
    fn rare_rewrite(
        &mut self,
        clause: &[Lit],
        premises: &[ThmId],
        args: &[Expr],
        handler: &mut impl RuleHandler,
    ) -> Result<ThmId, Error> {
        let Some(name) = args.first().and_then(string_value) else {
            return Err(Error::Malformed {
                message: "rare_rewrite requires a string rule name".to_owned(),
            });
        };
        if let Some(domain) = rare_rewrite_arithmetic_domain(name) {
            return Err(Error::ArithmeticTheoryMissing {
                step: String::new(),
                rule: name.to_owned(),
                domain: domain.to_owned(),
            });
        }
        match name {
            "eq-refl" => {
                require_no_premises(name, premises)?;
                let target = positive_unit(clause, "rare_rewrite eq-refl")?;
                let [_bool_ty, proposition, truth] = equality_children(&self.kernel, target)?;
                if self.kernel.arena().bool_value(truth) != Some(true) {
                    return Err(Error::Malformed {
                        message: "eq-refl must rewrite to true".to_owned(),
                    });
                }
                let [_domain, left, right] = equality_children(&self.kernel, proposition)?;
                join_same_syntax(&mut self.kernel, left, right)?;
                let proved = self.kernel.refl(self.bool_ty, left)?;
                let theorem =
                    self.convert_equality(proved.theorem, proved.equality, proposition)?;
                self.equality_to_true(proposition, truth, theorem, target)
            }
            "bool-xor-refl" => {
                require_no_premises(name, premises)?;
                self.evaluate(clause)
            }
            "distinct-binary-elim" => {
                require_no_premises(name, premises)?;
                self.reflexivity(clause)
            }
            "bool-eq-true" => {
                require_no_premises(name, premises)?;
                self.bool_eq_true(clause)
            }
            "bool-eq-false" => {
                require_no_premises(name, premises)?;
                self.bool_eq_false(clause)
            }
            "ite-true-cond" => {
                require_no_premises(name, premises)?;
                self.ite_constant(clause, true)
            }
            "ite-false-cond" => {
                require_no_premises(name, premises)?;
                self.ite_constant(clause, false)
            }
            other => {
                let bool_ty = self.bool_ty;
                handler
                    .apply(RuleRequest {
                        kernel: &mut self.kernel,
                        bool_ty,
                        rule: "rare_rewrite",
                        clause,
                        premises,
                        args,
                    })?
                    .ok_or_else(|| Error::Unsupported {
                        message: format!("rare_rewrite {other:?}"),
                    })
            }
        }
    }

    fn bool_eq_true(&mut self, clause: &[Lit]) -> Result<ThmId, Error> {
        let target = positive_unit(clause, "bool-eq-true")?;
        let [_bool_ty, equality, proposition] = equality_children(&self.kernel, target)?;
        let [_inner_bool_ty, left, truth] = equality_children(&self.kernel, equality)?;
        if self.kernel.arena().bool_value(truth) != Some(true) {
            return Err(Error::Malformed {
                message: "bool-eq-true does not compare with true".to_owned(),
            });
        }
        join_same_syntax(&mut self.kernel, left, proposition)?;

        let equality_assumption = self.kernel.identity(Lit::positive(equality.get()))?;
        let equality_implies_proposition = self.kernel.eqt_elim(equality_assumption)?;
        let proposition_assumption = self.kernel.identity(Lit::positive(proposition.get()))?;
        let proposition_implies_equality =
            self.equality_to_true(proposition, truth, proposition_assumption, equality)?;
        let result = self.kernel.deduct_antisym(
            self.bool_ty,
            equality,
            proposition,
            equality_implies_proposition,
            proposition_implies_equality,
        )?;
        self.convert_equality(result.theorem, result.equality, target)
    }

    fn bool_eq_false(&mut self, clause: &[Lit]) -> Result<ThmId, Error> {
        let target = positive_unit(clause, "bool-eq-false")?;
        let [_bool_ty, equality, negation] = equality_children(&self.kernel, target)?;
        let [_inner_bool_ty, proposition, falsehood] = equality_children(&self.kernel, equality)?;
        if self.kernel.arena().bool_value(falsehood) != Some(false)
            || self.kernel.arena().op1(negation) != Some(Op1::Not)
        {
            return Err(Error::Malformed {
                message: "bool-eq-false has the wrong shape".to_owned(),
            });
        }
        let negated = self
            .kernel
            .arena()
            .children(negation)
            .and_then(|mut children| children.next())
            .ok_or_else(|| Error::Malformed {
                message: "bool-eq-false negation has no operand".to_owned(),
            })?;
        join_same_syntax(&mut self.kernel, proposition, negated)?;

        let equality_assumption = self.kernel.identity(Lit::positive(equality.get()))?;
        let proposition_assumption = self.kernel.identity(Lit::positive(proposition.get()))?;
        let equality_implies_false = self
            .kernel
            .eq_mp(equality_assumption, proposition_assumption)?;
        self.kernel
            .not_right(equality_implies_false, Lit::positive(proposition.get()))?;
        let equality_implies_false = self
            .kernel
            .flatten_conclusion(equality_implies_false, Lit::positive(falsehood.get()))?;
        let equality_implies_negation = self
            .kernel
            .fold_conclusion(equality_implies_false, Lit::positive(negation.get()))?;

        let negation_assumption = self.kernel.identity(Lit::positive(negation.get()))?;
        let negation_assumption = self.kernel.expand_conclusion(
            negation_assumption,
            Lit::positive(negation.get()),
            None,
        )?;
        let proposition_assumption = self.kernel.identity(Lit::positive(proposition.get()))?;
        let contradiction = self.kernel.resolve(
            proposition_assumption,
            negation_assumption,
            Lit::positive(proposition.get()),
        )?;
        self.kernel
            .weaken(contradiction, &[], &[Lit::positive(falsehood.get())])?;
        let false_implies_proposition = self.kernel.false_left(Lit::positive(falsehood.get()))?;
        self.kernel.weaken(
            false_implies_proposition,
            &[],
            &[Lit::positive(proposition.get())],
        )?;
        let negation_implies_equality = self.kernel.deduct_antisym(
            self.bool_ty,
            proposition,
            falsehood,
            contradiction,
            false_implies_proposition,
        )?;
        let negation_implies_equality = self.convert_equality(
            negation_implies_equality.theorem,
            negation_implies_equality.equality,
            equality,
        )?;
        let result = self.kernel.deduct_antisym(
            self.bool_ty,
            equality,
            negation,
            equality_implies_negation,
            negation_implies_equality,
        )?;
        self.convert_equality(result.theorem, result.equality, target)
    }

    fn ite_constant(&mut self, clause: &[Lit], value: bool) -> Result<ThmId, Error> {
        let target = positive_unit(
            clause,
            if value {
                "ite-true-cond"
            } else {
                "ite-false-cond"
            },
        )?;
        let [_bool_ty, source, branch] = equality_children(&self.kernel, target)?;
        let cached = self.conditionals.clone();
        let conditional = cached
            .into_iter()
            .find_map(|(_, _, _, conditional)| {
                join_same_syntax(&mut self.kernel, conditional.term, source)
                    .ok()
                    .map(|_| conditional)
            })
            .ok_or_else(|| Error::Malformed {
                message: "ite rewrite does not name a lowered conditional".to_owned(),
            })?;
        if self.kernel.arena().bool_value(conditional.condition) != Some(value) {
            return Err(Error::Malformed {
                message: "ite rewrite condition is not the stated constant".to_owned(),
            });
        }
        let theorem = if value {
            conditional_when_true(&mut self.kernel, self.bool_ty, conditional)?
        } else {
            conditional_when_false(&mut self.kernel, self.bool_ty, conditional)?
        };
        let condition_equality = if value {
            conditional.condition_true
        } else {
            conditional.condition_false
        };
        let proved = self.kernel.refl(self.bool_ty, conditional.condition)?;
        let proved = self.convert_equality(proved.theorem, proved.equality, condition_equality)?;
        let theorem = self
            .kernel
            .cut(proved, theorem, Lit::positive(condition_equality.get()))?;
        let derived = positive_theorem_equality(&self.kernel, theorem)?;
        join_same_syntax(&mut self.kernel, conditional.term, source)?;
        join_same_syntax(
            &mut self.kernel,
            if value {
                conditional.then_branch
            } else {
                conditional.else_branch
            },
            branch,
        )?;
        self.convert_equality(theorem, derived, target)
    }

    fn xor_two(&mut self, clause: &[Lit], premises: &[ThmId]) -> Result<ThmId, Error> {
        let [premise] = premises else {
            return Err(Error::Malformed {
                message: "xor2 requires one premise".to_owned(),
            });
        };
        let [left_literal, right_literal] = clause else {
            return Err(Error::Malformed {
                message: "xor2 requires two literals".to_owned(),
            });
        };
        if left_literal.is_positive() || right_literal.is_positive() {
            return Err(Error::Unsupported {
                message: "xor2 polarity other than the negative pair".to_owned(),
            });
        }
        let source = conclusion_literals(&self.kernel, *premise)?;
        let [source] = source.as_slice() else {
            return Err(Error::Malformed {
                message: "xor2 premise must conclude one xor".to_owned(),
            });
        };
        let xor = reference(source.magnitude())?;
        let equality = self
            .kernel
            .arena()
            .children(xor)
            .and_then(|mut children| children.next())
            .ok_or_else(|| Error::Malformed {
                message: "xor2 premise is not a lowered xor".to_owned(),
            })?;
        let [_bool_ty, left, right] = equality_children(&self.kernel, equality)?;
        let truth = self.kernel.bool(self.bool_ty, true)?;
        let left_assumption = self.kernel.identity(Lit::positive(left.get()))?;
        let left_target = self.kernel.eq(self.bool_ty, left, truth)?;
        let left_true = self.equality_to_true(left, truth, left_assumption, left_target)?;
        let right_assumption = self.kernel.identity(Lit::positive(right.get()))?;
        let right_target = self.kernel.eq(self.bool_ty, right, truth)?;
        let right_true = self.equality_to_true(right, truth, right_assumption, right_target)?;
        let truth_right = equality_symmetry(&mut self.kernel, self.bool_ty, right_true)?;
        let equal = equality_transitivity(
            &mut self.kernel,
            self.bool_ty,
            left_true,
            truth_right.theorem,
        )?;
        let equal = self.convert_equality(equal.theorem, equal.equality, equality)?;
        let negative_equality = self.kernel.expand_conclusion(*premise, *source, None)?;
        let theorem = self.kernel.resolve(
            negative_equality,
            equal,
            Lit::positive(equality.get()).negated(),
        )?;
        self.kernel.not_right(theorem, Lit::positive(left.get()))?;
        self.kernel.not_right(theorem, Lit::positive(right.get()))?;
        self.kernel.contract_theorem(theorem)?;
        Ok(theorem)
    }

    fn xor_one(&mut self, clause: &[Lit], premises: &[ThmId]) -> Result<ThmId, Error> {
        let [premise] = premises else {
            return Err(Error::Malformed {
                message: "xor1 requires one premise".to_owned(),
            });
        };
        let [left_literal, right_literal] = clause else {
            return Err(Error::Malformed {
                message: "xor1 requires two literals".to_owned(),
            });
        };
        if !left_literal.is_positive() || !right_literal.is_positive() {
            return Err(Error::Unsupported {
                message: "xor1 polarity other than the positive pair".to_owned(),
            });
        }
        let source = conclusion_literals(&self.kernel, *premise)?;
        let [source] = source.as_slice() else {
            return Err(Error::Malformed {
                message: "xor1 premise must conclude one xor".to_owned(),
            });
        };
        let xor = reference(source.magnitude())?;
        let equality = self
            .kernel
            .arena()
            .children(xor)
            .and_then(|mut children| children.next())
            .ok_or_else(|| Error::Malformed {
                message: "xor1 premise is not a lowered xor".to_owned(),
            })?;
        let [_bool_ty, left, right] = equality_children(&self.kernel, equality)?;
        let falsehood = self.kernel.bool(self.bool_ty, false)?;
        let left_false = self.equality_under_negation(left, falsehood)?;
        let right_false = self.equality_under_negation(right, falsehood)?;
        let false_right = equality_symmetry(&mut self.kernel, self.bool_ty, right_false)?;
        let equal = equality_transitivity(
            &mut self.kernel,
            self.bool_ty,
            left_false,
            false_right.theorem,
        )?;
        let equal = self.convert_equality(equal.theorem, equal.equality, equality)?;
        let negative_equality = self.kernel.expand_conclusion(*premise, *source, None)?;
        let theorem = self.kernel.resolve(
            negative_equality,
            equal,
            Lit::positive(equality.get()).negated(),
        )?;
        self.kernel
            .not_right(theorem, Lit::positive(left.get()).negated())?;
        self.kernel
            .not_right(theorem, Lit::positive(right.get()).negated())?;
        self.kernel.contract_theorem(theorem)?;
        Ok(theorem)
    }

    fn xor_positive_two(&mut self, clause: &[Lit], premises: &[ThmId]) -> Result<ThmId, Error> {
        if !premises.is_empty() {
            return Err(Error::Malformed {
                message: "xor_pos2 does not take premises".to_owned(),
            });
        }
        let [negated_xor, left, right] = clause else {
            return Err(Error::Malformed {
                message: "xor_pos2 requires three literals".to_owned(),
            });
        };
        if negated_xor.is_positive() {
            return Err(Error::Malformed {
                message: "xor_pos2 must negate its xor".to_owned(),
            });
        }
        let xor = reference(negated_xor.magnitude())?;
        let assumption = self.kernel.identity(Lit::positive(xor.get()))?;
        let theorem = self.xor_two(&[*left, *right], &[assumption])?;
        self.kernel.not_right(theorem, Lit::positive(xor.get()))?;
        self.kernel.contract_theorem(theorem)?;
        Ok(theorem)
    }

    fn equality_under_negation(
        &mut self,
        proposition: Ref,
        falsehood: Ref,
    ) -> Result<ThmId, Error> {
        let positive = self.kernel.identity(Lit::positive(proposition.get()))?;
        let negative = self
            .kernel
            .identity(Lit::positive(proposition.get()).negated())?;
        let contradiction =
            self.kernel
                .resolve(positive, negative, Lit::positive(proposition.get()))?;
        self.kernel
            .weaken(contradiction, &[], &[Lit::positive(falsehood.get())])?;
        let false_implies_proposition = self.kernel.false_left(Lit::positive(falsehood.get()))?;
        self.kernel.weaken(
            false_implies_proposition,
            &[],
            &[Lit::positive(proposition.get())],
        )?;
        let equality = self.kernel.deduct_antisym(
            self.bool_ty,
            proposition,
            falsehood,
            contradiction,
            false_implies_proposition,
        )?;
        Ok(equality.theorem)
    }

    fn not_symmetry(&mut self, clause: &[Lit], premises: &[ThmId]) -> Result<ThmId, Error> {
        let [premise] = premises else {
            return Err(Error::Malformed {
                message: "not_symm requires one premise".to_owned(),
            });
        };
        let target = positive_unit(clause, "not_symm")?;
        let target_equality = self
            .kernel
            .arena()
            .children(target)
            .and_then(|mut children| children.next())
            .ok_or_else(|| Error::Malformed {
                message: "not_symm target is not a negation".to_owned(),
            })?;
        let source = conclusion_literals(&self.kernel, *premise)?;
        let [source] = source.as_slice() else {
            return Err(Error::Malformed {
                message: "not_symm premise must conclude one negation".to_owned(),
            });
        };
        let source_negation = reference(source.magnitude())?;
        let source_equality = self
            .kernel
            .arena()
            .children(source_negation)
            .and_then(|mut children| children.next())
            .ok_or_else(|| Error::Malformed {
                message: "not_symm premise is not a negation".to_owned(),
            })?;
        let negative_source = self.kernel.expand_conclusion(*premise, *source, None)?;
        let target_assumption = self.kernel.identity(Lit::positive(target_equality.get()))?;
        let symmetric = equality_symmetry(&mut self.kernel, self.bool_ty, target_assumption)?;
        let symmetric =
            self.convert_equality(symmetric.theorem, symmetric.equality, source_equality)?;
        let theorem = self.kernel.resolve(
            negative_source,
            symmetric,
            Lit::positive(source_equality.get()).negated(),
        )?;
        self.kernel
            .not_right(theorem, Lit::positive(target_equality.get()))?;
        let theorem = self
            .kernel
            .fold_conclusion(theorem, Lit::positive(target.get()))?;
        Ok(theorem)
    }

    /// Checks the Boolean constant folding `evaluate` states.
    ///
    /// Two gates run before any derivation. The stated equation must not be
    /// between numeric-sorted terms, and the proposition must be Boolean all
    /// the way down. Without them an arithmetic evaluation would be rejected
    /// only because a Boolean derivation happened not to apply, which is an
    /// accident rather than a decision, and it stops holding the moment
    /// arithmetic terms are lowerable at all.
    fn evaluate(&mut self, clause: &[Lit]) -> Result<ThmId, Error> {
        let target = positive_unit(clause, "evaluate")?;
        let [_bool_ty, proposition, constant] = equality_children(&self.kernel, target)?;
        for side in [proposition, constant] {
            if let Some(domain) = self.arithmetic_domain(side)? {
                return Err(Error::ArithmeticTheoryMissing {
                    step: String::new(),
                    rule: "evaluate".to_owned(),
                    domain: domain.to_owned(),
                });
            }
        }
        self.require_boolean_evaluable(proposition, 0)?;
        if self.kernel.arena().bool_value(constant) != Some(false) {
            return Err(Error::Unsupported {
                message: "evaluate result other than false".to_owned(),
            });
        }
        let left = self.kernel.identity(Lit::positive(proposition.get()))?;
        let left = self
            .kernel
            .flatten_conclusion(left, Lit::positive(proposition.get()))?;
        let conclusions = conclusion_literals(&self.kernel, left)?;
        if conclusions.is_empty() {
            self.kernel
                .weaken(left, &[], &[Lit::positive(constant.get())])?;
        } else if let [literal] = conclusions.as_slice()
            && !literal.is_positive()
        {
            let equality = reference(literal.magnitude())?;
            let [_domain, lhs, rhs] = equality_children(&self.kernel, equality)?;
            join_same_syntax(&mut self.kernel, lhs, rhs)?;
            let proved = self.kernel.refl(self.bool_ty, lhs)?;
            let proved = self.convert_equality(proved.theorem, proved.equality, equality)?;
            let contradiction = self.kernel.resolve(left, proved, *literal)?;
            self.kernel
                .weaken(contradiction, &[], &[Lit::positive(constant.get())])?;
            return self.equality_to_false(proposition, constant, contradiction, target);
        } else {
            return Err(Error::Unsupported {
                message: "evaluate expression does not reduce to false".to_owned(),
            });
        }
        let right = self.kernel.false_left(Lit::positive(constant.get()))?;
        self.kernel
            .weaken(right, &[], &[Lit::positive(proposition.get())])?;
        let result =
            self.kernel
                .deduct_antisym(self.bool_ty, proposition, constant, left, right)?;
        self.convert_equality(result.theorem, result.equality, target)
    }

    /// Returns the numeric sort of `term`, if it has one.
    fn arithmetic_domain(&self, term: Ref) -> Result<Option<&'static str>, Error> {
        let Ok(numeric) = self.numeric() else {
            return Ok(None);
        };
        let classifier = self.kernel.classifier(term)?;
        if self.kernel.equivalent(classifier, numeric.int_ty)? {
            return Ok(Some("integer"));
        }
        if self.kernel.equivalent(classifier, numeric.real_ty)? {
            return Ok(Some("rational"));
        }
        Ok(None)
    }

    /// Requires every node of a folded proposition to be Boolean structure.
    ///
    /// The one non-constant leaf allowed is an equality between operands the
    /// kernel already identifies, which reflexivity discharges and which is
    /// sort-agnostic.
    fn require_boolean_evaluable(&self, term: Ref, depth: usize) -> Result<(), Error> {
        if depth >= MAX_TERM_DEPTH {
            return Err(Error::TermTooDeep {
                limit: MAX_TERM_DEPTH,
            });
        }
        let arena = self.kernel.arena();
        if arena.bool_value(term).is_some() {
            return Ok(());
        }
        if arena.op1(term) == Some(Op1::Not)
            || matches!(arena.op2(term), Some(Op2::And | Op2::Or | Op2::Imp))
        {
            let children = arena
                .children(term)
                .ok_or_else(|| Error::Malformed {
                    message: "Boolean operator has no operands".to_owned(),
                })?
                .collect::<Vec<_>>();
            for child in children {
                self.require_boolean_evaluable(child, depth + 1)?;
            }
            return Ok(());
        }
        if arena.tag(term) == Some(Tag::Tm(TmTag::Eq)) {
            let [_domain, left, right] = equality_children(&self.kernel, term)?;
            if left == right || self.kernel.equivalent(left, right)? {
                return Ok(());
            }
        }
        // A numeric-sorted node, or one applied to numeric-sorted operands, is
        // arithmetic rather than merely unimplemented, and must say so.
        let mut candidates = vec![term];
        if let Some(children) = arena.children(term) {
            candidates.extend(children);
        }
        for candidate in candidates {
            if let Some(domain) = self.arithmetic_domain(candidate)? {
                return Err(Error::ArithmeticTheoryMissing {
                    step: String::new(),
                    rule: "evaluate".to_owned(),
                    domain: domain.to_owned(),
                });
            }
        }
        Err(Error::Unsupported {
            message: format!(
                "evaluate over a subterm this build cannot fold: {:?}",
                arena.tag(term)
            ),
        })
    }

    fn equality_to_false(
        &mut self,
        proposition: Ref,
        falsehood: Ref,
        proposition_implies_false: ThmId,
        target: Ref,
    ) -> Result<ThmId, Error> {
        let false_implies_proposition = self.kernel.false_left(Lit::positive(falsehood.get()))?;
        self.kernel.weaken(
            false_implies_proposition,
            &[],
            &[Lit::positive(proposition.get())],
        )?;
        let result = self.kernel.deduct_antisym(
            self.bool_ty,
            proposition,
            falsehood,
            proposition_implies_false,
            false_implies_proposition,
        )?;
        self.convert_equality(result.theorem, result.equality, target)
    }

    fn equality_to_true(
        &mut self,
        proposition: Ref,
        truth: Ref,
        proposition_theorem: ThmId,
        target: Ref,
    ) -> Result<ThmId, Error> {
        let truth_theorem = self.kernel.true_right(Lit::positive(truth.get()))?;
        let result = self.kernel.deduct_antisym(
            self.bool_ty,
            proposition,
            truth,
            truth_theorem,
            proposition_theorem,
        )?;
        self.convert_equality(result.theorem, result.equality, target)
    }

    fn false_rule(&mut self, clause: &[Lit]) -> Result<ThmId, Error> {
        let [literal] = clause else {
            return Err(Error::Malformed {
                message: "false requires one literal".to_owned(),
            });
        };
        if literal.is_positive() {
            return Err(Error::Malformed {
                message: "false requires a negative literal".to_owned(),
            });
        }
        let falsehood =
            Lit::positive(
                i32::try_from(literal.magnitude()).map_err(|_| Error::Malformed {
                    message: "false literal exceeds the checked arena".to_owned(),
                })?,
            );
        let theorem = self.kernel.false_left(falsehood)?;
        self.kernel.not_right(theorem, falsehood)?;
        Ok(theorem)
    }

    fn resolution(&mut self, premises: &[ThmId]) -> Result<ThmId, Error> {
        let (first, rest) = premises.split_first().ok_or_else(|| Error::Malformed {
            message: "resolution has no premises".to_owned(),
        })?;
        let mut result = *first;
        for &next in rest {
            let mut next = next;
            let left = conclusion_literals(&self.kernel, result)?;
            let right = conclusion_literals(&self.kernel, next)?;
            let mut pivot = left
                .iter()
                .find(|literal| right.contains(&literal.negated()))
                .copied();
            if pivot.is_none() {
                'candidate: for &left_literal in &left {
                    for &right_literal in &right {
                        if left_literal.is_positive() == right_literal.is_positive() {
                            continue;
                        }
                        let left_reference = reference(left_literal.magnitude())?;
                        let right_reference = reference(right_literal.magnitude())?;
                        if join_same_syntax(&mut self.kernel, left_reference, right_reference)
                            .is_ok()
                        {
                            self.kernel.convert_conclusions(
                                next,
                                right_reference,
                                left_reference,
                            )?;
                            pivot = Some(left_literal);
                            break 'candidate;
                        }
                    }
                }
            }
            // CVC5 sometimes resolves a singleton `(not p)` assumption as
            // the negative literal `p`, but in other proofs resolves the
            // exact named negation as an atom. Prefer exact atoms above and
            // only expose the logical clause view when that cannot resolve.
            if pivot.is_none()
                && right.len() == 1
                && right[0].is_positive()
                && self.kernel.arena().op1(reference(right[0].magnitude())?) == Some(Op1::Not)
            {
                next = self.kernel.expand_conclusion(next, right[0], None)?;
                let flattened = conclusion_literals(&self.kernel, next)?;
                pivot = left
                    .iter()
                    .find(|literal| flattened.contains(&literal.negated()))
                    .copied();
            }
            if pivot.is_none() {
                for &literal in &left {
                    if !literal.is_positive() {
                        continue;
                    }
                    let formula = reference(literal.magnitude())?;
                    if self.kernel.arena().op1(formula) != Some(Op1::Not) {
                        continue;
                    }
                    let Some(child) = self
                        .kernel
                        .arena()
                        .children(formula)
                        .and_then(|mut children| children.next())
                    else {
                        continue;
                    };
                    if right.contains(&Lit::positive(child.get())) {
                        result = self.kernel.flatten_conclusion(result, literal)?;
                        pivot = Some(Lit::positive(child.get()).negated());
                        break;
                    }
                }
            }
            let pivot = pivot.ok_or_else(|| Error::Malformed {
                message: "resolution premises have no complementary pivot".to_owned(),
            })?;
            result = self.kernel.resolve(result, next, pivot)?;
        }
        self.kernel.contract_theorem(result)?;
        Ok(result)
    }

    fn reflexivity(&mut self, clause: &[Lit]) -> Result<ThmId, Error> {
        let target = positive_unit(clause, "refl")?;
        let [_domain, left, right] = equality_children(&self.kernel, target)?;
        join_same_syntax(&mut self.kernel, left, right)?;
        let result = self.kernel.refl(self.bool_ty, left)?;
        self.convert_equality(result.theorem, result.equality, target)
    }

    fn symmetry(&mut self, clause: &[Lit], premises: &[ThmId]) -> Result<ThmId, Error> {
        let [premise] = premises else {
            return Err(Error::Malformed {
                message: "symm requires one premise".to_owned(),
            });
        };
        let target = positive_unit(clause, "symm")?;
        let result = equality_symmetry(&mut self.kernel, self.bool_ty, *premise)?;
        self.convert_equality(result.theorem, result.equality, target)
    }

    fn transitivity(&mut self, clause: &[Lit], premises: &[ThmId]) -> Result<ThmId, Error> {
        let (first, rest) = premises.split_first().ok_or_else(|| Error::Malformed {
            message: "trans requires premises".to_owned(),
        })?;
        let mut theorem = *first;
        let mut equality = positive_theorem_equality(&self.kernel, theorem)?;
        for &next in rest {
            let result = equality_transitivity(&mut self.kernel, self.bool_ty, theorem, next)?;
            theorem = result.theorem;
            equality = result.equality;
        }
        self.convert_equality(theorem, equality, positive_unit(clause, "trans")?)
    }

    #[allow(clippy::too_many_lines)]
    fn congruence(&mut self, clause: &[Lit], premises: &[ThmId]) -> Result<ThmId, Error> {
        let target = positive_unit(clause, "cong")?;
        let [domain, compact_left, compact_right] = equality_children(&self.kernel, target)?;
        if let Some(theorem) =
            self.conditional_congruence(target, compact_left, compact_right, premises)?
        {
            return Ok(theorem);
        }
        if let Some(theorem) =
            self.equality_congruence(target, compact_left, compact_right, premises)?
        {
            return Ok(theorem);
        }
        let left_expansion = self.kernel.lower_logical_tree(&self.init, compact_left)?;
        let right_expansion = self.kernel.lower_logical_tree(&self.init, compact_right)?;
        let left = left_expansion.raw;
        let right = right_expansion.raw;
        let (left_head, left_args) = application_spine(&self.kernel, left)?;
        let (right_head, right_args) = application_spine(&self.kernel, right)?;
        if left_args.is_empty() && right_args.is_empty() && premises.len() == 2 {
            let left_proved = positive_theorem_equality(&self.kernel, premises[0])?;
            let right_proved = positive_theorem_equality(&self.kernel, premises[1])?;
            if join_same_syntax(&mut self.kernel, left_proved, compact_left).is_ok()
                && join_same_syntax(&mut self.kernel, right_proved, compact_right).is_ok()
            {
                self.kernel
                    .convert_conclusions(premises[0], left_proved, compact_left)?;
                self.kernel
                    .convert_conclusions(premises[1], right_proved, compact_right)?;
                let truth = self.kernel.bool(self.bool_ty, true)?;
                let left_target = self.kernel.eq(self.bool_ty, compact_left, truth)?;
                let left_true =
                    self.equality_to_true(compact_left, truth, premises[0], left_target)?;
                let right_target = self.kernel.eq(self.bool_ty, compact_right, truth)?;
                let right_true =
                    self.equality_to_true(compact_right, truth, premises[1], right_target)?;
                let right_true = equality_symmetry(&mut self.kernel, self.bool_ty, right_true)?;
                let combined = equality_transitivity(
                    &mut self.kernel,
                    self.bool_ty,
                    left_true,
                    right_true.theorem,
                )?;
                return self.convert_equality(combined.theorem, combined.equality, target);
            }
        }
        if left_args.len() != premises.len() || right_args.len() != premises.len() {
            return Err(Error::Malformed {
                message: format!(
                    "cong premise count {} does not match application arities {} and {} for {compact_left:?} {:?} and {compact_right:?} {:?}; conditional terms {:?}",
                    premises.len(),
                    left_args.len(),
                    right_args.len(),
                    self.kernel.arena().tag(compact_left),
                    self.kernel.arena().tag(compact_right),
                    self.conditionals
                        .iter()
                        .map(|entry| entry.3.term)
                        .collect::<Vec<_>>(),
                ),
            });
        }
        join_same_syntax(&mut self.kernel, left_head, right_head)?;
        let proved = self.kernel.refl(self.bool_ty, left_head)?;
        let mut theorem = proved.theorem;
        let mut equality = proved.equality;
        let mut right_function = right_head;
        for ((&left_arg, &right_arg), &premise) in left_args.iter().zip(&right_args).zip(premises) {
            let [_argument_ty, premise_left, premise_right] = equality_children(
                &self.kernel,
                positive_theorem_equality(&self.kernel, premise)?,
            )?;
            join_same_syntax(&mut self.kernel, premise_left, left_arg)?;
            join_same_syntax(&mut self.kernel, premise_right, right_arg)?;
            let applied_function = self.kernel.ap_thm(theorem, left_arg)?;
            let applied_argument = self.kernel.ap_term(premise, right_function)?;
            let combined = equality_transitivity(
                &mut self.kernel,
                self.bool_ty,
                applied_function.theorem,
                applied_argument.theorem,
            )?;
            theorem = combined.theorem;
            equality = combined.equality;
            right_function = applied_argument.right;
        }
        let raw_target = self.kernel.eq(self.bool_ty, left, right)?;
        join_same_syntax(&mut self.kernel, equality, raw_target)?;
        self.kernel
            .convert_conclusions(theorem, equality, raw_target)?;
        // An equality row stores its operand type as its first child, so the
        // conversion evidence must be reflexivity on that type rather than on
        // the Boolean result type. The two coincide only when the congruence
        // relates Boolean-sorted operands.
        let classifier = self.kernel.syn_refl(None, SynRel::Conv, domain)?;
        let left = self.kernel.syn_symm(None, left_expansion.fact)?;
        let right = self.kernel.syn_symm(None, right_expansion.fact)?;
        let conversion = self.kernel.syn_congr(
            None,
            SynRel::Conv,
            None,
            None,
            raw_target,
            target,
            &[classifier, left, right],
        )?;
        self.kernel.union_syn_fact(conversion)?;
        self.kernel
            .convert_conclusions(theorem, raw_target, target)?;
        Ok(theorem)
    }

    #[allow(clippy::too_many_lines)]
    fn conditional_congruence(
        &mut self,
        target: Ref,
        left: Ref,
        right: Ref,
        premises: &[ThmId],
    ) -> Result<Option<ThmId>, Error> {
        let cached = self.conditionals.clone();
        let left_conditional = cached.iter().find_map(|(_, _, _, conditional)| {
            (conditional.term == left)
                .then_some(*conditional)
                .or_else(|| {
                    join_same_syntax(&mut self.kernel, conditional.term, left)
                        .ok()
                        .map(|_| *conditional)
                })
        });
        let right_conditional = cached.iter().find_map(|(_, _, _, conditional)| {
            (conditional.term == right)
                .then_some(*conditional)
                .or_else(|| {
                    join_same_syntax(&mut self.kernel, conditional.term, right)
                        .ok()
                        .map(|_| *conditional)
                })
        });
        let (Some(left_conditional), Some(right_conditional)) =
            (left_conditional, right_conditional)
        else {
            if left_conditional.is_some() || right_conditional.is_some() {
                return Err(Error::Malformed {
                    message: format!(
                        "cong relates one lowered conditional: left={}, right={}",
                        left_conditional.is_some(),
                        right_conditional.is_some()
                    ),
                });
            }
            return Ok(None);
        };
        let Some(value) = self.kernel.arena().bool_value(right_conditional.condition) else {
            return Ok(None);
        };
        if join_same_syntax(
            &mut self.kernel,
            left_conditional.then_branch,
            right_conditional.then_branch,
        )
        .is_err()
            || join_same_syntax(
                &mut self.kernel,
                left_conditional.else_branch,
                right_conditional.else_branch,
            )
            .is_err()
        {
            return Ok(None);
        }
        let [condition_premise, ..] = premises else {
            return Err(Error::Malformed {
                message: "conditional congruence has no condition premise".to_owned(),
            });
        };
        let condition_equality = positive_theorem_equality(&self.kernel, *condition_premise)?;
        let left_condition_equality = if value {
            left_conditional.condition_true
        } else {
            left_conditional.condition_false
        };
        self.convert_equality(
            *condition_premise,
            condition_equality,
            left_condition_equality,
        )?;

        let left_law = if value {
            conditional_when_true(&mut self.kernel, self.bool_ty, left_conditional)?
        } else {
            conditional_when_false(&mut self.kernel, self.bool_ty, left_conditional)?
        };
        let left_law = self.kernel.cut(
            *condition_premise,
            left_law,
            Lit::positive(left_condition_equality.get()),
        )?;

        let right_condition_equality = if value {
            right_conditional.condition_true
        } else {
            right_conditional.condition_false
        };
        let right_condition = self
            .kernel
            .refl(self.bool_ty, right_conditional.condition)?;
        let right_condition = self.convert_equality(
            right_condition.theorem,
            right_condition.equality,
            right_condition_equality,
        )?;
        let right_law = if value {
            conditional_when_true(&mut self.kernel, self.bool_ty, right_conditional)?
        } else {
            conditional_when_false(&mut self.kernel, self.bool_ty, right_conditional)?
        };
        let right_law = self.kernel.cut(
            right_condition,
            right_law,
            Lit::positive(right_condition_equality.get()),
        )?;
        let right_law = equality_symmetry(&mut self.kernel, self.bool_ty, right_law)?;
        let result =
            equality_transitivity(&mut self.kernel, self.bool_ty, left_law, right_law.theorem)?;
        self.convert_equality(result.theorem, result.equality, target)
            .map(Some)
    }

    fn equality_congruence(
        &mut self,
        target: Ref,
        left: Ref,
        right: Ref,
        premises: &[ThmId],
    ) -> Result<Option<ThmId>, Error> {
        if self.kernel.arena().tag(left) != Some(Tag::Tm(TmTag::Eq))
            || self.kernel.arena().tag(right) != Some(Tag::Tm(TmTag::Eq))
        {
            return Ok(None);
        }
        let [_left_ty, left_left, left_right] = equality_children(&self.kernel, left)?;
        let [_right_ty, right_left, right_right] = equality_children(&self.kernel, right)?;
        let left_operands = self.operand_equality(left_left, right_left, premises)?;
        let right_operands = self.operand_equality(left_right, right_right, premises)?;

        let left_reversed = equality_symmetry(&mut self.kernel, self.bool_ty, left_operands)?;
        let left_identity = self.kernel.identity(Lit::positive(left.get()))?;
        let forward = equality_transitivity(
            &mut self.kernel,
            self.bool_ty,
            left_reversed.theorem,
            left_identity,
        )?;
        let forward = equality_transitivity(
            &mut self.kernel,
            self.bool_ty,
            forward.theorem,
            right_operands,
        )?;
        let forward = self.convert_equality(forward.theorem, forward.equality, right)?;

        let right_reversed = equality_symmetry(&mut self.kernel, self.bool_ty, right_operands)?;
        let right_identity = self.kernel.identity(Lit::positive(right.get()))?;
        let backward = equality_transitivity(
            &mut self.kernel,
            self.bool_ty,
            left_operands,
            right_identity,
        )?;
        let backward = equality_transitivity(
            &mut self.kernel,
            self.bool_ty,
            backward.theorem,
            right_reversed.theorem,
        )?;
        let backward = self.convert_equality(backward.theorem, backward.equality, left)?;
        let result = self
            .kernel
            .deduct_antisym(self.bool_ty, left, right, forward, backward)?;
        self.convert_equality(result.theorem, result.equality, target)
            .map(Some)
    }

    fn operand_equality(
        &mut self,
        left: Ref,
        right: Ref,
        premises: &[ThmId],
    ) -> Result<ThmId, Error> {
        let target = self.kernel.eq(self.bool_ty, left, right)?;
        if join_same_syntax(&mut self.kernel, left, right).is_ok() {
            let proved = self.kernel.refl(self.bool_ty, left)?;
            return self.convert_equality(proved.theorem, proved.equality, target);
        }
        for &premise in premises {
            let source = positive_theorem_equality(&self.kernel, premise)?;
            let [_ty, source_left, source_right] = equality_children(&self.kernel, source)?;
            if join_same_syntax(&mut self.kernel, source_left, left).is_ok()
                && join_same_syntax(&mut self.kernel, source_right, right).is_ok()
            {
                let theorem = self.kernel.copy_theorem(premise)?;
                return self.convert_equality(theorem, source, target);
            }
            if join_same_syntax(&mut self.kernel, source_left, right).is_ok()
                && join_same_syntax(&mut self.kernel, source_right, left).is_ok()
            {
                let reversed = equality_symmetry(&mut self.kernel, self.bool_ty, premise)?;
                return self.convert_equality(reversed.theorem, reversed.equality, target);
            }
        }
        Err(Error::Malformed {
            message: "cong has no premise for a changed equality operand".to_owned(),
        })
    }

    fn equiv_pos2(&mut self, clause: &[Lit]) -> Result<ThmId, Error> {
        let [not_equality, _, _] = clause else {
            return Err(Error::Malformed {
                message: "equiv_pos2 requires three literals".to_owned(),
            });
        };
        if not_equality.is_positive() {
            return Err(Error::Malformed {
                message: "equiv_pos2 has invalid polarities".to_owned(),
            });
        }
        let equality = reference(not_equality.magnitude())?;
        let [_domain, left, _right] = equality_children(&self.kernel, equality)?;
        let equality_identity = self.kernel.identity(not_equality.negated())?;
        let left_identity = self.kernel.identity(Lit::positive(left.get()))?;
        let result = self.kernel.eq_mp(equality_identity, left_identity)?;
        self.kernel.not_right(result, not_equality.negated())?;
        self.kernel.not_right(result, Lit::positive(left.get()))?;
        self.kernel.contract_theorem(result)?;
        Ok(result)
    }

    fn convert_equality(
        &mut self,
        theorem: ThmId,
        source: Ref,
        target: Ref,
    ) -> Result<ThmId, Error> {
        if !self.kernel.equivalent(source, target)? {
            join_same_syntax(&mut self.kernel, source, target)?;
        }
        self.kernel.convert_conclusions(theorem, source, target)?;
        Ok(theorem)
    }

    fn check_clause(
        &mut self,
        step: &str,
        theorem: ThmId,
        expected: &[Lit],
    ) -> Result<ThmId, Error> {
        let mut actual = conclusion_literals(&self.kernel, theorem)?;
        for &literal in expected {
            let reference = reference(literal.magnitude())?;
            let is_false = matches!(
                (
                    literal.is_positive(),
                    self.kernel.arena().bool_value(reference)
                ),
                (true, Some(false)) | (false, Some(true))
            );
            if is_false && !actual.contains(&literal) {
                self.kernel.weaken(theorem, &[], &[literal])?;
            }
        }
        actual = conclusion_literals(&self.kernel, theorem)?;
        let mut expected = expected.to_vec();
        actual.sort_unstable();
        expected.sort_unstable();
        if actual != expected {
            for wanted in &expected {
                let wanted_reference = reference(wanted.magnitude())?;
                for candidate in &actual {
                    if candidate.is_positive() != wanted.is_positive() {
                        continue;
                    }
                    let candidate_reference = reference(candidate.magnitude())?;
                    if join_same_syntax(&mut self.kernel, candidate_reference, wanted_reference)
                        .is_ok()
                    {
                        self.kernel.convert_conclusions(
                            theorem,
                            candidate_reference,
                            wanted_reference,
                        )?;
                    }
                }
            }
            self.kernel.contract_theorem(theorem)?;
            actual = conclusion_literals(&self.kernel, theorem)?;
            actual.sort_unstable();
        }
        if actual != expected {
            let canonical_actual = actual
                .iter()
                .copied()
                .map(|literal| canonical_clause_literal(&self.kernel, literal))
                .collect::<Result<Vec<_>, _>>()?;
            let canonical_expected = expected
                .iter()
                .copied()
                .map(|literal| canonical_clause_literal(&self.kernel, literal))
                .collect::<Result<Vec<_>, _>>()?;
            if canonical_actual == canonical_expected {
                return Ok(theorem);
            }
            return Err(Error::ClauseMismatch {
                step: step.to_owned(),
                actual,
                expected,
            });
        }
        Ok(theorem)
    }

    fn check_exact_goal(&self, theorem: ThmId) -> Result<(), Error> {
        // This check inspects the refutation's own sequent only, so a rule
        // handler holding `&mut Kernel` could otherwise reach `tm_ref` or
        // `import_literal`, assume an unchecked `hol.sort` predicate with a
        // caller-asserted type, and pass every other gate.
        let ambient = self.kernel.arena().ambient_predicates();
        if ambient != self.ambient.as_slice() {
            return Err(Error::Malformed {
                message: format!(
                    "replay changed the ambient predicate context from {:?} to {ambient:?}",
                    self.ambient
                ),
            });
        }
        let value = self
            .kernel
            .thm()
            .get(theorem)
            .ok_or_else(|| Error::Malformed {
                message: format!("missing theorem {theorem:?}"),
            })?;
        if value.rhs.rows().next().is_some() {
            return Err(Error::NoRefutation);
        }
        let actual = value
            .lhs
            .rows()
            .map(|row| match row {
                [literal] => Ok(*literal),
                _ => Err(Error::Malformed {
                    message: "refutation contains a non-unit premise".to_owned(),
                }),
            })
            .collect::<Result<BTreeSet<_>, _>>()?;
        let expected = self.assertions.iter().copied().collect::<BTreeSet<_>>();
        if actual != expected {
            return Err(Error::Malformed {
                message: format!(
                    "refutation is not bound to the exact assertion set: actual {actual:?}, expected {expected:?}"
                ),
            });
        }
        Ok(())
    }
}

/// Pushes object-level negations into a lowered literal's polarity.
///
/// Two spellings of one Alethe literal, the sequent-level negative literal on
/// `a` and any `tm.not` row over it, reduce to the same result, which is what
/// makes the subproof discharge check independent of how cvc5 printed the
/// clause.
fn strip_negations(kernel: &Kernel, literal: Lit) -> Result<Lit, Error> {
    let mut literal = literal;
    loop {
        let formula = reference(literal.magnitude())?;
        if kernel.arena().op1(formula) != Some(Op1::Not) {
            return Ok(literal);
        }
        let child = kernel
            .arena()
            .children(formula)
            .and_then(|mut children| children.next())
            .ok_or_else(|| Error::Malformed {
                message: "negation has no operand".to_owned(),
            })?;
        let positive = Lit::positive(child.get());
        literal = if literal.is_positive() {
            positive.negated()
        } else {
            positive
        };
    }
}

fn canonical_clause_literal(kernel: &Kernel, literal: Lit) -> Result<Lit, Error> {
    if !literal.is_positive() {
        return Ok(literal);
    }
    let formula = reference(literal.magnitude())?;
    if kernel.arena().op1(formula) != Some(Op1::Not) {
        return Ok(literal);
    }
    let child = kernel
        .arena()
        .children(formula)
        .and_then(|mut children| children.next())
        .ok_or_else(|| Error::Malformed {
            message: "negation has no operand".to_owned(),
        })?;
    Ok(Lit::positive(child.get()).negated())
}

/// Replays a `QF_UF` Alethe proof and binds its empty-clause theorem to the
/// exact normalized assertion set from `problem`.
///
/// # Errors
///
/// Returns [`Error`] for unsupported syntax or rules, unasserted assumptions,
/// missing premises, mismatched clauses, or any rejected checked derivation.
pub fn replay_qf_uf(problem: &SmtProblem, proof: &AletheProof) -> Result<Refutation, Error> {
    replay_qf_uf_with_handler(problem, proof, &mut RejectUnknownRules)
}

/// Replays a `QF_UF` proof with a checked userspace fallback for unknown rules.
///
/// Handler results pass the same exact-clause and final assertion-set checks as
/// built-in replay rules.
///
/// # Errors
///
/// Returns [`Error`] under the same conditions as [`replay_qf_uf`], or when
/// `handler` rejects a rule it recognizes.
pub fn replay_qf_uf_with_handler(
    problem: &SmtProblem,
    proof: &AletheProof,
    handler: &mut impl RuleHandler,
) -> Result<Refutation, Error> {
    let mut replayer = Replayer::new(Logic::QfUf)?;
    replayer.ingest_problem(problem)?;
    replayer.ingest_proof(proof, handler)
}

/// Lowers a `QF_UFLIA` problem and proof into checked rows and reports the
/// first arithmetic rule this build cannot check.
///
/// This proves nothing, and the returned [`Lowering`] deliberately offers no
/// theorem, no theorem index, and no conversion into a [`Refutation`]. There
/// is also no handler-taking variant: the extension point is not offered on
/// this path, because filling the arithmetic gap from userspace is exactly
/// what must not happen while no HOL theory in this tree states arithmetic.
/// Issue 1208 tracks the checked arithmetic that would change this.
///
/// # Errors
///
/// Returns [`Error`] for unsupported syntax, unasserted assumptions, missing
/// premises, mismatched clauses, or any rejected checked derivation, and
/// [`Error::NoArithmeticGap`] if the proof replayed to its end, which this
/// build must not certify.
pub fn lower_qf_uflia(problem: &SmtProblem, proof: &AletheProof) -> Result<Lowering, Error> {
    let mut replayer = Replayer::new(Logic::QfUflia)?;
    replayer.ingest_problem(problem)?;
    replayer.lower_proof(proof)
}

impl Error {
    /// Attaches the Alethe step index to an error raised while checking it.
    fn at_step(self, step: &str) -> Self {
        match self {
            Self::ArithmeticTheoryMissing {
                step: stated,
                rule,
                domain,
            } if stated.is_empty() => Self::ArithmeticTheoryMissing {
                step: step.to_owned(),
                rule,
                domain,
            },
            other => other,
        }
    }
}

/// Names the arithmetic domain a top-level Alethe rule reasons in.
///
/// `poly_simp` and `poly_simp_rel` are cvc5 Alethe extensions rather than base
/// specification rules; they are listed because cvc5 emits them more than any
/// other arithmetic rule.
fn arithmetic_rule_domain(rule: &str) -> Option<&'static str> {
    match rule {
        "poly_simp" | "poly_simp_rel" | "la_generic" | "la_mult_pos" | "la_mult_neg"
        | "la_disequality" | "la_rw_eq" | "la_totality" | "la_tautology" | "comp_simplify"
        | "div_intro" => Some("integer or rational"),
        _ => None,
    }
}

/// Names the arithmetic domain a RARE rewrite reasons in.
fn rare_rewrite_arithmetic_domain(name: &str) -> Option<&'static str> {
    (name.starts_with("arith-") || matches!(name, "mod-elim" | "div-elim"))
        .then_some("integer or rational")
}

/// Rejects a premise on a RARE rewrite that states its conclusion outright.
fn require_no_premises(name: &str, premises: &[ThmId]) -> Result<(), Error> {
    if premises.is_empty() {
        return Ok(());
    }
    Err(Error::Malformed {
        message: format!(
            "rare_rewrite {name:?} takes no premises, got {}",
            premises.len()
        ),
    })
}

/// Returns whether a symbol spelling can only be a signed numeral.
///
/// The reader classifies an atom whose first byte is a digit as a number, so a
/// numeral reaches the symbol arm only carrying its sign.
fn signed_numeral_spelling(spelling: &str) -> bool {
    spelling
        .strip_prefix('-')
        .is_some_and(|rest| rest.starts_with(|character: char| character.is_ascii_digit()))
}

/// Classifies one canonical numeral spelling, rejecting every other one.
///
/// Non-canonical spellings are rejected rather than normalized, so there is no
/// second place where two spellings of one value could disagree.
fn numeral_kind(spelling: &str) -> Option<NumeralKind> {
    let (negative, body) = match spelling.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, spelling),
    };
    let kind = match body.split_once('/') {
        None if canonical_natural(body) => NumeralKind::Integer,
        Some((numerator, denominator))
            if canonical_natural(numerator) && positive_natural(denominator) =>
        {
            NumeralKind::Rational
        }
        _ => return None,
    };
    // A zero magnitude has one canonical spelling, so the signed one is not it.
    if negative && body.starts_with('0') {
        return None;
    }
    Some(kind)
}

/// Matches `0 | [1-9][0-9]*`, so `007` and the empty spelling are rejected.
fn canonical_natural(digits: &str) -> bool {
    match digits.as_bytes() {
        [b'0'] => true,
        [first, rest @ ..] if first.is_ascii_digit() && *first != b'0' => {
            rest.iter().all(u8::is_ascii_digit)
        }
        _ => false,
    }
}

/// Matches `[1-9][0-9]*`, so a rational denominator is never zero.
fn positive_natural(digits: &str) -> bool {
    digits != "0" && canonical_natural(digits)
}

/// Returns whether `literal` occurs as a unit row in a theorem's antecedent.
fn has_unit_premise(kernel: &Kernel, theorem: ThmId, literal: Lit) -> Result<bool, Error> {
    let value = kernel.thm().get(theorem).ok_or_else(|| Error::Malformed {
        message: format!("missing theorem {theorem:?}"),
    })?;
    Ok(value
        .lhs
        .rows()
        .any(|row| matches!(row, [single] if *single == literal)))
}

/// Requires the SMT-LIB Core minimum arity shared by `and`, `or` and `=>`.
fn arity_at_least_two<'a>(
    operator: &str,
    arguments: &'a [Expr],
) -> Result<(&'a Expr, &'a [Expr]), Error> {
    match arguments.split_first() {
        Some((first, rest)) if !rest.is_empty() => Ok((first, rest)),
        _ => Err(Error::Malformed {
            message: format!(
                "{operator} requires at least two arguments, got {}",
                arguments.len()
            ),
        }),
    }
}

fn symbol(expression: &Expr) -> Result<&str, Error> {
    match expression.node() {
        ExprKind::Atom(node) => match SpannedRepr::atom(node) {
            Atom::Symbol(value) => Ok(value),
            _ => Err(Error::Malformed {
                message: "expected a symbol".to_owned(),
            }),
        },
        ExprKind::List(_) => Err(Error::Malformed {
            message: "expected a symbol".to_owned(),
        }),
    }
}

fn string_value(expression: &Expr) -> Option<&str> {
    match expression.node() {
        ExprKind::Atom(node) => match SpannedRepr::atom(node) {
            Atom::String(value) => Some(value),
            _ => None,
        },
        ExprKind::List(_) => None,
    }
}

fn number_value(expression: &Expr) -> Result<&str, Error> {
    match expression.node() {
        ExprKind::Atom(node) => match SpannedRepr::atom(node) {
            Atom::Number(value) => Ok(value),
            _ => Err(Error::Malformed {
                message: "expected a numeric argument".to_owned(),
            }),
        },
        ExprKind::List(_) => Err(Error::Malformed {
            message: "expected a numeric argument".to_owned(),
        }),
    }
}

fn keyword(expression: &Expr) -> Result<&str, Error> {
    match expression.node() {
        ExprKind::Atom(node) => match SpannedRepr::atom(node) {
            Atom::Keyword(value) => Ok(value),
            _ => Err(Error::Malformed {
                message: "expected an attribute".to_owned(),
            }),
        },
        ExprKind::List(_) => Err(Error::Malformed {
            message: "expected an attribute".to_owned(),
        }),
    }
}

fn reference(magnitude: u32) -> Result<Ref, Error> {
    let value = i32::try_from(magnitude).map_err(|_| Error::Malformed {
        message: "literal reference exceeds i32".to_owned(),
    })?;
    Ref::new(value).ok_or_else(|| Error::Malformed {
        message: "literal references are one-based".to_owned(),
    })
}

fn positive_unit(clause: &[Lit], rule: &str) -> Result<Ref, Error> {
    let [literal] = clause else {
        return Err(Error::Malformed {
            message: format!("{rule} requires a unit clause"),
        });
    };
    if !literal.is_positive() {
        return Err(Error::Malformed {
            message: format!("{rule} requires a positive equality"),
        });
    }
    reference(literal.magnitude())
}

fn equality_children(kernel: &Kernel, equality: Ref) -> Result<[Ref; 3], Error> {
    if kernel.arena().tag(equality) != Some(Tag::Tm(TmTag::Eq)) {
        return Err(Error::Malformed {
            message: "expected an equality term".to_owned(),
        });
    }
    kernel
        .arena()
        .children(equality)
        .ok_or_else(|| Error::Malformed {
            message: "equality has no children".to_owned(),
        })?
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|_| Error::Malformed {
            message: "equality has the wrong arity".to_owned(),
        })
}

fn positive_theorem_equality(kernel: &Kernel, theorem: ThmId) -> Result<Ref, Error> {
    let value = kernel.thm().get(theorem).ok_or_else(|| Error::Malformed {
        message: format!("missing theorem {theorem:?}"),
    })?;
    let rows = value.rhs.rows().collect::<Vec<_>>();
    match rows.as_slice() {
        [row] if row.len() == 1 && row[0].is_positive() => reference(row[0].magnitude()),
        _ => Err(Error::Malformed {
            message: "premise does not conclude one positive equality".to_owned(),
        }),
    }
}

fn conclusion_literals(kernel: &Kernel, theorem: ThmId) -> Result<Vec<Lit>, Error> {
    kernel
        .thm()
        .get(theorem)
        .ok_or_else(|| Error::Malformed {
            message: format!("missing theorem {theorem:?}"),
        })?
        .rhs
        .rows()
        .map(|row| match row {
            [literal] => Ok(*literal),
            _ => Err(Error::Malformed {
                message: "Alethe clause theorem contains a non-unit DNF row".to_owned(),
            }),
        })
        .collect()
}

fn conjunction_arity(kernel: &Kernel, term: Ref) -> usize {
    if kernel.arena().op2(term) != Some(Op2::And) {
        return 1;
    }
    kernel
        .arena()
        .children(term)
        .expect("a checked binary operator has children")
        .map(|child| conjunction_arity(kernel, child))
        .sum()
}

fn application_spine(kernel: &Kernel, mut term: Ref) -> Result<(Ref, Vec<Ref>), Error> {
    let mut reversed = Vec::new();
    while kernel.arena().tag(term) == Some(Tag::Tm(TmTag::App)) {
        let children = kernel
            .arena()
            .children(term)
            .ok_or_else(|| Error::Malformed {
                message: "application has no children".to_owned(),
            })?
            .collect::<Vec<_>>();
        let [function, argument] = children.as_slice() else {
            return Err(Error::Malformed {
                message: "application has the wrong arity".to_owned(),
            });
        };
        term = *function;
        reversed.push(*argument);
    }
    reversed.reverse();
    Ok((term, reversed))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parse_alethe, parse_cvc5_output, parse_smtlib2};
    use covalence_logic_hol::{KindTag, TyTag};
    use std::io::Write as _;
    use std::process::{Command, Stdio};

    const PROBLEM: &str = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../proof/alethe/tests/fixtures/cvc5-qf-uf/problem.smt2"
    ));
    const PROOF: &str = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../proof/alethe/tests/fixtures/cvc5-qf-uf/proof.alethe"
    ));

    #[test]
    fn replays_the_selected_cvc5_qf_uf_refutation() {
        let problem = parse_smtlib2(PROBLEM).expect("problem parses");
        let proof = parse_alethe(PROOF).expect("proof parses");
        let result = replay_qf_uf(&problem, &proof).expect("proof replays");
        let theorem = result
            .kernel()
            .thm()
            .get(result.theorem())
            .expect("refutation theorem");
        assert_eq!(theorem.lhs.rows().count(), 3);
        assert!(theorem.rhs.rows().next().is_none());
    }

    #[test]
    fn generates_and_replays_a_proof_with_cvc5() {
        generate_and_replay(PROBLEM);
    }

    #[test]
    fn replays_a_live_cvc5_qf_uf_rule_corpus() {
        const CASES: &[&str] = &[
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(assert (not (= a a)))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(declare-const b U)\n(declare-const c U)\n(assert (= a b))\n(assert (= b c))\n(assert (not (= a c)))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n(assert p)\n(assert (not q))\n(assert (=> p q))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n(assert (and p q))\n(assert (or (not p) (not q)))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert (xor p p))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(declare-const b U)\n(assert (distinct a b))\n(assert (= a b))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(declare-const b U)\n(declare-const p Bool)\n(assert (not (= (ite p a b) (ite p a b))))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert (let ((x p)) (and x (not x))))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(declare-const b U)\n(declare-const p Bool)\n(assert p)\n(assert (not (= (ite p a b) a)))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(declare-const b U)\n(declare-const p Bool)\n(assert (not p))\n(assert (not (= (ite p a b) b)))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n(assert (xor p q))\n(assert p)\n(assert q)\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(declare-const b U)\n(declare-const c U)\n(assert (distinct a b c))\n(assert (= a b))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n(assert (xor p q))\n(assert (not p))\n(assert (not q))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n(declare-const r Bool)\n(assert (xor p q r))\n(assert p)\n(assert q)\n(assert (not r))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n(assert (= p q))\n(assert p)\n(assert (not q))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n(declare-const r Bool)\n(assert (=> p q r))\n(assert p)\n(assert q)\n(assert (not r))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n(declare-const r Bool)\n(assert (or p q r))\n(assert (not p))\n(assert (not q))\n(assert (not r))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert (! p :named hyp))\n(assert (not p))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(declare-const b U)\n(declare-const c U)\n(assert (= a b c))\n(assert (not (= a c)))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(declare-const b U)\n(declare-const c U)\n(assert (distinct a b c))\n(assert (= b c))\n(check-sat)\n",
        ];
        for problem in CASES {
            generate_and_replay(problem);
        }
    }

    fn generate_and_replay(problem_source: &str) {
        let mut child = Command::new("cvc5")
            .args([
                "--produce-proofs",
                "--proof-format-mode=alethe",
                "--proof-granularity=dsl-rewrite",
                "--no-proof-allow-trust",
                "--dump-proofs",
                "--lang=smt2",
            ])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .expect("cvc5 is part of the Nix test environment");
        child
            .stdin
            .take()
            .expect("cvc5 stdin")
            .write_all(problem_source.as_bytes())
            .expect("write problem to cvc5");
        let output = child.wait_with_output().expect("wait for cvc5");
        assert!(output.status.success(), "cvc5 failed: {output:?}");
        let stdout = String::from_utf8(output.stdout).expect("cvc5 emits UTF-8");
        let problem = parse_smtlib2(problem_source).expect("problem parses");
        let proof = parse_cvc5_output(&stdout).expect("generated proof parses");
        replay_qf_uf(&problem, &proof).unwrap_or_else(|error| {
            panic!(
                "generated proof replays for:\n{problem_source}\nproof:\n{stdout}\nerror: {error}"
            )
        });
    }

    #[test]
    fn rejects_an_unasserted_assumption_and_a_forged_clause() {
        let problem = parse_smtlib2(PROBLEM).expect("problem parses");
        let unasserted = parse_alethe("(assume x true)").expect("proof parses");
        assert!(matches!(
            replay_qf_uf(&problem, &unasserted),
            Err(Error::UnassertedAssumption)
        ));

        let forged = PROOF.replace("(step t4 (cl)", "(step t4 (cl @p_4)");
        let forged = parse_alethe(&forged).expect("proof parses");
        assert!(matches!(
            replay_qf_uf(&problem, &forged),
            Err(Error::ClauseMismatch { .. } | Error::Kernel { .. })
        ));
    }

    /// Lowers `problem_source` and returns its kernel with the lowered
    /// assertion rows in source order.
    fn lowered_assertions(problem_source: &str) -> (Kernel, Vec<Ref>) {
        lowered_assertions_for(Logic::QfUf, problem_source)
    }

    fn lowered_assertions_for(logic: Logic, problem_source: &str) -> (Kernel, Vec<Ref>) {
        let problem = parse_smtlib2(problem_source).expect("problem parses");
        let mut replayer = Replayer::new(logic).expect("checked Boolean init compiles");
        replayer.ingest_problem(&problem).expect("problem lowers");
        let rows = replayer
            .assertion_terms
            .iter()
            .map(|term| term.reference)
            .collect();
        (replayer.kernel, rows)
    }

    #[test]
    fn lowers_implication_right_associatively() {
        let (mut kernel, rows) = lowered_assertions(
            "(set-logic QF_UF)\n\
             (declare-const p Bool)\n\
             (declare-const q Bool)\n\
             (declare-const r Bool)\n\
             (assert (=> p q r))\n\
             (assert (=> p (=> q r)))\n\
             (assert (=> (=> p q) r))\n\
             (check-sat)\n",
        );
        let [flat, nested, left] = rows.as_slice() else {
            panic!("three assertions lower to three rows");
        };
        assert!(
            join_same_syntax(&mut kernel, *flat, *left).is_err(),
            "(=> p q r) must not lower like (=> (=> p q) r)"
        );
        join_same_syntax(&mut kernel, *flat, *nested)
            .expect("(=> p q r) lowers like (=> p (=> q r))");
    }

    #[test]
    fn rejects_a_left_associated_implication_assumption() {
        // The problem is satisfiable (p false, r false); only the discarded
        // left-associative reading of `(=> p q r)` is unsatisfiable, so the
        // assumption stating that reading must not match any assertion.
        let problem = parse_smtlib2(
            "(set-logic QF_UF)\n\
             (declare-const p Bool)\n\
             (declare-const q Bool)\n\
             (declare-const r Bool)\n\
             (assert (=> p q r))\n\
             (assert (not p))\n\
             (assert (not r))\n\
             (check-sat)\n",
        )
        .expect("problem parses");
        let proof = parse_alethe("(assume a0 (=> (=> p q) r))").expect("proof parses");
        assert!(matches!(
            replay_qf_uf(&problem, &proof),
            Err(Error::UnassertedAssumption)
        ));
    }

    #[test]
    fn rejects_degenerate_boolean_arities() {
        for source in [
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert (=> p))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert (and p))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert (or p))\n(check-sat)\n",
        ] {
            let problem = parse_smtlib2(source).expect("problem parses");
            let proof = parse_alethe("(assume a0 p)").expect("proof parses");
            assert!(
                matches!(replay_qf_uf(&problem, &proof), Err(Error::Malformed { .. })),
                "unary Boolean operator accepted in: {source}"
            );
        }
    }

    #[test]
    fn let_binders_shadow_constants() {
        let (mut kernel, rows) = lowered_assertions(
            "(set-logic QF_UF)\n\
             (assert (let ((true false)) true))\n\
             (assert false)\n\
             (check-sat)\n",
        );
        let [shadowed, constant] = rows.as_slice() else {
            panic!("two assertions lower to two rows");
        };
        join_same_syntax(&mut kernel, *shadowed, *constant)
            .expect("a let binder shadows the constant true");
    }

    #[test]
    fn let_binders_shadow_named_terms() {
        let (mut kernel, rows) = lowered_assertions(
            "(set-logic QF_UF)\n\
             (declare-const p Bool)\n\
             (declare-const q Bool)\n\
             (assert (! p :named @x))\n\
             (assert (let ((@x q)) @x))\n\
             (assert q)\n\
             (check-sat)\n",
        );
        let [named, shadowed, binding] = rows.as_slice() else {
            panic!("three assertions lower to three rows");
        };
        assert!(
            join_same_syntax(&mut kernel, *shadowed, *named).is_err(),
            "a let binder must win over the @-named term"
        );
        join_same_syntax(&mut kernel, *shadowed, *binding)
            .expect("a let binder resolves to its bound value");
    }

    #[test]
    fn rejects_reserved_and_colliding_names() {
        let problem = parse_smtlib2(
            "(set-logic QF_UF)\n(declare-const @p_1 Bool)\n(assert @p_1)\n(check-sat)\n",
        )
        .expect("problem parses");
        let proof = parse_alethe("(assume a0 @p_1)").expect("proof parses");
        assert!(matches!(
            replay_qf_uf(&problem, &proof),
            Err(Error::Unsupported { .. })
        ));

        let problem = parse_smtlib2(
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert (! p :named p))\n(check-sat)\n",
        )
        .expect("problem parses");
        let proof = parse_alethe("(assume a0 p)").expect("proof parses");
        assert!(matches!(
            replay_qf_uf(&problem, &proof),
            Err(Error::Malformed { .. })
        ));
    }

    #[test]
    fn rejects_non_boolean_xor_operands() {
        let problem = parse_smtlib2(
            "(set-logic QF_UF)\n\
             (declare-sort U 0)\n\
             (declare-const a U)\n\
             (declare-const b U)\n\
             (assert (xor a b))\n\
             (check-sat)\n",
        )
        .expect("problem parses");
        let proof = parse_alethe("(assume a0 (xor a b))").expect("proof parses");
        assert!(matches!(
            replay_qf_uf(&problem, &proof),
            Err(Error::Malformed { .. })
        ));
    }

    #[test]
    fn rejects_a_hole_step_without_consulting_a_handler() {
        struct AcceptEverything(bool);

        impl RuleHandler for AcceptEverything {
            fn apply(&mut self, _request: RuleRequest<'_>) -> Result<Option<ThmId>, Error> {
                self.0 = true;
                Ok(None)
            }
        }

        let problem = parse_smtlib2(
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n",
        )
        .expect("problem parses");
        let proof = parse_alethe(
            "(assume a0 p)\n\
             (assume a1 (not p))\n\
             (step t0 (cl) :rule hole :premises (a0 a1))",
        )
        .expect("proof parses");
        let mut handler = AcceptEverything(false);
        assert!(matches!(
            replay_qf_uf_with_handler(&problem, &proof, &mut handler),
            Err(Error::Unsupported { .. })
        ));
        assert!(!handler.0, "a hole step must never reach a rule handler");
    }

    #[test]
    fn rejects_an_over_deep_term() {
        let depth = MAX_TERM_DEPTH + 8;
        let source = format!(
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert {}p{})\n(check-sat)\n",
            "(not ".repeat(depth),
            ")".repeat(depth)
        );
        let problem = parse_smtlib2(&source).expect("problem parses");
        let proof = parse_alethe("(assume a0 p)").expect("proof parses");
        assert!(matches!(
            replay_qf_uf(&problem, &proof),
            Err(Error::TermTooDeep {
                limit: MAX_TERM_DEPTH
            })
        ));
    }

    #[test]
    fn checks_a_user_defined_rule_handler() {
        struct ReflexivityHandler;

        impl RuleHandler for ReflexivityHandler {
            fn apply(&mut self, request: RuleRequest<'_>) -> Result<Option<ThmId>, Error> {
                if request.rule != "user-refute-refl" {
                    return Ok(None);
                }
                if !request.clause.is_empty() {
                    return Err(Error::Malformed {
                        message: "user-refute-refl expects the empty clause".to_owned(),
                    });
                }
                let [premise] = request.premises else {
                    return Err(Error::Malformed {
                        message: "user-refute-refl expects one premise".to_owned(),
                    });
                };
                let conclusions = conclusion_literals(request.kernel, *premise)?;
                let [source] = conclusions.as_slice() else {
                    return Err(Error::Malformed {
                        message: "user-refute-refl premise is not a unit".to_owned(),
                    });
                };
                let negation = reference(source.magnitude())?;
                let target = request
                    .kernel
                    .arena()
                    .children(negation)
                    .and_then(|mut children| children.next())
                    .ok_or_else(|| Error::Malformed {
                        message: "user-refute-refl premise is not a negation".to_owned(),
                    })?;
                let [_ty, left, right] = equality_children(request.kernel, target)?;
                join_same_syntax(request.kernel, left, right)?;
                let theorem = request.kernel.refl(request.bool_ty, left)?;
                join_same_syntax(request.kernel, theorem.equality, target)?;
                request
                    .kernel
                    .convert_conclusions(theorem.theorem, theorem.equality, target)?;
                let negative = request.kernel.expand_conclusion(*premise, *source, None)?;
                Ok(Some(request.kernel.resolve(
                    negative,
                    theorem.theorem,
                    Lit::positive(target.get()).negated(),
                )?))
            }
        }

        let problem = parse_smtlib2(
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(assert (not (= a a)))\n(check-sat)\n",
        )
        .expect("problem parses");
        let proof = parse_alethe(
            "(assume a0 (not (= a a)))\n\
             (step t0 (cl) :rule user-refute-refl :premises (a0))",
        )
        .expect("proof parses");
        replay_qf_uf_with_handler(&problem, &proof, &mut ReflexivityHandler)
            .expect("handler theorem is checked and replayed");
        assert!(matches!(
            replay_qf_uf(&problem, &proof),
            Err(Error::Unsupported { .. })
        ));
    }

    // --- QF_UFLIA frontend -------------------------------------------------

    const UFLIA_PROBLEM: &str = "(set-logic QF_UFLIA)\n\
         (declare-fun f (Int) Int)\n\
         (declare-const x Int)\n\
         (assert (= (f x) x))\n\
         (check-sat)\n";

    const UFLIA_FIXTURE_PROBLEM: &str = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../proof/alethe/tests/fixtures/cvc5-qf-uflia/problem.smt2"
    ));
    const UFLIA_FIXTURE_PROOF: &str = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../proof/alethe/tests/fixtures/cvc5-qf-uflia/proof.alethe"
    ));

    /// Lowers `sources` as Alethe proof terms against `problem_source`.
    fn lowered_proof_terms(problem_source: &str, sources: &[&str]) -> (Kernel, Vec<Ref>) {
        let mut replayer = uflia_replayer(problem_source);
        let rows = sources
            .iter()
            .map(|source| lower_proof_term(&mut replayer, source).expect("term lowers"))
            .collect();
        (replayer.kernel, rows)
    }

    fn uflia_replayer(problem_source: &str) -> Replayer {
        let problem = parse_smtlib2(problem_source).expect("problem parses");
        let mut replayer = Replayer::new(Logic::QfUflia).expect("checked Boolean init compiles");
        replayer.ingest_problem(&problem).expect("problem lowers");
        replayer.dialect = Dialect::Alethe;
        replayer
    }

    fn lower_proof_term(replayer: &mut Replayer, source: &str) -> Result<Ref, Error> {
        let proof = parse_alethe(&format!("(assume a0 {source})")).expect("term parses");
        let [AletheCommand::Assume { term, .. }] = proof.commands() else {
            panic!("one assume command");
        };
        replayer.term(term).map(|term| term.reference)
    }

    #[test]
    fn interns_one_numeral_spelling_as_one_row() {
        let (mut kernel, rows) =
            lowered_proof_terms(UFLIA_PROBLEM, &["5", "5", "7", "(f 5)", "(f 5)"]);
        let [first, second, seven, applied, applied_again] = rows.as_slice() else {
            panic!("five terms lower to five rows");
        };
        assert_eq!(first, second, "one spelling interns to one row");
        assert_ne!(first, seven, "distinct values are distinct rows");
        // Applications are appended rather than hash-consed, so two `(f 5)`
        // terms are two rows over one shared numeral row, and join.
        join_same_syntax(&mut kernel, *applied, *applied_again)
            .expect("two occurrences of (f 5) join");
        assert!(
            join_same_syntax(&mut kernel, *first, *seven).is_err(),
            "5 and 7 must never join"
        );
    }

    #[test]
    fn separates_spellings_the_producer_relates_by_a_rule() {
        // cvc5 states `(= (- 3) -3)` as an `evaluate` step, so identifying the
        // two spellings here would turn that step into reflexivity and assume
        // the arithmetic fact it is supposed to justify.
        let (mut kernel, rows) = lowered_proof_terms(UFLIA_PROBLEM, &["-3", "(- 3)", "5", "5/1"]);
        let [bare, applied, integer, rational] = rows.as_slice() else {
            panic!("four terms lower to four rows");
        };
        assert_ne!(bare, applied, "-3 and (- 3) are different rows");
        assert!(
            join_same_syntax(&mut kernel, *bare, *applied).is_err(),
            "-3 and (- 3) must never join"
        );
        assert_ne!(integer, rational, "5 and 5/1 are different rows");
        assert!(
            !kernel
                .equivalent(
                    kernel.classifier(*integer).expect("classifier"),
                    kernel.classifier(*rational).expect("classifier"),
                )
                .expect("classifiers compare"),
            "5 is Int-sorted and 5/1 is Real-sorted"
        );
    }

    #[test]
    fn reads_bare_negative_numerals_in_both_dialects() {
        let mut replayer = uflia_replayer(
            "(set-logic QF_UFLIA)\n(declare-const x Int)\n(assert (= x -3))\n(check-sat)\n",
        );
        let from_input = replayer.numeric().expect("numeric vocabulary").int_numerals["-3"];
        let from_proof = lower_proof_term(&mut replayer, "-3").expect("term lowers");
        assert_eq!(
            from_input, from_proof,
            "one spelling interns to one row in both readers"
        );
    }

    #[test]
    fn rejects_rational_literals_in_smtlib_input() {
        let problem = parse_smtlib2(
            "(set-logic QF_UFLIA)\n(declare-const x Int)\n(assert (= x 1/1))\n(check-sat)\n",
        )
        .expect("problem parses");
        let mut replayer = Replayer::new(Logic::QfUflia).expect("init compiles");
        assert!(matches!(
            replayer.ingest_problem(&problem),
            Err(Error::Malformed { .. })
        ));
    }

    #[test]
    fn rejects_the_real_sort_in_input() {
        let problem = parse_smtlib2(
            "(set-logic QF_UFLIA)\n(declare-const r Real)\n(assert (= r r))\n(check-sat)\n",
        )
        .expect("problem parses");
        let mut replayer = Replayer::new(Logic::QfUflia).expect("init compiles");
        assert!(matches!(
            replayer.ingest_problem(&problem),
            Err(Error::Unsupported { .. })
        ));
    }

    #[test]
    fn rejects_non_canonical_numeral_spellings() {
        let mut replayer = uflia_replayer(UFLIA_PROBLEM);
        for spelling in ["007", "-0", "1/0", "1.5", "0/0", "-0/1", "1/01"] {
            assert!(
                matches!(
                    lower_proof_term(&mut replayer, spelling),
                    Err(Error::Malformed { .. })
                ),
                "numeral {spelling:?} was not rejected"
            );
        }
    }

    #[test]
    fn rejects_declarations_that_collide_with_the_reader() {
        for source in [
            "(set-logic QF_UFLIA)\n(declare-const -3 Int)\n(check-sat)\n",
            "(set-logic QF_UFLIA)\n(declare-sort Int 0)\n(check-sat)\n",
            "(set-logic QF_UFLIA)\n(declare-sort Real 0)\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const Bool U)\n(check-sat)\n",
        ] {
            let problem = parse_smtlib2(source).expect("problem parses");
            let logic = if source.contains("QF_UFLIA") {
                Logic::QfUflia
            } else {
                Logic::QfUf
            };
            let mut replayer = Replayer::new(logic).expect("init compiles");
            assert!(
                matches!(
                    replayer.ingest_problem(&problem),
                    Err(Error::Malformed { .. })
                ),
                "declaration accepted in: {source}"
            );
        }
    }

    #[test]
    fn rejects_a_let_binder_spelled_as_a_numeral() {
        let mut replayer = uflia_replayer(UFLIA_PROBLEM);
        assert!(matches!(
            lower_proof_term(&mut replayer, "(let ((-3 x)) -3)"),
            Err(Error::Malformed { .. })
        ));
    }

    #[test]
    fn folds_arithmetic_operators_the_way_cvc5_states_them() {
        let (mut kernel, rows) = lowered_proof_terms(
            "(set-logic QF_UFLIA)\n\
             (declare-const x Int)\n\
             (declare-const y Int)\n\
             (declare-const z Int)\n\
             (assert (= x x))\n\
             (check-sat)\n",
            &[
                "(+ x y z)",
                "(+ (+ x y) z)",
                "(+ x (+ y z))",
                "(- x y)",
                "(< x y)",
                "(> x y)",
            ],
        );
        let [flat, left, right, difference, less, greater] = rows.as_slice() else {
            panic!("six terms lower to six rows");
        };
        join_same_syntax(&mut kernel, *flat, *left)
            .expect("SMT-LIB Ints declares + left-associative");
        assert!(
            join_same_syntax(&mut kernel, *flat, *right).is_err(),
            "(+ x y z) must not lower like (+ x (+ y z))"
        );
        assert!(
            join_same_syntax(&mut kernel, *difference, *less).is_err(),
            "different operators are different heads"
        );
        assert!(
            join_same_syntax(&mut kernel, *less, *greater).is_err(),
            "(< x y) must not be normalized into (> y x)"
        );
    }

    #[test]
    fn rejects_arithmetic_shapes_this_reader_does_not_read() {
        let mut replayer = uflia_replayer(
            "(set-logic QF_UFLIA)\n\
             (declare-const x Int)\n\
             (declare-const y Int)\n\
             (declare-const p Bool)\n\
             (assert (= x x))\n\
             (check-sat)\n",
        );
        // The chainable comparison form is refused rather than guessed.
        assert!(matches!(
            lower_proof_term(&mut replayer, "(< x y x)"),
            Err(Error::Unsupported { .. })
        ));
        assert!(matches!(
            lower_proof_term(&mut replayer, "(+ x p)"),
            Err(Error::Malformed { .. })
        ));
        assert!(matches!(
            lower_proof_term(&mut replayer, "(+ x)"),
            Err(Error::Malformed { .. })
        ));
        assert!(matches!(
            lower_proof_term(&mut replayer, "(to_real p)"),
            Err(Error::Kernel { .. })
        ));
        // to_real lifts Int into Real, and its result is not an Int again.
        assert!(matches!(
            lower_proof_term(&mut replayer, "(+ x (to_real x))"),
            Err(Error::Malformed { .. })
        ));
        lower_proof_term(&mut replayer, "(* -1/1 (to_real (- x 1)))")
            .expect("a Real-sorted product over a coercion lowers");
    }

    #[test]
    fn lowers_qf_uflia_without_import_proxy_rows() {
        // The compact literal rows of issue 1210 have no checked lowering, so
        // this frontend emits none and adds no dependency on them.
        let (kernel, _) = lowered_assertions_for(
            Logic::QfUflia,
            "(set-logic QF_UFLIA)\n\
             (declare-fun f (Int) Int)\n\
             (declare-const x Int)\n\
             (assert (= (f (+ x -3)) (* 2 x)))\n\
             (assert (< x 5))\n\
             (check-sat)\n",
        );
        for index in 1..=kernel.arena().len() {
            let Ok(value) = i32::try_from(index) else {
                continue;
            };
            let Some(reference) = Ref::new(value) else {
                continue;
            };
            let Some(tag) = kernel.arena().tag(reference) else {
                continue;
            };
            assert!(
                !matches!(
                    tag,
                    Tag::Kind(KindTag::Ref) | Tag::Ty(TyTag::Ref) | Tag::Tm(TmTag::Ref)
                ),
                "row {index} is an unchecked import proxy: {tag:?}"
            );
        }
        assert!(
            kernel.arena().ambient_predicates().is_empty(),
            "lowering must assume nothing about imported rows"
        );
    }

    #[test]
    fn partitions_the_logic_entry_points() {
        let uf = parse_smtlib2(PROBLEM).expect("problem parses");
        let uflia = parse_smtlib2(UFLIA_FIXTURE_PROBLEM).expect("problem parses");
        let proof = parse_alethe(PROOF).expect("proof parses");
        assert!(matches!(
            replay_qf_uf(&uflia, &proof),
            Err(Error::Unsupported { .. })
        ));
        assert!(matches!(
            lower_qf_uflia(&uf, &proof),
            Err(Error::Unsupported { .. })
        ));
        let unknown = parse_smtlib2("(set-logic QF_LIA)\n(check-sat)\n").expect("problem parses");
        assert!(matches!(
            replay_qf_uf(&unknown, &proof),
            Err(Error::Unsupported { .. })
        ));
        assert_eq!(
            replay_qf_uf(&uf, &proof)
                .expect("QF_UF still replays")
                .logic(),
            Logic::QfUf
        );
    }

    #[test]
    fn lowers_the_qf_uflia_fixture_and_stops_at_an_unwritten_rule() {
        let problem = parse_smtlib2(UFLIA_FIXTURE_PROBLEM).expect("problem parses");
        let proof = parse_alethe(UFLIA_FIXTURE_PROOF).expect("proof parses");
        // Every term in this proof lowers; the first thing this build cannot
        // do is the Boolean rewrite `bool-double-not-elim`, which is not
        // written yet rather than arithmetic. Both are hard rejections.
        assert!(matches!(
            lower_qf_uflia(&problem, &proof),
            Err(Error::Unsupported { .. })
        ));
    }

    #[test]
    fn rejects_arithmetic_rules_with_a_named_error() {
        let problem = parse_smtlib2(
            "(set-logic QF_UFLIA)\n\
             (declare-const x Int)\n\
             (assert (= x 1))\n\
             (assert (not (= x 1)))\n\
             (check-sat)\n",
        )
        .expect("problem parses");
        for (source, expected) in [
            ("(step t0 (cl (= (* 1 x) x)) :rule poly_simp)", "poly_simp"),
            (
                "(step t0 (cl (< x 1)) :rule la_generic :args (1/1 1/1))",
                "la_generic",
            ),
            (
                "(step t0 (cl (= (<= x 1) (>= 1 x))) :rule rare_rewrite :args (\"arith-elim-leq\" x 1))",
                "arith-elim-leq",
            ),
            ("(step t0 (cl (= (+ 5 -6) -1)) :rule evaluate)", "evaluate"),
            (
                "(step t0 (cl (= (= 5 6) false)) :rule evaluate)",
                "evaluate",
            ),
        ] {
            let proof = parse_alethe(source).expect("proof parses");
            let lowering = lower_qf_uflia(&problem, &proof)
                .unwrap_or_else(|error| panic!("{source} raised {error} rather than a gap"));
            let gap = lowering.arithmetic_gap();
            assert_eq!((gap.step(), gap.rule()), ("t0", expected));
        }
        // The same rules are refused on the QF_UF path with the same error.
        let problem = parse_smtlib2(PROBLEM).expect("problem parses");
        let proof = parse_alethe("(step t0 (cl) :rule la_generic)").expect("proof parses");
        assert!(matches!(
            replay_qf_uf(&problem, &proof),
            Err(Error::ArithmeticTheoryMissing { .. })
        ));
    }

    #[test]
    fn keeps_boolean_evaluate_checkable() {
        let problem = parse_smtlib2(
            "(set-logic QF_UFLIA)\n\
             (declare-const x Int)\n\
             (assert (= x 1))\n\
             (assert (not (= x 1)))\n\
             (check-sat)\n",
        )
        .expect("problem parses");
        let proof = parse_alethe("(step t0 (cl (= (not true) false)) :rule evaluate)")
            .expect("proof parses");
        // The step checks; the proof simply never reaches an empty clause.
        assert!(matches!(
            lower_qf_uflia(&problem, &proof),
            Err(Error::NoRefutation)
        ));
    }

    /// One curated cvc5 `QF_UFLIA` problem and the first rule that stops it.
    ///
    /// The gap is machine-checked rather than asserted in prose: it is exactly
    /// how far this build reaches, and it turns into a positive corpus one
    /// rule at a time.
    #[test]
    fn lowers_live_cvc5_qf_uflia_proofs_to_a_named_arithmetic_gap() {
        const GAPS: &[(&str, &str, &str, &str)] = &[
            (
                "(set-logic QF_UFLIA)\n(declare-const x Int)\n(declare-const y Int)\n(assert (= (+ x y) 10))\n(assert (= x 3))\n(assert (not (= y 7)))\n(check-sat)\n",
                "t3",
                "poly_simp",
                "integer or rational",
            ),
            (
                "(set-logic QF_UFLIA)\n(declare-const x Int)\n(assert (< x 5))\n(assert (> x 5))\n(check-sat)\n",
                "t1",
                "arith-elim-lt",
                "integer or rational",
            ),
            (
                "(set-logic QF_UFLIA)\n(declare-const x Int)\n(assert (= x (- 3)))\n(assert (> x (- 1)))\n(check-sat)\n",
                "t2",
                "evaluate",
                "integer",
            ),
            (
                "(set-logic QF_UFLIA)\n(declare-const x Int)\n(assert (= (* 3 x) 12))\n(assert (not (= x 4)))\n(check-sat)\n",
                "t1",
                "poly_simp",
                "integer or rational",
            ),
            (
                "(set-logic QF_UFLIA)\n(declare-fun f (Int) Int)\n(declare-const x Int)\n(assert (not (= (f (+ x 1)) (f (+ 1 x)))))\n(check-sat)\n",
                "t1",
                "poly_simp",
                "integer or rational",
            ),
            (
                "(set-logic QF_UFLIA)\n(declare-const x Int)\n(assert (= (* 2 x) 1))\n(check-sat)\n",
                "t1",
                "poly_simp",
                "integer or rational",
            ),
            (
                "(set-logic QF_UFLIA)\n(declare-fun g (Int Int) Int)\n(declare-const x Int)\n(assert (= (g x 0) 5))\n(assert (= (g x (- 1 1)) 6))\n(check-sat)\n",
                "t3",
                "evaluate",
                "integer",
            ),
            (
                "(set-logic QF_UFLIA)\n(declare-const x Int)\n(assert (= (* (- 2) x) 6))\n(assert (not (= x (- 3))))\n(check-sat)\n",
                "t1",
                "evaluate",
                "integer",
            ),
            (
                "(set-logic QF_UFLIA)\n(declare-const x Int)\n(assert (> (* 3 x) 1))\n(assert (< (* 3 x) 3))\n(check-sat)\n",
                "t1",
                "arith-elim-gt",
                "integer or rational",
            ),
        ];
        for (source, step, rule, domain) in GAPS {
            let stdout = solve_with_cvc5(source);
            let problem = parse_smtlib2(source).expect("problem parses");
            let proof = parse_cvc5_output(&stdout).expect("generated proof parses");
            let lowering = lower_qf_uflia(&problem, &proof)
                .unwrap_or_else(|error| panic!("no gap for:\n{source}\nerror: {error}"));
            let gap = lowering.arithmetic_gap();
            assert_eq!(
                (gap.step(), gap.rule(), gap.domain()),
                (*step, *rule, *domain)
            );
            assert_eq!(lowering.logic(), Logic::QfUflia);
            assert!(!lowering.assertions().is_empty());
            assert!(lowering.steps() > 0);
        }
    }

    #[test]
    fn refuses_to_certify_a_qf_uflia_proof_that_needed_no_arithmetic() {
        // Whether a QF_UFLIA problem's unsatisfiability is purely UF is not
        // visible in the input; it depends on cvc5's normalization. So a proof
        // that replays without ever needing arithmetic is refused rather than
        // returned, and there is no shape in which it could be returned.
        let source = "(set-logic QF_UFLIA)\n\
             (declare-fun f (Int) Int)\n\
             (declare-const x Int)\n\
             (declare-const y Int)\n\
             (assert (= x y))\n\
             (assert (not (= (f x) (f y))))\n\
             (check-sat)\n";
        let stdout = solve_with_cvc5(source);
        let problem = parse_smtlib2(source).expect("problem parses");
        let proof = parse_cvc5_output(&stdout).expect("generated proof parses");
        assert!(matches!(
            lower_qf_uflia(&problem, &proof),
            Err(Error::NoArithmeticGap)
        ));
    }

    fn solve_with_cvc5(problem_source: &str) -> String {
        let mut child = Command::new("cvc5")
            .args([
                "--produce-proofs",
                "--proof-format-mode=alethe",
                "--proof-granularity=dsl-rewrite",
                "--no-proof-allow-trust",
                "--dump-proofs",
                "--lang=smt2",
            ])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .expect("cvc5 is part of the Nix test environment");
        child
            .stdin
            .take()
            .expect("cvc5 stdin")
            .write_all(problem_source.as_bytes())
            .expect("write problem to cvc5");
        let output = child.wait_with_output().expect("wait for cvc5");
        assert!(output.status.success(), "cvc5 failed: {output:?}");
        String::from_utf8(output.stdout).expect("cvc5 emits UTF-8")
    }

    // --- subproof frames ---------------------------------------------------

    const FRAME_PROBLEM: &str = "(set-logic QF_UF)\n\
         (declare-sort U 0)\n\
         (declare-const a U)\n\
         (declare-const b U)\n\
         (assert (= a b))\n\
         (assert (not (= a b)))\n\
         (check-sat)\n";

    /// Two outer assumptions, a frame assuming one of them, and a frame-local
    /// refutation of it. Repeated terms are shared through `:named` aliases,
    /// as cvc5 shares them, because the replayer appends rather than
    /// hash-conses a term row.
    const FRAME_PREFIX: &str = "(assume a0 (! (= a b) :named @p_1))\n\
         (assume a1 (! (not @p_1) :named @p_2))\n\
         (anchor :step t1)\n\
         (assume t1.a0 @p_1)\n\
         (step t1.t0 (cl) :rule resolution :premises (t1.a0 a1))\n";

    fn replay_frame(proof_source: &str) -> Result<Refutation, Error> {
        let problem = parse_smtlib2(FRAME_PROBLEM).expect("problem parses");
        let proof = parse_alethe(proof_source).expect("proof parses");
        replay_qf_uf(&problem, &proof)
    }

    #[test]
    fn discharges_a_subproof_frame_assumption() {
        let refutation = replay_frame(&format!(
            "{FRAME_PREFIX}\
             (step t1 (cl @p_2) :rule subproof :discharge (t1.a0))\n\
             (step t2 (cl) :rule resolution :premises (t1 a0))"
        ))
        .expect("the frame discharges and the proof replays");
        let theorem = refutation
            .kernel()
            .thm()
            .get(refutation.theorem())
            .expect("refutation theorem");
        assert_eq!(theorem.lhs.rows().count(), 2);
        assert!(theorem.rhs.rows().next().is_none());
    }

    #[test]
    fn discharges_a_frame_assumption_the_frame_never_used() {
        // The frame assumes `(not (not (= a b)))`, which the problem never
        // asserts, so a frame assumption must not be checked against the
        // assertion set. Its body never uses the assumption, so the discharge
        // has to left-weaken first. Its last step is another step's theorem
        // unchanged, so the discharge has to copy before mutating: without the
        // copy this proof would corrupt `a0` and the final goal check fails.
        let refutation = replay_frame(
            "(assume a0 (! (= a b) :named @p_1))\n\
             (assume a1 (! (not @p_1) :named @p_2))\n\
             (anchor :step t1)\n\
             (assume t1.a0 (! (not @p_2) :named @p_3))\n\
             (step t1.t0 (cl @p_1) :rule resolution :premises (a0))\n\
             (step t1 (cl (not @p_3) @p_1) :rule subproof :discharge (t1.a0))\n\
             (step t2 (cl) :rule resolution :premises (a0 a1))",
        )
        .expect("an unused frame assumption still discharges");
        let theorem = refutation
            .kernel()
            .thm()
            .get(refutation.theorem())
            .expect("refutation theorem");
        assert_eq!(theorem.lhs.rows().count(), 2);
    }

    #[test]
    fn discharges_a_frame_assumption_out_of_the_antecedent() {
        // The invariant a frame rests on: an assumption enters only through
        // `Kernel::identity`, so it sits in the antecedent, and `subproof` is
        // the only thing that takes it back out. Reading the closed frame's
        // theorem states that directly, because a leftover hypothesis is
        // otherwise invisible until the final goal check.
        let problem = parse_smtlib2(
            "(set-logic QF_UF)\n\
             (declare-const p Bool)\n\
             (declare-const q Bool)\n\
             (assert p)\n\
             (assert (not p))\n\
             (assert q)\n\
             (check-sat)\n",
        )
        .expect("problem parses");
        let proof = parse_alethe(
            "(assume a0 (! p :named @p_1))\n\
             (assume a1 (! (not @p_1) :named @p_2))\n\
             (assume a2 (! q :named @p_3))\n\
             (anchor :step t1)\n\
             (assume t1.a0 (! (not @p_3) :named @p_4))\n\
             (step t1.t0 (cl) :rule resolution :premises (t1.a0 a2))\n\
             (step t1 (cl (not @p_4)) :rule subproof :discharge (t1.a0))\n\
             (step t2 (cl) :rule resolution :premises (a0 a1))",
        )
        .expect("proof parses");
        let mut replayer = Replayer::new(Logic::QfUf).expect("checked Boolean init compiles");
        replayer.ingest_problem(&problem).expect("problem lowers");
        replayer
            .run_proof(&proof, &mut RejectUnknownRules)
            .expect("the proof replays");
        let frame_local = Lit::positive(replayer.named["@p_4"].reference.get());
        let assumption = Lit::positive(replayer.named["@p_3"].reference.get());
        let closed = replayer.steps["t1"];
        assert!(
            !has_unit_premise(&replayer.kernel, closed, frame_local)
                .expect("the closed frame has a theorem"),
            "the frame-local assumption must not survive in the antecedent"
        );
        assert!(
            has_unit_premise(&replayer.kernel, closed, assumption).expect("theorem"),
            "an outer premise the frame used stays in the antecedent"
        );
    }

    #[test]
    fn rejects_a_frame_step_cited_outside_its_frame() {
        // The attack: assume the negation of an assertion inside a frame,
        // refute it there, then cite the inner empty clause from outside. The
        // inner index left scope when the frame closed.
        let error = replay_frame(&format!(
            "{FRAME_PREFIX}\
             (step t1 (cl @p_2) :rule subproof :discharge (t1.a0))\n\
             (step t2 (cl) :rule resolution :premises (t1.t0))"
        ))
        .expect_err("an inner index is out of scope");
        let Error::OutOfScopePremise { step, premise } = &error else {
            panic!("expected an out-of-scope premise, got {error}");
        };
        assert_eq!((step.as_str(), premise.as_str()), ("t2", "t1.t0"));
    }

    #[test]
    fn rejects_an_inner_empty_clause_as_the_refutation() {
        // `t1.t0` derives the empty clause under a frame-local assumption, so
        // it is not the proof's refutation.
        assert!(matches!(
            replay_frame(&format!(
                "{FRAME_PREFIX}(step t1 (cl @p_2) :rule subproof :discharge (t1.a0))"
            )),
            Err(Error::NoRefutation)
        ));
    }

    #[test]
    fn rejects_malformed_subproof_frames() {
        for proof in [
            // The discharge list names nothing.
            format!("{FRAME_PREFIX}(step t1 (cl @p_2) :rule subproof :discharge ())"),
            // The discharge list names an index that is not an assumption.
            format!("{FRAME_PREFIX}(step t1 (cl @p_2) :rule subproof :discharge (t1.t0))"),
            // The clause literal is not the negated assumption.
            format!("{FRAME_PREFIX}(step t1 (cl @p_1) :rule subproof :discharge (t1.a0))"),
            // The clause is shorter than the discharge list.
            format!("{FRAME_PREFIX}(step t1 (cl) :rule subproof :discharge (t1.a0))"),
            // Another rule may not conclude a frame.
            format!("{FRAME_PREFIX}(step t1 (cl @p_2) :rule resolution :premises (t1.t0))"),
            // `subproof` takes no premises.
            format!(
                "{FRAME_PREFIX}(step t1 (cl @p_2) :rule subproof :premises (t1.t0) :discharge (t1.a0))"
            ),
            // The anchor is never closed.
            FRAME_PREFIX.to_owned(),
            // An assume may not follow the frame's first step.
            format!("{FRAME_PREFIX}(assume t1.a1 @p_1)"),
        ] {
            assert!(
                matches!(replay_frame(&proof), Err(Error::Frame { .. })),
                "frame accepted in:\n{proof}"
            );
        }
    }

    #[test]
    fn rejects_an_anchor_with_context_arguments() {
        assert!(matches!(
            replay_frame(
                "(assume a0 (! (= a b) :named @p_1))\n\
                 (assume a1 (! (not @p_1) :named @p_2))\n\
                 (anchor :step t1 :args ((:= x a)))"
            ),
            Err(Error::Unsupported { .. })
        ));
    }

    #[test]
    fn rejects_a_frame_index_reused_after_its_frame_closed() {
        assert!(matches!(
            replay_frame(&format!(
                "{FRAME_PREFIX}\
                 (step t1 (cl @p_2) :rule subproof :discharge (t1.a0))\n\
                 (step t1.t0 (cl (= a a)) :rule refl)"
            )),
            Err(Error::Malformed { .. })
        ));
    }

    // --- fail-closed guarantees --------------------------------------------

    /// Refutes `p` and `(not p)` honestly, then adds one hypothesis the
    /// problem never asserted.
    struct SmuggleHandler;

    impl RuleHandler for SmuggleHandler {
        fn apply(&mut self, request: RuleRequest<'_>) -> Result<Option<ThmId>, Error> {
            if request.rule != "smuggle" {
                return Ok(None);
            }
            let [positive, negative] = request.premises else {
                return Err(Error::Malformed {
                    message: "smuggle expects two premises".to_owned(),
                });
            };
            let left = conclusion_literals(request.kernel, *positive)?;
            let right = conclusion_literals(request.kernel, *negative)?;
            let ([pivot], [negation]) = (left.as_slice(), right.as_slice()) else {
                return Err(Error::Malformed {
                    message: "smuggle expects unit premises".to_owned(),
                });
            };
            let expanded = request
                .kernel
                .expand_conclusion(*negative, *negation, None)?;
            let theorem = request.kernel.resolve(*positive, expanded, *pivot)?;
            let extra = request.kernel.tm_fv(u64::MAX, request.bool_ty)?;
            request
                .kernel
                .weaken(theorem, &[Lit::positive(extra.get())], &[])?;
            Ok(Some(theorem))
        }
    }

    #[test]
    fn rejects_a_hypothesis_the_problem_never_asserted() {
        let problem = parse_smtlib2(
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n",
        )
        .expect("problem parses");
        let proof = parse_alethe(
            "(assume a0 p)\n\
             (assume a1 (not p))\n\
             (step t0 (cl) :rule smuggle :premises (a0 a1))",
        )
        .expect("proof parses");
        let error = replay_qf_uf_with_handler(&problem, &proof, &mut SmuggleHandler)
            .expect_err("an extra hypothesis is not the assertion set");
        assert!(
            error.to_string().contains("assertion set"),
            "unexpected error: {error}"
        );
    }

    struct NoResolver;

    impl covalence_logic_hol::Resolver for NoResolver {
        type Error = std::convert::Infallible;

        fn resolve(
            &mut self,
            _link: &covalence_logic_hol::Link,
        ) -> Result<covalence_logic_hol::Table, Self::Error> {
            unreachable!("a literal import resolves without I/O")
        }
    }

    /// Refutes honestly, then assumes an unchecked foreign typing predicate.
    struct AmbientHandler;

    impl RuleHandler for AmbientHandler {
        fn apply(&mut self, request: RuleRequest<'_>) -> Result<Option<ThmId>, Error> {
            if request.rule != "smuggle" {
                return Ok(None);
            }
            let [positive, negative] = request.premises else {
                return Err(Error::Malformed {
                    message: "smuggle expects two premises".to_owned(),
                });
            };
            let left = conclusion_literals(request.kernel, *positive)?;
            let right = conclusion_literals(request.kernel, *negative)?;
            let ([pivot], [negation]) = (left.as_slice(), right.as_slice()) else {
                return Err(Error::Malformed {
                    message: "smuggle expects unit premises".to_owned(),
                });
            };
            let expanded = request
                .kernel
                .expand_conclusion(*negative, *negation, None)?;
            let theorem = request.kernel.resolve(*positive, expanded, *pivot)?;

            let mut foreign = Kernel::new();
            let star = foreign.star()?;
            let foreign_bool = foreign.bool_ty(star)?;
            let foreign_variable = foreign.tm_fv(0, foreign_bool)?;
            let source = request.kernel.import_literal(foreign.into_arena())?;
            request
                .kernel
                .tm_ref(&mut NoResolver, source, foreign_variable, request.bool_ty)?;
            Ok(Some(theorem))
        }
    }

    #[test]
    fn rejects_an_ambient_predicate_added_during_replay() {
        let problem = parse_smtlib2(
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n",
        )
        .expect("problem parses");
        let proof = parse_alethe(
            "(assume a0 p)\n\
             (assume a1 (not p))\n\
             (step t0 (cl) :rule smuggle :premises (a0 a1))",
        )
        .expect("proof parses");
        let error = replay_qf_uf_with_handler(&problem, &proof, &mut AmbientHandler)
            .expect_err("an unchecked ambient predicate is refused");
        assert!(
            error.to_string().contains("ambient predicate"),
            "unexpected error: {error}"
        );
    }

    /// Recognizes one unknown RARE rewrite by reading its premise.
    struct RarePremiseHandler {
        premises: usize,
        forge: bool,
    }

    impl RuleHandler for RarePremiseHandler {
        fn apply(&mut self, request: RuleRequest<'_>) -> Result<Option<ThmId>, Error> {
            if request.rule != "rare_rewrite" {
                return Ok(None);
            }
            if args_name(request.args) != Some("made-up-rewrite") {
                return Ok(None);
            }
            self.premises = request.premises.len();
            let [premise] = request.premises else {
                return Err(Error::Malformed {
                    message: "made-up-rewrite expects one premise".to_owned(),
                });
            };
            if self.forge {
                // Returning a theorem for a different clause must still fail.
                return Ok(Some(*premise));
            }
            let target = positive_unit(request.clause, "made-up-rewrite")?;
            let [_domain, left, right] = equality_children(request.kernel, target)?;
            join_same_syntax(request.kernel, left, right)?;
            let proved = request.kernel.refl(request.bool_ty, left)?;
            join_same_syntax(request.kernel, proved.equality, target)?;
            request
                .kernel
                .convert_conclusions(proved.theorem, proved.equality, target)?;
            Ok(Some(proved.theorem))
        }
    }

    fn args_name(args: &[Expr]) -> Option<&str> {
        args.first().and_then(string_value)
    }

    #[test]
    fn passes_rare_rewrite_premises_through_to_a_handler() {
        let problem = parse_smtlib2(
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n",
        )
        .expect("problem parses");
        let proof = parse_alethe(
            "(assume a0 p)\n\
             (assume a1 (not p))\n\
             (step t0 (cl (= p p)) :rule rare_rewrite :premises (a0) :args (\"made-up-rewrite\" p))\n\
             (step t1 (cl) :rule resolution :premises (a0 a1))",
        )
        .expect("proof parses");
        let mut handler = RarePremiseHandler {
            premises: 0,
            forge: false,
        };
        replay_qf_uf_with_handler(&problem, &proof, &mut handler)
            .expect("the handled rewrite and the refutation replay");
        assert_eq!(handler.premises, 1, "the premise reached the handler");

        // The exact-clause postcheck still runs on the handler's theorem.
        let mut handler = RarePremiseHandler {
            premises: 0,
            forge: true,
        };
        assert!(matches!(
            replay_qf_uf_with_handler(&problem, &proof, &mut handler),
            Err(Error::ClauseMismatch { .. } | Error::Kernel { .. })
        ));
    }

    #[test]
    fn rejects_premises_on_a_premise_free_rare_rewrite() {
        let problem = parse_smtlib2(
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n",
        )
        .expect("problem parses");
        let proof = parse_alethe(
            "(assume a0 p)\n\
             (step t0 (cl (= (= p p) true)) :rule rare_rewrite :premises (a0) :args (\"eq-refl\" p))",
        )
        .expect("proof parses");
        assert!(matches!(
            replay_qf_uf(&problem, &proof),
            Err(Error::Malformed { .. })
        ));
    }
}
