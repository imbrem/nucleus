//! A proof-producing normalizer for natural-number arithmetic.
//!
//! [`NaturalNormalizer::normalize`] takes an [`Expr`] and returns the theorem
//! `⊢ expr = normal form`. The normal form is a sum of monomials:
//!
//! - a monomial is a coefficient times a sorted product of atoms;
//! - the monomials are sorted too, with the constant last.
//!
//! Two expressions are equal in every commutative semiring exactly when their
//! normal forms match. [`NaturalNormalizer::prove_equal`] uses that.
//!
//! The normalizer is untrusted: it picks the rewrites, the kernel checks them.
//! A bug here produces a failure, never a false theorem.
//!
//! Two limits:
//!
//! - Literals are `succ` towers, capped at [`MAX_LITERAL`]. `nat.zero` and
//!   `nat.succ` are the only numerals the init slice provides.
//! - `a - b` normalizes only when `b` is a literal no larger than the constant
//!   term of `a`. Any other subtraction stays an atom.

use std::cell::RefCell;
use std::collections::HashMap;

use covalence_logic_hol::{Kernel, Ref, ThmId};

use crate::{
    Expr, NaturalError, NaturalRing, NaturalSubtraction, Naturals, ProvedEquality,
    natural_arithmetic::{exact_equality, sole_conclusion},
    natural_calc::{Calc, on_left, on_right, under},
    natural_expr::Node,
    syntax::join_same_syntax,
};

/// Largest literal [`NumeralEngine::Unary`] will build.
pub const MAX_LITERAL: u64 = 4096;

/// How a literal is lowered to a `nat` term.
///
/// Both engines prove the same statements; they differ in how much work the
/// kernel does. Pick one with [`NaturalNormalizer::with_engine`].
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum NumeralEngine {
    /// `succ` applied to zero, once per unit.
    ///
    /// A literal reads back as itself, which keeps small normal forms easy to
    /// look at, but building `n` costs `n` rows and adding two literals costs
    /// `n` checked steps. Capped at [`MAX_LITERAL`].
    #[default]
    Unary,
    /// Doubling and `succ`, one level per bit.
    ///
    /// A literal is `O(log n)` terms, addition is `O(log n)` checked steps and
    /// multiplication `O(log n)` of those. Doubling is written `a + a`, so this
    /// needs no definition the semiring does not already have. Literals are
    /// bounded only by `u64`.
    Binary,
}

impl NumeralEngine {
    /// The largest literal this engine will build.
    #[must_use]
    pub const fn max_literal(self) -> u64 {
        match self {
            Self::Unary => MAX_LITERAL,
            Self::Binary => u64::MAX,
        }
    }

    /// The name used in benchmark output.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Unary => "unary",
            Self::Binary => "binary",
        }
    }
}

/// Normalizes arithmetic expressions against one proved law package.
///
/// A normalizer holds kernel-local theorem handles, so use one with the kernel
/// its law packages were proved in.
pub struct NaturalNormalizer<'a> {
    calc: Calc<'a>,
    ring: NaturalRing,
    subtraction: Option<NaturalSubtraction>,
    engine: NumeralEngine,
    /// Applications built during the call in progress, so equal terms share one
    /// row. Cleared at each entry point: a row belongs to one kernel, and the
    /// next call may be given a different one.
    ///
    /// The arena appends rather than shares, and the normalizer rebuilds the
    /// same subterms constantly. Caching keeps the arena small and, more
    /// importantly, keeps an atom's identity stable so two occurrences of the
    /// same subexpression collect into one monomial.
    applications: RefCell<HashMap<(Ref, Ref), Ref>>,
}

/// A commutative monoid whose laws the sorting machinery uses.
#[derive(Clone, Copy)]
struct Monoid {
    operation: Ref,
    unit: Ref,
    /// `∀a b c. (a ∘ b) ∘ c = a ∘ (b ∘ c)`.
    associative: ThmId,
    /// `∀a b. a ∘ b = b ∘ a`.
    commutative: ThmId,
    /// `∀a b c. (a ∘ b) ∘ c = (a ∘ c) ∘ b`.
    exchange: ThmId,
    /// `∀a. e ∘ a = a`.
    left_unit: ThmId,
    /// `∀a. a ∘ e = a`.
    right_unit: ThmId,
}

/// One summand: a coefficient times a sorted product of atoms.
///
/// The coefficient is always at least one, so a monomial never renders as
/// zero.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Monomial {
    atoms: Vec<Ref>,
    coefficient: u64,
}

/// One factor inside a monomial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Factor {
    Coefficient(u64),
    Atom(Ref),
}

/// A sum of monomials, sorted by atoms with the constant last.
type Polynomial = Vec<Monomial>;

impl<'a> NaturalNormalizer<'a> {
    /// Normalizes sums and products only.
    #[must_use]
    pub fn new(naturals: &'a Naturals, ring: NaturalRing) -> Self {
        Self {
            calc: Calc {
                naturals,
                bool_ty: ring.signature.bool_ty,
                opaque: vec![ring.signature.add, ring.signature.mul, ring.signature.succ],
            },
            ring,
            subtraction: None,
            engine: NumeralEngine::Unary,
            applications: RefCell::new(HashMap::new()),
        }
    }

    /// Selects how literals are lowered.
    #[must_use]
    pub fn with_engine(mut self, engine: NumeralEngine) -> Self {
        self.engine = engine;
        self
    }

    /// The engine this normalizer lowers literals with.
    #[must_use]
    pub const fn engine(&self) -> NumeralEngine {
        self.engine
    }

    /// Normalizes sums, products, and truncated subtraction.
    #[must_use]
    pub fn with_subtraction(
        naturals: &'a Naturals,
        ring: NaturalRing,
        subtraction: NaturalSubtraction,
    ) -> Self {
        let mut normalizer = Self::new(naturals, ring);
        normalizer
            .calc
            .opaque
            .extend([subtraction.declaration.sub, subtraction.declaration.pred]);
        normalizer.subtraction = Some(subtraction);
        normalizer
    }

    /// Builds `function argument`, reusing an earlier identical application.
    fn app(&self, kernel: &mut Kernel, function: Ref, argument: Ref) -> Result<Ref, NaturalError> {
        if let Some(cached) = self.applications.borrow().get(&(function, argument)) {
            return Ok(*cached);
        }
        let term = kernel.app(function, argument)?;
        self.applications
            .borrow_mut()
            .insert((function, argument), term);
        Ok(term)
    }

    /// Builds `operation left right`.
    fn binary(
        &self,
        kernel: &mut Kernel,
        operation: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Ref, NaturalError> {
        let partial = self.app(kernel, operation, left)?;
        self.app(kernel, partial, right)
    }

    /// Runs one derivation on a staged kernel, committing only on success.
    ///
    /// The term cache names rows in whichever kernel is passed, so it starts
    /// empty and is emptied again afterwards. That keeps a normalizer usable
    /// with a forked or replaced kernel, at the cost of not sharing rows
    /// between calls.
    fn staged<T>(
        &self,
        kernel: &mut Kernel,
        action: impl FnOnce(&Self, &mut Kernel) -> Result<T, NaturalError>,
    ) -> Result<T, NaturalError> {
        self.applications.borrow_mut().clear();
        let mut forked = kernel.fork();
        let result = action(self, &mut forked);
        self.applications.borrow_mut().clear();
        let value = result?;
        *kernel = forked;
        Ok(value)
    }

    /// Builds the `succ` tower for one literal.
    ///
    /// # Errors
    ///
    /// Returns an error above [`MAX_LITERAL`].
    pub fn numeral(&self, kernel: &mut Kernel, value: u64) -> Result<Ref, NaturalError> {
        self.staged(kernel, |normalizer, kernel| {
            normalizer.build_numeral(kernel, value)
        })
    }

    fn build_numeral(&self, kernel: &mut Kernel, value: u64) -> Result<Ref, NaturalError> {
        if value > self.engine.max_literal() {
            return Err(NaturalError::WrongForm {
                expected: "a literal within the numeral bound",
            });
        }
        match self.engine {
            NumeralEngine::Unary => {
                let mut term = self.ring.signature.zero;
                for _ in 0..value {
                    term = self.app(kernel, self.ring.signature.succ, term)?;
                }
                Ok(term)
            }
            NumeralEngine::Binary => self.binary_numeral(kernel, value),
        }
    }

    /// `numeral(0) = 0`, `numeral(2k) = numeral(k) + numeral(k)`, and
    /// `numeral(2k + 1) = succ numeral(2k)`.
    ///
    /// Doubling zero collapses to zero, so every value has one term.
    fn binary_numeral(&self, kernel: &mut Kernel, value: u64) -> Result<Ref, NaturalError> {
        if value == 0 {
            return Ok(self.ring.signature.zero);
        }
        let doubled = self.binary_double(kernel, value / 2)?;
        if value.is_multiple_of(2) {
            Ok(doubled)
        } else {
            self.app(kernel, self.ring.signature.succ, doubled)
        }
    }

    /// The term for `2 * half`.
    fn binary_double(&self, kernel: &mut Kernel, half: u64) -> Result<Ref, NaturalError> {
        if half == 0 {
            return Ok(self.ring.signature.zero);
        }
        let inner = self.binary_numeral(kernel, half)?;
        self.binary(kernel, self.ring.signature.add, inner, inner)
    }

    /// Builds the HOL term an expression denotes.
    ///
    /// # Errors
    ///
    /// Returns an error for a literal above [`MAX_LITERAL`], for a subtraction
    /// when the package was built without one, or if the kernel rejects a
    /// construction.
    pub fn term(&self, kernel: &mut Kernel, expr: &Expr) -> Result<Ref, NaturalError> {
        self.staged(kernel, |normalizer, kernel| {
            normalizer.build_term(kernel, expr)
        })
    }

    fn build_term(&self, kernel: &mut Kernel, expr: &Expr) -> Result<Ref, NaturalError> {
        match expr.node() {
            Node::Atom(term) => Ok(*term),
            Node::Literal(value) => self.build_numeral(kernel, *value),
            Node::Add(left, right) => {
                let left = self.build_term(kernel, left)?;
                let right = self.build_term(kernel, right)?;
                self.binary(kernel, self.ring.signature.add, left, right)
            }
            Node::Mul(left, right) => {
                let left = self.build_term(kernel, left)?;
                let right = self.build_term(kernel, right)?;
                self.binary(kernel, self.ring.signature.mul, left, right)
            }
            Node::Sub(left, right) => {
                let sub = self.require_subtraction()?.declaration.sub;
                let left = self.build_term(kernel, left)?;
                let right = self.build_term(kernel, right)?;
                self.binary(kernel, sub, left, right)
            }
        }
    }

    /// Proves `⊢ expr = normal form`.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as [`term`](Self::term), or
    /// if a coefficient overflows.
    pub fn normalize(
        &self,
        kernel: &mut Kernel,
        expr: &Expr,
    ) -> Result<ProvedEquality, NaturalError> {
        self.staged(kernel, |normalizer, kernel| {
            Ok(normalizer.normal_form(kernel, expr)?.1)
        })
    }

    /// Proves `⊢ left = right` when both sides share a normal form.
    ///
    /// # Errors
    ///
    /// Returns an error if the normal forms differ, or under the same
    /// conditions as [`normalize`](Self::normalize).
    pub fn prove_equal(
        &self,
        kernel: &mut Kernel,
        left: &Expr,
        right: &Expr,
    ) -> Result<ProvedEquality, NaturalError> {
        self.staged(kernel, |normalizer, kernel| {
            let (left_polynomial, left_equality) = normalizer.normal_form(kernel, left)?;
            let (right_polynomial, right_equality) = normalizer.normal_form(kernel, right)?;
            if left_polynomial != right_polynomial {
                return Err(NaturalError::WrongForm {
                    expected: "two expressions with the same normal form",
                });
            }
            let reversed = normalizer.calc.symm(kernel, right_equality.theorem)?;
            let theorem = normalizer
                .calc
                .chain(kernel, &[left_equality.theorem, reversed])?;
            let equality = proved(kernel, theorem)?;
            join_same_syntax(kernel, equality.left, left_equality.left)?;
            join_same_syntax(kernel, equality.right, right_equality.left)?;
            Ok(equality)
        })
    }

    /// Evaluates a closed expression to a number, with a proof.
    ///
    /// # Errors
    ///
    /// Returns an error if the expression does not reduce to a literal, or
    /// under the same conditions as [`normalize`](Self::normalize).
    pub fn evaluate(
        &self,
        kernel: &mut Kernel,
        expr: &Expr,
    ) -> Result<(u64, ProvedEquality), NaturalError> {
        self.staged(kernel, |normalizer, kernel| {
            let (polynomial, equality) = normalizer.normal_form(kernel, expr)?;
            let value = match polynomial.as_slice() {
                [] => 0,
                [only] if only.atoms.is_empty() => only.coefficient,
                _ => {
                    return Err(NaturalError::WrongForm {
                        expected: "a closed arithmetic expression",
                    });
                }
            };
            // The returned number is read off the polynomial, so tie it to the
            // theorem rather than trusting the two to agree.
            let numeral = normalizer.build_numeral(kernel, value)?;
            join_same_syntax(kernel, equality.right, numeral)?;
            Ok((value, equality))
        })
    }

    fn require_subtraction(&self) -> Result<&NaturalSubtraction, NaturalError> {
        self.subtraction.as_ref().ok_or(NaturalError::WrongForm {
            expected: "a normalizer built with truncated subtraction",
        })
    }

    fn sum_monoid(&self) -> Monoid {
        Monoid {
            operation: self.ring.signature.add,
            unit: self.ring.signature.zero,
            associative: self.ring.proof.add_associative,
            commutative: self.ring.proof.add_commutative,
            exchange: self.ring.proof.add_exchange,
            left_unit: self.ring.proof.add_zero,
            right_unit: self.ring.proof.add_right_zero,
        }
    }

    fn product_monoid(&self) -> Monoid {
        Monoid {
            operation: self.ring.signature.mul,
            unit: self.ring.signature.one,
            associative: self.ring.proof.mul_associative,
            commutative: self.ring.proof.mul_commutative,
            exchange: self.ring.proof.mul_exchange,
            left_unit: self.ring.proof.mul_one,
            right_unit: self.ring.proof.mul_right_one,
        }
    }
}

/// A sorted list of terms in one commutative monoid.
///
/// Both the sum of monomials and the product inside a monomial are lists kept
/// in key order, so insertion and merging are written once here.
trait Sorted {
    type Item: Clone;
    type Key: Ord;

    fn monoid(&self) -> Monoid;

    /// Builds `left ∘ right`.
    fn binary(&self, kernel: &mut Kernel, left: Ref, right: Ref) -> Result<Ref, NaturalError>;

    fn key(&self, item: &Self::Item) -> Self::Key;

    fn render(&self, kernel: &mut Kernel, item: &Self::Item) -> Result<Ref, NaturalError>;

    /// `⊢ render(left) ∘ render(right) = render(combined)`, when the two
    /// combine into a single term.
    fn combine(
        &self,
        kernel: &mut Kernel,
        left: &Self::Item,
        right: &Self::Item,
    ) -> Result<Option<(Self::Item, ThmId)>, NaturalError>;
}

/// Builds `x1 ∘ x2 ∘ … ∘ xn`, left-nested; the empty list is the unit.
fn fold<T: Sorted>(terms: &T, kernel: &mut Kernel, items: &[T::Item]) -> Result<Ref, NaturalError> {
    match items.split_last() {
        None => Ok(terms.monoid().unit),
        Some((last, [])) => terms.render(kernel, last),
        Some((last, rest)) => {
            let head = fold(terms, kernel, rest)?;
            let tail = terms.render(kernel, last)?;
            terms.binary(kernel, head, tail)
        }
    }
}

/// Inserts one term into a sorted list.
///
/// Proves `⊢ fold(items) ∘ render(new) = fold(result)`.
fn insert<T: Sorted>(
    terms: &T,
    kernel: &mut Kernel,
    calc: &Calc<'_>,
    items: &[T::Item],
    new: &T::Item,
) -> Result<(Vec<T::Item>, ThmId), NaturalError> {
    let monoid = terms.monoid();
    let new_term = terms.render(kernel, new)?;
    let Some((last, rest)) = items.split_last() else {
        let theorem = calc.at(kernel, monoid.left_unit, &[new_term])?;
        return Ok((vec![new.clone()], theorem));
    };
    let last_term = terms.render(kernel, last)?;

    // `new` combines with the term already at the end.
    if terms.key(last) == terms.key(new)
        && let Some((combined, step)) = terms.combine(kernel, last, new)?
    {
        let mut result = rest.to_vec();
        result.push(combined);
        if rest.is_empty() {
            return Ok((result, step));
        }
        let head = fold(terms, kernel, rest)?;
        let regroup = calc.at(kernel, monoid.associative, &[head, last_term, new_term])?;
        let inner = on_right(kernel, monoid.operation, head, step)?;
        let theorem = calc.chain(kernel, &[regroup, inner])?;
        return Ok((result, theorem));
    }

    // `new` belongs at the end, where the list already puts it.
    if terms.key(last) <= terms.key(new) {
        let whole = fold(terms, kernel, items)?;
        let applied = terms.binary(kernel, whole, new_term)?;
        let theorem = kernel.refl(calc.bool_ty, applied)?.theorem;
        let mut result = items.to_vec();
        result.push(new.clone());
        return Ok((result, theorem));
    }

    // `new` sorts before `last`, so swap them and keep going left.
    if rest.is_empty() {
        let theorem = calc.at(kernel, monoid.commutative, &[last_term, new_term])?;
        return Ok((vec![new.clone(), last.clone()], theorem));
    }
    let head = fold(terms, kernel, rest)?;
    let swap = calc.at(kernel, monoid.exchange, &[head, last_term, new_term])?;
    let (inserted, inner) = insert(terms, kernel, calc, rest, new)?;
    let lifted = on_left(kernel, monoid.operation, inner, last_term)?;
    let theorem = calc.chain(kernel, &[swap, lifted])?;
    let mut result = inserted;
    result.push(last.clone());
    Ok((result, theorem))
}

/// Merges two sorted lists.
///
/// Proves `⊢ fold(left) ∘ fold(right) = fold(result)`.
fn merge<T: Sorted>(
    terms: &T,
    kernel: &mut Kernel,
    calc: &Calc<'_>,
    left: &[T::Item],
    right: &[T::Item],
) -> Result<(Vec<T::Item>, ThmId), NaturalError> {
    let monoid = terms.monoid();
    let Some((last, rest)) = right.split_last() else {
        let whole = fold(terms, kernel, left)?;
        let theorem = calc.at(kernel, monoid.right_unit, &[whole])?;
        return Ok((left.to_vec(), theorem));
    };
    if rest.is_empty() {
        return insert(terms, kernel, calc, left, last);
    }
    let left_term = fold(terms, kernel, left)?;
    let head = fold(terms, kernel, rest)?;
    let last_term = terms.render(kernel, last)?;
    let regroup = calc.at(kernel, monoid.associative, &[left_term, head, last_term])?;
    let regroup = calc.symm(kernel, regroup)?;
    let (merged, inner) = merge(terms, kernel, calc, left, rest)?;
    let lifted = on_left(kernel, monoid.operation, inner, last_term)?;
    let (result, tail) = insert(terms, kernel, calc, &merged, last)?;
    let theorem = calc.chain(kernel, &[regroup, lifted, tail])?;
    Ok((result, theorem))
}

/// The summands of a polynomial.
struct Summands<'n, 'a>(&'n NaturalNormalizer<'a>);

/// The factors inside one monomial.
struct Factors<'n, 'a>(&'n NaturalNormalizer<'a>);

impl Sorted for Summands<'_, '_> {
    type Item = Monomial;
    /// Constants sort last, so a literal subtraction can peel one off the end.
    type Key = (bool, Vec<Ref>);

    fn monoid(&self) -> Monoid {
        self.0.sum_monoid()
    }

    fn binary(&self, kernel: &mut Kernel, left: Ref, right: Ref) -> Result<Ref, NaturalError> {
        self.0
            .binary(kernel, self.0.ring.signature.add, left, right)
    }

    fn key(&self, item: &Self::Item) -> Self::Key {
        (item.atoms.is_empty(), item.atoms.clone())
    }

    fn render(&self, kernel: &mut Kernel, item: &Self::Item) -> Result<Ref, NaturalError> {
        self.0.render_monomial(kernel, item)
    }

    fn combine(
        &self,
        kernel: &mut Kernel,
        left: &Self::Item,
        right: &Self::Item,
    ) -> Result<Option<(Self::Item, ThmId)>, NaturalError> {
        self.0.add_monomials(kernel, left, right).map(Some)
    }
}

impl Sorted for Factors<'_, '_> {
    type Item = Factor;
    /// The coefficient sorts before every atom.
    type Key = (u8, Option<Ref>);

    fn monoid(&self) -> Monoid {
        self.0.product_monoid()
    }

    fn binary(&self, kernel: &mut Kernel, left: Ref, right: Ref) -> Result<Ref, NaturalError> {
        self.0
            .binary(kernel, self.0.ring.signature.mul, left, right)
    }

    fn key(&self, item: &Self::Item) -> Self::Key {
        match item {
            Factor::Coefficient(_) => (0, None),
            Factor::Atom(atom) => (1, Some(*atom)),
        }
    }

    fn render(&self, kernel: &mut Kernel, item: &Self::Item) -> Result<Ref, NaturalError> {
        match item {
            Factor::Coefficient(value) => self.0.build_numeral(kernel, *value),
            Factor::Atom(atom) => Ok(*atom),
        }
    }

    fn combine(
        &self,
        kernel: &mut Kernel,
        left: &Self::Item,
        right: &Self::Item,
    ) -> Result<Option<(Self::Item, ThmId)>, NaturalError> {
        let (Factor::Coefficient(left), Factor::Coefficient(right)) = (left, right) else {
            return Ok(None);
        };
        let product = left.checked_mul(*right).ok_or(NaturalError::WrongForm {
            expected: "a coefficient product within range",
        })?;
        let theorem = self.0.mul_numerals(kernel, *left, *right)?;
        Ok(Some((Factor::Coefficient(product), theorem)))
    }
}

/// Numerals, monomials, and the polynomial arithmetic built on top of them.
impl NaturalNormalizer<'_> {
    /// `⊢ succ numeral(value) = numeral(value + 1)`.
    ///
    /// A unary numeral already carries its successor on the outside, so this is
    /// reflexivity there.
    fn succ_numeral(&self, kernel: &mut Kernel, value: u64) -> Result<ThmId, NaturalError> {
        match self.engine {
            NumeralEngine::Unary => {
                let term = self.build_numeral(kernel, value + 1)?;
                Ok(kernel.refl(self.calc.bool_ty, term)?.theorem)
            }
            NumeralEngine::Binary => self.succ_numeral_binary(kernel, value),
        }
    }

    /// `⊢ pred numeral(value) = numeral(value - 1)`, truncated at zero.
    fn pred_numeral(
        &self,
        kernel: &mut Kernel,
        subtraction: &NaturalSubtraction,
        value: u64,
    ) -> Result<ThmId, NaturalError> {
        if value == 0 {
            return Ok(subtraction.proof.pred_zero);
        }
        let pred = subtraction.declaration.pred;
        let previous = self.build_numeral(kernel, value - 1)?;
        // numeral(v) is succ numeral(v - 1), so pred strips the successor.
        let raise = self.succ_numeral(kernel, value - 1)?;
        let raise = self.calc.symm(kernel, raise)?;
        let under = under(kernel, pred, raise)?;
        let strip = self
            .calc
            .at(kernel, subtraction.proof.pred_successor, &[previous])?;
        self.calc.chain(kernel, &[under, strip])
    }

    /// `⊢ numeral x - numeral y = numeral (x - y)`, truncated at zero.
    ///
    /// One step per unit of `y`, which is what the byte layer needs: indices
    /// and slice bounds are small even when the values are not.
    fn sub_numerals(
        &self,
        kernel: &mut Kernel,
        subtraction: &NaturalSubtraction,
        left: u64,
        right: u64,
    ) -> Result<ThmId, NaturalError> {
        let pred = subtraction.declaration.pred;
        let left_term = self.build_numeral(kernel, left)?;
        let mut theorem = self
            .calc
            .at(kernel, subtraction.proof.sub_zero, &[left_term])?;
        for taken in 1..=right {
            let previous = self.build_numeral(kernel, taken - 1)?;
            // `sub.successor` is stated at `succ b`, and a binary numeral is not
            // syntactically the successor of its predecessor, so say so first.
            let raise = self.succ_numeral(kernel, taken - 1)?;
            let raise = self.calc.symm(kernel, raise)?;
            let shaped = on_right(kernel, subtraction.declaration.sub, left_term, raise)?;
            let expand = self.calc.at(
                kernel,
                subtraction.proof.sub_successor,
                &[left_term, previous],
            )?;
            let expand = self.calc.chain(kernel, &[shaped, expand])?;
            let inner = under(kernel, pred, theorem)?;
            let collapse = self.pred_numeral(kernel, subtraction, left.saturating_sub(taken - 1))?;
            theorem = self.calc.chain(kernel, &[expand, inner, collapse])?;
        }
        Ok(theorem)
    }

    /// `⊢ succ numeral(value) = numeral(value + 1)`, for binary numerals.
    ///
    /// An even value already carries its successor on the outside, so only an
    /// odd one has to do work: it turns into a double, which needs the same
    /// fact one bit down.
    fn succ_numeral_binary(
        &self,
        kernel: &mut Kernel,
        value: u64,
    ) -> Result<ThmId, NaturalError> {
        let add = self.ring.signature.add;
        let succ = self.ring.signature.succ;
        let term = self.binary_numeral(kernel, value)?;
        let raised = self.app(kernel, succ, term)?;
        let next = value.checked_add(1).ok_or(NaturalError::WrongForm {
            expected: "a literal successor within range",
        })?;
        let target = self.binary_numeral(kernel, next)?;
        if raised == target {
            return Ok(kernel.refl(self.calc.bool_ty, raised)?.theorem);
        }

        // value = 2a + 1, so the successor carries: succ (succ (2a)) = 2(a + 1).
        let half = value / 2;
        let inner = self.binary_numeral(kernel, half)?;
        let next = self.binary_numeral(kernel, half + 1)?;
        let raised_inner = self.app(kernel, succ, inner)?;
        let carried = self.succ_numeral_binary(kernel, half)?;
        let carried = self.calc.symm(kernel, carried)?; // numeral(a + 1) = succ numeral(a)

        let left = on_left(kernel, add, carried, next)?;
        let right = on_right(kernel, add, raised_inner, carried)?;
        let expand = self.calc.at(
            kernel,
            self.ring.proof.add_successor,
            &[inner, raised_inner],
        )?;
        let shift = self
            .calc
            .at(kernel, self.ring.proof.add_right_successor, &[inner, inner])?;
        let shift = self.calc.under_succ(kernel, shift)?;
        let mut steps = vec![left, right, expand, shift];
        if half == 0 {
            // Doubling zero collapses, so the two sides meet at succ (succ 0).
            let zero = self.ring.signature.zero;
            let collapse = self.calc.at(kernel, self.ring.proof.add_zero, &[zero])?;
            let once = self.calc.under_succ(kernel, collapse)?;
            steps.push(self.calc.under_succ(kernel, once)?);
        }
        let forward = self.calc.chain(kernel, &steps)?;
        self.calc.symm(kernel, forward)
    }

    /// `⊢ 2a + 2b = 2(a + b)`, on the doubled halves of two binary numerals.
    fn double_sum(
        &self,
        kernel: &mut Kernel,
        left: u64,
        right: u64,
    ) -> Result<ThmId, NaturalError> {
        let add = self.ring.signature.add;
        let doubled_right = self.binary_double(kernel, right)?;
        if left == 0 {
            return self
                .calc
                .at(kernel, self.ring.proof.add_zero, &[doubled_right]);
        }
        let doubled_left = self.binary_double(kernel, left)?;
        if right == 0 {
            return self
                .calc
                .at(kernel, self.ring.proof.add_right_zero, &[doubled_left]);
        }
        let first = self.binary_numeral(kernel, left)?;
        let second = self.binary_numeral(kernel, right)?;
        let total = left.checked_add(right).ok_or(NaturalError::WrongForm {
            expected: "a literal sum within range",
        })?;
        let summed = self.binary_numeral(kernel, total)?;
        let pair = self.binary(kernel, add, first, second)?;

        let regroup = self.calc.at(
            kernel,
            self.ring.proof.add_interchange,
            &[first, first, second, second],
        )?;
        let halves = self.add_numerals(kernel, left, right)?;
        let outer = on_left(kernel, add, halves, pair)?;
        let inner = on_right(kernel, add, summed, halves)?;
        self.calc.chain(kernel, &[regroup, outer, inner])
    }

    /// `⊢ x + y = x + y` evaluated: `numeral x + numeral y = numeral (x + y)`.
    fn add_numerals(
        &self,
        kernel: &mut Kernel,
        left: u64,
        right: u64,
    ) -> Result<ThmId, NaturalError> {
        match self.engine {
            NumeralEngine::Unary => self.add_numerals_unary(kernel, left, right),
            NumeralEngine::Binary => self.add_numerals_binary(kernel, left, right),
        }
    }

    fn add_numerals_unary(
        &self,
        kernel: &mut Kernel,
        left: u64,
        right: u64,
    ) -> Result<ThmId, NaturalError> {
        let right_term = self.build_numeral(kernel, right)?;
        let mut theorem = self
            .calc
            .at(kernel, self.ring.proof.add_zero, &[right_term])?;
        for count in 1..=left {
            let previous = self.build_numeral(kernel, count - 1)?;
            let expand = self.calc.at(
                kernel,
                self.ring.proof.add_successor,
                &[previous, right_term],
            )?;
            let lifted = self.calc.under_succ(kernel, theorem)?;
            theorem = self.calc.chain(kernel, &[expand, lifted])?;
        }
        Ok(theorem)
    }

    /// `numeral x * numeral y = numeral (x * y)`.
    fn mul_numerals(
        &self,
        kernel: &mut Kernel,
        left: u64,
        right: u64,
    ) -> Result<ThmId, NaturalError> {
        match self.engine {
            NumeralEngine::Unary => self.mul_numerals_unary(kernel, left, right),
            NumeralEngine::Binary => self.mul_numerals_binary(kernel, left, right),
        }
    }

    fn mul_numerals_unary(
        &self,
        kernel: &mut Kernel,
        left: u64,
        right: u64,
    ) -> Result<ThmId, NaturalError> {
        // Refuse a product the engine could not build, rather than spending
        // O(left * right) steps on the way to the same error.
        let product = left.checked_mul(right).ok_or(NaturalError::WrongForm {
            expected: "a numeral product within range",
        })?;
        if product > self.engine.max_literal() {
            return Err(NaturalError::WrongForm {
                expected: "a literal within the numeral bound",
            });
        }
        let right_term = self.build_numeral(kernel, right)?;
        let mut theorem = self
            .calc
            .at(kernel, self.ring.proof.mul_zero, &[right_term])?;
        for count in 1..=left {
            let previous = self.build_numeral(kernel, count - 1)?;
            let expand = self.calc.at(
                kernel,
                self.ring.proof.mul_successor,
                &[previous, right_term],
            )?;
            let lifted = on_left(kernel, self.ring.signature.add, theorem, right_term)?;
            let partial = (count - 1)
                .checked_mul(right)
                .ok_or(NaturalError::WrongForm {
                    expected: "a numeral product within range",
                })?;
            let collapse = self.add_numerals(kernel, partial, right)?;
            theorem = self.calc.chain(kernel, &[expand, lifted, collapse])?;
        }
        Ok(theorem)
    }

    /// `numeral x + numeral y = numeral (x + y)`, one bit at a time.
    fn add_numerals_binary(
        &self,
        kernel: &mut Kernel,
        left: u64,
        right: u64,
    ) -> Result<ThmId, NaturalError> {
        let right_term = self.binary_numeral(kernel, right)?;
        if left == 0 {
            return self
                .calc
                .at(kernel, self.ring.proof.add_zero, &[right_term]);
        }
        let left_term = self.binary_numeral(kernel, left)?;
        if right == 0 {
            return self
                .calc
                .at(kernel, self.ring.proof.add_right_zero, &[left_term]);
        }

        let (left_half, right_half) = (left / 2, right / 2);
        let doubled_left = self.binary_double(kernel, left_half)?;
        let doubled_right = self.binary_double(kernel, right_half)?;
        let halves = self.double_sum(kernel, left_half, right_half)?;

        match (left % 2, right % 2) {
            (0, 0) => Ok(halves),
            (1, 0) => {
                let expand = self.calc.at(
                    kernel,
                    self.ring.proof.add_successor,
                    &[doubled_left, doubled_right],
                )?;
                let lifted = self.calc.under_succ(kernel, halves)?;
                self.calc.chain(kernel, &[expand, lifted])
            }
            (0, 1) => {
                let expand = self.calc.at(
                    kernel,
                    self.ring.proof.add_right_successor,
                    &[doubled_left, doubled_right],
                )?;
                let lifted = self.calc.under_succ(kernel, halves)?;
                self.calc.chain(kernel, &[expand, lifted])
            }
            // Both bits set, so the sum carries into the next bit.
            _ => {
                let raised_right = self.app(kernel, self.ring.signature.succ, doubled_right)?;
                let expand = self.calc.at(
                    kernel,
                    self.ring.proof.add_successor,
                    &[doubled_left, raised_right],
                )?;
                let shift = self.calc.at(
                    kernel,
                    self.ring.proof.add_right_successor,
                    &[doubled_left, doubled_right],
                )?;
                let shift = self.calc.under_succ(kernel, shift)?;
                let lifted = self.calc.under_succ(kernel, halves)?;
                let lifted = self.calc.under_succ(kernel, lifted)?;
                let carry_from = left_half
                    .checked_add(right_half)
                    .and_then(|half| half.checked_mul(2))
                    .and_then(|even| even.checked_add(1))
                    .ok_or(NaturalError::WrongForm {
                        expected: "a literal sum within range",
                    })?;
                let carry = self.succ_numeral(kernel, carry_from)?;
                self.calc.chain(kernel, &[expand, shift, lifted, carry])
            }
        }
    }

    /// `numeral x * numeral y = numeral (x * y)`, one bit of `x` at a time.
    fn mul_numerals_binary(
        &self,
        kernel: &mut Kernel,
        left: u64,
        right: u64,
    ) -> Result<ThmId, NaturalError> {
        let add = self.ring.signature.add;
        let right_term = self.binary_numeral(kernel, right)?;
        if left == 0 {
            return self
                .calc
                .at(kernel, self.ring.proof.mul_zero, &[right_term]);
        }
        let left_term = self.binary_numeral(kernel, left)?;
        if right == 0 {
            return self
                .calc
                .at(kernel, self.ring.proof.mul_right_zero, &[left_term]);
        }
        if left == 1 {
            return self.calc.at(kernel, self.ring.proof.mul_one, &[right_term]);
        }

        let half = left / 2;
        let inner = self.binary_numeral(kernel, half)?;
        let partial = half.checked_mul(right).ok_or(NaturalError::WrongForm {
            expected: "a literal product within range",
        })?;
        let partial_term = self.binary_numeral(kernel, partial)?;
        let product = self.binary(kernel, self.ring.signature.mul, inner, right_term)?;

        // 2a * y = a*y + a*y, which is the doubled numeral for a*y.
        let split = self.calc.at(
            kernel,
            self.ring.proof.mul_right_distributive,
            &[inner, inner, right_term],
        )?;
        let recursed = self.mul_numerals_binary(kernel, half, right)?;
        let outer = on_left(kernel, add, recursed, product)?;
        let folded = on_right(kernel, add, partial_term, recursed)?;
        let even = self.calc.chain(kernel, &[split, outer, folded])?;
        if left.is_multiple_of(2) {
            return Ok(even);
        }

        // 2a + 1 times y is the even case plus one more y.
        let doubled = self.binary_double(kernel, half)?;
        let expand = self.calc.at(
            kernel,
            self.ring.proof.mul_successor,
            &[doubled, right_term],
        )?;
        let rewritten = on_left(kernel, add, even, right_term)?;
        let doubled_partial = partial.checked_mul(2).ok_or(NaturalError::WrongForm {
            expected: "a literal product within range",
        })?;
        let total = self.add_numerals(kernel, doubled_partial, right)?;
        self.calc.chain(kernel, &[expand, rewritten, total])
    }

    /// The factor list of a monomial: its coefficient, then its atoms.
    fn factors(monomial: &Monomial) -> Vec<Factor> {
        let mut factors = vec![Factor::Coefficient(monomial.coefficient)];
        factors.extend(monomial.atoms.iter().copied().map(Factor::Atom));
        factors
    }

    fn monomial_from_factors(factors: &[Factor]) -> Result<Monomial, NaturalError> {
        let mut coefficient = None;
        let mut atoms = Vec::new();
        for factor in factors {
            match factor {
                Factor::Coefficient(value) if coefficient.is_none() => coefficient = Some(*value),
                Factor::Coefficient(_) => {
                    return Err(NaturalError::WrongForm {
                        expected: "one coefficient in a monomial",
                    });
                }
                Factor::Atom(atom) => atoms.push(*atom),
            }
        }
        Ok(Monomial {
            atoms,
            coefficient: coefficient.ok_or(NaturalError::WrongForm {
                expected: "a monomial with a coefficient",
            })?,
        })
    }

    fn render_monomial(
        &self,
        kernel: &mut Kernel,
        monomial: &Monomial,
    ) -> Result<Ref, NaturalError> {
        fold(&Factors(self), kernel, &Self::factors(monomial))
    }

    fn sum_fold(&self, kernel: &mut Kernel, polynomial: &[Monomial]) -> Result<Ref, NaturalError> {
        fold(&Summands(self), kernel, polynomial)
    }

    /// The product of a monomial's atoms; the empty product is one.
    fn atom_product(&self, kernel: &mut Kernel, atoms: &[Ref]) -> Result<Ref, NaturalError> {
        match atoms.split_last() {
            None => Ok(self.ring.signature.one),
            Some((last, [])) => Ok(*last),
            Some((last, rest)) => {
                let head = self.atom_product(kernel, rest)?;
                self.binary(kernel, self.ring.signature.mul, head, *last)
            }
        }
    }

    /// `⊢ render(monomial) = numeral(coefficient) * atom_product`.
    ///
    /// The rendered monomial nests to the left, so the coefficient is buried;
    /// this pulls it back out with associativity.
    fn scaled(&self, kernel: &mut Kernel, monomial: &Monomial) -> Result<ThmId, NaturalError> {
        let mul = self.ring.signature.mul;
        let coefficient = self.build_numeral(kernel, monomial.coefficient)?;
        let Some((first, rest)) = monomial.atoms.split_first() else {
            let unit = self
                .calc
                .at(kernel, self.ring.proof.mul_right_one, &[coefficient])?;
            return self.calc.symm(kernel, unit);
        };
        let mut atoms = *first;
        let mut theorem = {
            let scaled = self.binary(kernel, mul, coefficient, *first)?;
            kernel.refl(self.calc.bool_ty, scaled)?.theorem
        };
        for atom in rest {
            let lifted = on_left(kernel, mul, theorem, *atom)?;
            let regroup = self.calc.at(
                kernel,
                self.ring.proof.mul_associative,
                &[coefficient, atoms, *atom],
            )?;
            theorem = self.calc.chain(kernel, &[lifted, regroup])?;
            atoms = self.binary(kernel, mul, atoms, *atom)?;
        }
        Ok(theorem)
    }

    /// `⊢ render(left) + render(right) = render(combined)` for two monomials
    /// with the same atoms.
    fn add_monomials(
        &self,
        kernel: &mut Kernel,
        left: &Monomial,
        right: &Monomial,
    ) -> Result<(Monomial, ThmId), NaturalError> {
        let add = self.ring.signature.add;
        let mul = self.ring.signature.mul;
        let total =
            left.coefficient
                .checked_add(right.coefficient)
                .ok_or(NaturalError::WrongForm {
                    expected: "a coefficient sum within range",
                })?;
        let combined = Monomial {
            atoms: left.atoms.clone(),
            coefficient: total,
        };

        let atoms = self.atom_product(kernel, &left.atoms)?;
        let left_coefficient = self.build_numeral(kernel, left.coefficient)?;
        let right_coefficient = self.build_numeral(kernel, right.coefficient)?;
        let right_term = self.render_monomial(kernel, right)?;
        let scaled_left = self.scaled(kernel, left)?;
        let scaled_right = self.scaled(kernel, right)?;
        let first = on_left(kernel, add, scaled_left, right_term)?;
        let left_scaled = self.binary(kernel, mul, left_coefficient, atoms)?;
        let second = on_right(kernel, add, left_scaled, scaled_right)?;
        let gather = self.calc.at(
            kernel,
            self.ring.proof.mul_right_distributive,
            &[left_coefficient, right_coefficient, atoms],
        )?;
        let gather = self.calc.symm(kernel, gather)?;
        let evaluate = self.add_numerals(kernel, left.coefficient, right.coefficient)?;
        let folded = on_left(kernel, mul, evaluate, atoms)?;
        let back = self.scaled(kernel, &combined)?;
        let back = self.calc.symm(kernel, back)?;
        let theorem = self
            .calc
            .chain(kernel, &[first, second, gather, folded, back])?;
        Ok((combined, theorem))
    }

    /// `⊢ render(left) * render(right) = render(product)`.
    fn multiply_monomials(
        &self,
        kernel: &mut Kernel,
        left: &Monomial,
        right: &Monomial,
    ) -> Result<(Monomial, ThmId), NaturalError> {
        let (merged, theorem) = merge(
            &Factors(self),
            kernel,
            &self.calc,
            &Self::factors(left),
            &Self::factors(right),
        )?;
        Ok((Self::monomial_from_factors(&merged)?, theorem))
    }

    /// `⊢ render(monomial) * sum_fold(polynomial) = sum_fold(result)`.
    fn multiply_monomial_polynomial(
        &self,
        kernel: &mut Kernel,
        monomial: &Monomial,
        polynomial: &[Monomial],
    ) -> Result<(Polynomial, ThmId), NaturalError> {
        let add = self.ring.signature.add;
        let mul = self.ring.signature.mul;
        let monomial_term = self.render_monomial(kernel, monomial)?;
        let Some((last, rest)) = polynomial.split_last() else {
            let theorem = self
                .calc
                .at(kernel, self.ring.proof.mul_right_zero, &[monomial_term])?;
            return Ok((Vec::new(), theorem));
        };
        if rest.is_empty() {
            let (product, theorem) = self.multiply_monomials(kernel, monomial, last)?;
            return Ok((vec![product], theorem));
        }
        let head = self.sum_fold(kernel, rest)?;
        let last_term = self.render_monomial(kernel, last)?;
        let split = self.calc.at(
            kernel,
            self.ring.proof.mul_left_distributive,
            &[monomial_term, head, last_term],
        )?;
        let (head_polynomial, head_theorem) =
            self.multiply_monomial_polynomial(kernel, monomial, rest)?;
        let (product, product_theorem) = self.multiply_monomials(kernel, monomial, last)?;
        let tail_term = self.binary(kernel, mul, monomial_term, last_term)?;
        let first = on_left(kernel, add, head_theorem, tail_term)?;
        let head_normal = self.sum_fold(kernel, &head_polynomial)?;
        let second = on_right(kernel, add, head_normal, product_theorem)?;
        let (result, gather) = insert(
            &Summands(self),
            kernel,
            &self.calc,
            &head_polynomial,
            &product,
        )?;
        let theorem = self.calc.chain(kernel, &[split, first, second, gather])?;
        Ok((result, theorem))
    }

    /// `⊢ sum_fold(left) * sum_fold(right) = sum_fold(result)`.
    fn multiply_polynomials(
        &self,
        kernel: &mut Kernel,
        left: &[Monomial],
        right: &[Monomial],
    ) -> Result<(Polynomial, ThmId), NaturalError> {
        let add = self.ring.signature.add;
        let mul = self.ring.signature.mul;
        let right_term = self.sum_fold(kernel, right)?;
        let Some((last, rest)) = left.split_last() else {
            let theorem = self
                .calc
                .at(kernel, self.ring.proof.mul_zero, &[right_term])?;
            return Ok((Vec::new(), theorem));
        };
        if rest.is_empty() {
            return self.multiply_monomial_polynomial(kernel, last, right);
        }
        let head = self.sum_fold(kernel, rest)?;
        let last_term = self.render_monomial(kernel, last)?;
        let split = self.calc.at(
            kernel,
            self.ring.proof.mul_right_distributive,
            &[head, last_term, right_term],
        )?;
        let (head_polynomial, head_theorem) = self.multiply_polynomials(kernel, rest, right)?;
        let (tail_polynomial, tail_theorem) =
            self.multiply_monomial_polynomial(kernel, last, right)?;
        let tail_term = self.binary(kernel, mul, last_term, right_term)?;
        let first = on_left(kernel, add, head_theorem, tail_term)?;
        let head_normal = self.sum_fold(kernel, &head_polynomial)?;
        let second = on_right(kernel, add, head_normal, tail_theorem)?;
        let (result, gather) = merge(
            &Summands(self),
            kernel,
            &self.calc,
            &head_polynomial,
            &tail_polynomial,
        )?;
        let theorem = self.calc.chain(kernel, &[split, first, second, gather])?;
        Ok((result, theorem))
    }

    /// `⊢ sum_fold(polynomial) - numeral(amount) = sum_fold(result)`.
    ///
    /// Only a literal no larger than the polynomial's constant term can be
    /// cancelled; anything else leaves truncation visible and is refused.
    fn subtract_literal(
        &self,
        kernel: &mut Kernel,
        polynomial: &[Monomial],
        amount: u64,
    ) -> Result<(Polynomial, ThmId), NaturalError> {
        let subtraction = *self.require_subtraction()?;
        let add = self.ring.signature.add;
        let sub = subtraction.declaration.sub;
        let whole = self.sum_fold(kernel, polynomial)?;
        if amount == 0 {
            let theorem = self.calc.at(kernel, subtraction.proof.sub_zero, &[whole])?;
            return Ok((polynomial.to_vec(), theorem));
        }

        let (rest, constant) = match polynomial.split_last() {
            Some((last, rest)) if last.atoms.is_empty() => (rest, last.coefficient),
            _ => (polynomial, 0),
        };
        let remainder = constant
            .checked_sub(amount)
            .ok_or(NaturalError::WrongForm {
                expected: "a subtrahend no larger than the constant term",
            })?;
        let subtrahend = self.build_numeral(kernel, amount)?;
        let remainder_term = self.build_numeral(kernel, remainder)?;
        let mut result = rest.to_vec();
        if remainder > 0 {
            result.push(Monomial {
                atoms: Vec::new(),
                coefficient: remainder,
            });
        }

        // constant = remainder + amount, so the subtrahend can be cancelled.
        let split = self.add_numerals(kernel, remainder, amount)?;
        let split = self.calc.symm(kernel, split)?;
        if rest.is_empty() {
            let folded = on_left(kernel, sub, split, subtrahend)?;
            let cancel = self.calc.at(
                kernel,
                subtraction.proof.sub_add_cancel,
                &[remainder_term, subtrahend],
            )?;
            let theorem = self.calc.chain(kernel, &[folded, cancel])?;
            return Ok((result, theorem));
        }

        let head = self.sum_fold(kernel, rest)?;
        let lift = on_right(kernel, add, head, split)?;
        let regroup = self.calc.at(
            kernel,
            self.ring.proof.add_associative,
            &[head, remainder_term, subtrahend],
        )?;
        let regroup = self.calc.symm(kernel, regroup)?;
        let rebuilt = self.calc.chain(kernel, &[lift, regroup])?;
        let folded = on_left(kernel, sub, rebuilt, subtrahend)?;
        let cancelled = self.binary(kernel, add, head, remainder_term)?;
        let cancel = self.calc.at(
            kernel,
            subtraction.proof.sub_add_cancel,
            &[cancelled, subtrahend],
        )?;
        let mut steps = vec![folded, cancel];
        if remainder == 0 {
            steps.push(
                self.calc
                    .at(kernel, self.ring.proof.add_right_zero, &[head])?,
            );
        }
        let theorem = self.calc.chain(kernel, &steps)?;
        Ok((result, theorem))
    }
}

/// Walking an expression, and tidying the result.
impl NaturalNormalizer<'_> {
    /// The polynomial of an expression, with `⊢ term(expr) = sum_fold(it)`.
    fn polynomial(
        &self,
        kernel: &mut Kernel,
        expr: &Expr,
    ) -> Result<(Polynomial, ThmId), NaturalError> {
        match expr.node() {
            Node::Atom(term) => self.atom_polynomial(kernel, *term),
            Node::Literal(value) => {
                let term = self.build_numeral(kernel, *value)?;
                let polynomial = if *value == 0 {
                    Vec::new()
                } else {
                    vec![Monomial {
                        atoms: Vec::new(),
                        coefficient: *value,
                    }]
                };
                Ok((polynomial, kernel.refl(self.calc.bool_ty, term)?.theorem))
            }
            Node::Add(left, right) => {
                let (left_polynomial, left_theorem) = self.polynomial(kernel, left)?;
                let (right_polynomial, right_theorem) = self.polynomial(kernel, right)?;
                let steps = self.congruence(
                    kernel,
                    self.ring.signature.add,
                    right,
                    &left_polynomial,
                    left_theorem,
                    right_theorem,
                )?;
                let (result, gather) = merge(
                    &Summands(self),
                    kernel,
                    &self.calc,
                    &left_polynomial,
                    &right_polynomial,
                )?;
                let theorem = self.calc.chain(kernel, &[steps.0, steps.1, gather])?;
                Ok((result, theorem))
            }
            Node::Mul(left, right) => {
                let (left_polynomial, left_theorem) = self.polynomial(kernel, left)?;
                let (right_polynomial, right_theorem) = self.polynomial(kernel, right)?;
                let steps = self.congruence(
                    kernel,
                    self.ring.signature.mul,
                    right,
                    &left_polynomial,
                    left_theorem,
                    right_theorem,
                )?;
                let (result, gather) =
                    self.multiply_polynomials(kernel, &left_polynomial, &right_polynomial)?;
                let theorem = self.calc.chain(kernel, &[steps.0, steps.1, gather])?;
                Ok((result, theorem))
            }
            Node::Sub(left, right) => self.subtraction_polynomial(kernel, left, right),
        }
    }

    /// An opaque term becomes the single monomial `1 * term`.
    fn atom_polynomial(
        &self,
        kernel: &mut Kernel,
        term: Ref,
    ) -> Result<(Polynomial, ThmId), NaturalError> {
        let unit = self.calc.at(kernel, self.ring.proof.mul_one, &[term])?;
        let theorem = self.calc.symm(kernel, unit)?;
        Ok((
            vec![Monomial {
                atoms: vec![term],
                coefficient: 1,
            }],
            theorem,
        ))
    }

    /// Rewrites both operands of `operation` to their normal forms.
    ///
    /// Returns the two steps of
    /// `term(l) ∘ term(r) = fold(pl) ∘ term(r) = fold(pl) ∘ fold(pr)`.
    fn congruence(
        &self,
        kernel: &mut Kernel,
        operation: Ref,
        right: &Expr,
        left_polynomial: &[Monomial],
        left_theorem: ThmId,
        right_theorem: ThmId,
    ) -> Result<(ThmId, ThmId), NaturalError> {
        let right_term = self.build_term(kernel, right)?;
        let first = on_left(kernel, operation, left_theorem, right_term)?;
        let left_normal = self.sum_fold(kernel, left_polynomial)?;
        let second = on_right(kernel, operation, left_normal, right_theorem)?;
        Ok((first, second))
    }

    /// Truncated subtraction: cancelled when the subtrahend is a small enough
    /// literal, and left as an opaque atom otherwise.
    fn subtraction_polynomial(
        &self,
        kernel: &mut Kernel,
        left: &Expr,
        right: &Expr,
    ) -> Result<(Polynomial, ThmId), NaturalError> {
        let sub = self.require_subtraction()?.declaration.sub;
        let (left_polynomial, left_theorem) = self.polynomial(kernel, left)?;
        let (right_polynomial, right_theorem) = self.polynomial(kernel, right)?;

        let amount = constant_value(&right_polynomial);

        // Two literals always fold, even when the result truncates to zero.
        if let (Some(from), Some(taken)) = (constant_value(&left_polynomial), amount) {
            let subtraction = *self.require_subtraction()?;
            let steps = self.congruence(
                kernel,
                sub,
                right,
                &left_polynomial,
                left_theorem,
                right_theorem,
            )?;
            let fold = self.sub_numerals(kernel, &subtraction, from, taken)?;
            let theorem = self.calc.chain(kernel, &[steps.0, steps.1, fold])?;
            let remainder = from.saturating_sub(taken);
            let polynomial = if remainder == 0 {
                Vec::new()
            } else {
                vec![Monomial {
                    atoms: Vec::new(),
                    coefficient: remainder,
                }]
            };
            return Ok((polynomial, theorem));
        }

        let cancellable =
            amount.is_some_and(|amount| amount <= trailing_constant(&left_polynomial));
        let Some(amount) = amount.filter(|_| cancellable) else {
            // The atom is keyed on the normalized operands, not on the input
            // syntax. Otherwise `(x + y) - z` and `(y + x) - z` become different
            // atoms, and neither collects with the other.
            let steps = self.congruence(
                kernel,
                sub,
                right,
                &left_polynomial,
                left_theorem,
                right_theorem,
            )?;
            let left_normal = self.sum_fold(kernel, &left_polynomial)?;
            let right_normal = self.sum_fold(kernel, &right_polynomial)?;
            let atom = self.binary(kernel, sub, left_normal, right_normal)?;
            let (polynomial, unit) = self.atom_polynomial(kernel, atom)?;
            let theorem = self.calc.chain(kernel, &[steps.0, steps.1, unit])?;
            return Ok((polynomial, theorem));
        };

        let steps = self.congruence(
            kernel,
            sub,
            right,
            &left_polynomial,
            left_theorem,
            right_theorem,
        )?;
        let (result, cancel) = self.subtract_literal(kernel, &left_polynomial, amount)?;
        let theorem = self.calc.chain(kernel, &[steps.0, steps.1, cancel])?;
        Ok((result, theorem))
    }

    /// `⊢ sum_fold(polynomial) = <the printed normal form>`.
    ///
    /// The only difference is that a coefficient of one is dropped, so `x * y`
    /// prints as `x * y` rather than `1 * x * y`.
    fn beautify(
        &self,
        kernel: &mut Kernel,
        polynomial: &[Monomial],
    ) -> Result<(Ref, ThmId), NaturalError> {
        let add = self.ring.signature.add;
        let Some((first, rest)) = polynomial.split_first() else {
            let zero = self.ring.signature.zero;
            return Ok((zero, kernel.refl(self.calc.bool_ty, zero)?.theorem));
        };
        let (mut pretty, mut theorem) = self.beautify_monomial(kernel, first)?;
        for monomial in rest {
            let canonical = self.render_monomial(kernel, monomial)?;
            let (nice, step) = self.beautify_monomial(kernel, monomial)?;
            let lifted = on_left(kernel, add, theorem, canonical)?;
            let inner = on_right(kernel, add, pretty, step)?;
            theorem = self.calc.chain(kernel, &[lifted, inner])?;
            pretty = self.binary(kernel, add, pretty, nice)?;
        }
        Ok((pretty, theorem))
    }

    fn beautify_monomial(
        &self,
        kernel: &mut Kernel,
        monomial: &Monomial,
    ) -> Result<(Ref, ThmId), NaturalError> {
        if monomial.coefficient == 1 && !monomial.atoms.is_empty() {
            let atoms = self.atom_product(kernel, &monomial.atoms)?;
            let scaled = self.scaled(kernel, monomial)?;
            let drop = self.calc.at(kernel, self.ring.proof.mul_one, &[atoms])?;
            let theorem = self.calc.chain(kernel, &[scaled, drop])?;
            return Ok((atoms, theorem));
        }
        let canonical = self.render_monomial(kernel, monomial)?;
        Ok((
            canonical,
            kernel.refl(self.calc.bool_ty, canonical)?.theorem,
        ))
    }

    fn normal_form(
        &self,
        kernel: &mut Kernel,
        expr: &Expr,
    ) -> Result<(Polynomial, ProvedEquality), NaturalError> {
        let source = self.build_term(kernel, expr)?;
        let (polynomial, theorem) = self.polynomial(kernel, expr)?;
        let (_, tidy) = self.beautify(kernel, &polynomial)?;
        let theorem = self.calc.chain(kernel, &[theorem, tidy])?;
        let equality = proved(kernel, theorem)?;
        // The caller is told this theorem is about `expr`; check that it is.
        join_same_syntax(kernel, equality.left, source)?;
        Ok((polynomial, equality))
    }
}

/// The value of a polynomial with no atoms.
fn constant_value(polynomial: &[Monomial]) -> Option<u64> {
    match polynomial {
        [] => Some(0),
        [only] if only.atoms.is_empty() => Some(only.coefficient),
        _ => None,
    }
}

/// The polynomial's constant term, or zero if it has none.
fn trailing_constant(polynomial: &[Monomial]) -> u64 {
    match polynomial.split_last() {
        Some((last, _)) if last.atoms.is_empty() => last.coefficient,
        _ => 0,
    }
}

/// Reads a theorem's single equality conclusion back as a [`ProvedEquality`].
///
/// The endpoints come from the theorem rather than from a freshly built row,
/// so they are the exact syntax the kernel checked.
fn proved(kernel: &Kernel, theorem: ThmId) -> Result<ProvedEquality, NaturalError> {
    let equality = sole_conclusion(kernel, theorem)?;
    let [_, left, right] = exact_equality(kernel, equality)?;
    Ok(ProvedEquality {
        left,
        right,
        equality,
        theorem,
    })
}
