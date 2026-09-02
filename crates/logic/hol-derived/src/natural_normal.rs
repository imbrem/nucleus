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
    natural_calc::{Calc, on_left, on_right},
    natural_expr::Node,
    syntax::join_same_syntax,
};

/// Largest literal the normalizer will build as a `succ` tower.
pub const MAX_LITERAL: u64 = 4096;

/// Normalizes arithmetic expressions against one proved law package.
///
/// A normalizer holds kernel-local theorem handles and caches the terms it
/// builds, so use one with the single kernel it was created for.
pub struct NaturalNormalizer<'a> {
    calc: Calc<'a>,
    ring: NaturalRing,
    subtraction: Option<NaturalSubtraction>,
    /// Applications already built, so equal terms share one row.
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
            applications: RefCell::new(HashMap::new()),
        }
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
    /// The term cache names rows in this kernel, so a discarded attempt drops
    /// it too.
    fn staged<T>(
        &self,
        kernel: &mut Kernel,
        action: impl FnOnce(&Self, &mut Kernel) -> Result<T, NaturalError>,
    ) -> Result<T, NaturalError> {
        let mut forked = kernel.fork();
        match action(self, &mut forked) {
            Ok(value) => {
                *kernel = forked;
                Ok(value)
            }
            Err(error) => {
                self.applications.borrow_mut().clear();
                Err(error)
            }
        }
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
        if value > MAX_LITERAL {
            return Err(NaturalError::WrongForm {
                expected: "a literal within the unary numeral bound",
            });
        }
        let mut term = self.ring.signature.zero;
        for _ in 0..value {
            term = self.app(kernel, self.ring.signature.succ, term)?;
        }
        Ok(term)
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
    /// `⊢ x + y = x + y` evaluated: `numeral x + numeral y = numeral (x + y)`.
    fn add_numerals(
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
        let cancellable =
            amount.is_some_and(|amount| amount <= trailing_constant(&left_polynomial));
        let Some(amount) = amount.filter(|_| cancellable) else {
            let left_term = self.build_term(kernel, left)?;
            let right_term = self.build_term(kernel, right)?;
            let atom = self.binary(kernel, sub, left_term, right_term)?;
            return self.atom_polynomial(kernel, atom);
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
