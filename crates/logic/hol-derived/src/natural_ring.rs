//! Commutative-semiring laws for the natural numbers.
//!
//! [`NaturalArithmetic`] fixes `add` and `mul` and proves their recursion
//! equations. This module adds what a normalizer needs on top: associativity,
//! commutativity, the units, and both distributive laws.
//!
//! Nothing here is trusted. Every law goes through the public checked kernel
//! operations, and no new axiom or capability is introduced.
//!
//! Every statement quantifies left to right, so `mul.right_distributive` reads
//! `∀a b c. (a + b) * c = a * c + b * c` and is instantiated in that order. The
//! seven inherited equations are restated the same way, so a caller never has
//! to remember which package a law came from.

use covalence_logic_hol::{Kernel, Ref, ThmId};

use crate::{
    NaturalArithmetic, NaturalError, NaturalNameSupply, Naturals,
    natural_arithmetic::{apply2, next_global_name},
    natural_calc::{Calc, Law, on_left, on_right, quantify},
};

/// Semiring law statements over the natural numbers.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NaturalRingDecl {
    /// First name reserved for this package's temporary binders.
    pub base_name: u64,
    /// `∀a. 0 + a = a`.
    pub add_zero: Ref,
    /// `∀a b. succ a + b = succ (a + b)`.
    pub add_successor: Ref,
    /// `∀a. a + 0 = a`.
    pub add_right_zero: Ref,
    /// `∀a b. a + succ b = succ (a + b)`.
    pub add_right_successor: Ref,
    /// `∀a b. a + b = b + a`.
    pub add_commutative: Ref,
    /// `∀a b c. (a + b) + c = a + (b + c)`.
    pub add_associative: Ref,
    /// `∀a b c. (a + b) + c = (a + c) + b`.
    pub add_exchange: Ref,
    /// `∀a b c d. (a + b) + (c + d) = (a + c) + (b + d)`.
    pub add_interchange: Ref,
    /// `∀a. 0 * a = 0`.
    pub mul_zero: Ref,
    /// `∀a b. succ a * b = a * b + b`.
    pub mul_successor: Ref,
    /// `∀a. a * 0 = 0`.
    pub mul_right_zero: Ref,
    /// `∀a b. a * succ b = a * b + a`.
    pub mul_right_successor: Ref,
    /// `∀a. 1 * a = a`.
    pub mul_one: Ref,
    /// `∀a. a * 1 = a`.
    pub mul_right_one: Ref,
    /// `∀a b. a * b = b * a`.
    pub mul_commutative: Ref,
    /// `∀a b c. (a * b) * c = a * (b * c)`.
    pub mul_associative: Ref,
    /// `∀a b c. (a * b) * c = (a * c) * b`.
    pub mul_exchange: Ref,
    /// `∀a b c. (a + b) * c = a * c + b * c`.
    pub mul_right_distributive: Ref,
    /// `∀a b c. a * (b + c) = a * b + a * c`.
    pub mul_left_distributive: Ref,
}

/// Exact theorem handles certifying a [`NaturalRingDecl`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NaturalRingProof {
    /// Exact theorem `⊢ add_zero`.
    pub add_zero: ThmId,
    /// Exact theorem `⊢ add_successor`.
    pub add_successor: ThmId,
    /// Exact theorem `⊢ add_right_zero`.
    pub add_right_zero: ThmId,
    /// Exact theorem `⊢ add_right_successor`.
    pub add_right_successor: ThmId,
    /// Exact theorem `⊢ add_commutative`.
    pub add_commutative: ThmId,
    /// Exact theorem `⊢ add_associative`.
    pub add_associative: ThmId,
    /// Exact theorem `⊢ add_exchange`.
    pub add_exchange: ThmId,
    /// Exact theorem `⊢ add_interchange`.
    pub add_interchange: ThmId,
    /// Exact theorem `⊢ mul_zero`.
    pub mul_zero: ThmId,
    /// Exact theorem `⊢ mul_successor`.
    pub mul_successor: ThmId,
    /// Exact theorem `⊢ mul_right_zero`.
    pub mul_right_zero: ThmId,
    /// Exact theorem `⊢ mul_right_successor`.
    pub mul_right_successor: ThmId,
    /// Exact theorem `⊢ mul_one`.
    pub mul_one: ThmId,
    /// Exact theorem `⊢ mul_right_one`.
    pub mul_right_one: ThmId,
    /// Exact theorem `⊢ mul_commutative`.
    pub mul_commutative: ThmId,
    /// Exact theorem `⊢ mul_associative`.
    pub mul_associative: ThmId,
    /// Exact theorem `⊢ mul_exchange`.
    pub mul_exchange: ThmId,
    /// Exact theorem `⊢ mul_right_distributive`.
    pub mul_right_distributive: ThmId,
    /// Exact theorem `⊢ mul_left_distributive`.
    pub mul_left_distributive: ThmId,
}

/// A semiring law package certified in one checked kernel.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NaturalRing {
    /// Law statements.
    pub declaration: NaturalRingDecl,
    /// Kernel-local exact theorem handles.
    pub proof: NaturalRingProof,
    /// Symbols this package reasons about.
    pub signature: NaturalRingSignature,
}

/// The syntax a [`NaturalRing`] operates on.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NaturalRingSignature {
    /// The natural-number type.
    pub ty: Ref,
    /// The Boolean type carrying every equality.
    pub bool_ty: Ref,
    /// `nat.zero`.
    pub zero: Ref,
    /// `nat.succ`.
    pub succ: Ref,
    /// `succ zero`.
    pub one: Ref,
    /// `nat.add`.
    pub add: Ref,
    /// `nat.mul`.
    pub mul: Ref,
}

impl NaturalRing {
    /// Resolves one law name.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<Ref> {
        self.symbols()
            .find_map(|(candidate, reference, _)| (candidate == name).then_some(reference))
    }

    /// Resolves one law name to its exact theorem.
    #[must_use]
    pub fn theorem(&self, name: &str) -> Option<ThmId> {
        self.symbols()
            .find_map(|(candidate, _, theorem)| (candidate == name).then_some(theorem))
    }

    /// Iterates every law as `(name, statement, theorem)`.
    #[must_use]
    pub fn symbols(&self) -> impl ExactSizeIterator<Item = (&'static str, Ref, ThmId)> {
        let declaration = self.declaration;
        let proof = self.proof;
        [
            ("nat.add.zero", declaration.add_zero, proof.add_zero),
            (
                "nat.add.successor",
                declaration.add_successor,
                proof.add_successor,
            ),
            (
                "nat.add.right_zero",
                declaration.add_right_zero,
                proof.add_right_zero,
            ),
            (
                "nat.add.right_successor",
                declaration.add_right_successor,
                proof.add_right_successor,
            ),
            (
                "nat.add.commutative",
                declaration.add_commutative,
                proof.add_commutative,
            ),
            (
                "nat.add.associative",
                declaration.add_associative,
                proof.add_associative,
            ),
            (
                "nat.add.exchange",
                declaration.add_exchange,
                proof.add_exchange,
            ),
            (
                "nat.add.interchange",
                declaration.add_interchange,
                proof.add_interchange,
            ),
            ("nat.mul.zero", declaration.mul_zero, proof.mul_zero),
            (
                "nat.mul.successor",
                declaration.mul_successor,
                proof.mul_successor,
            ),
            (
                "nat.mul.right_zero",
                declaration.mul_right_zero,
                proof.mul_right_zero,
            ),
            (
                "nat.mul.right_successor",
                declaration.mul_right_successor,
                proof.mul_right_successor,
            ),
            ("nat.mul.one", declaration.mul_one, proof.mul_one),
            (
                "nat.mul.right_one",
                declaration.mul_right_one,
                proof.mul_right_one,
            ),
            (
                "nat.mul.commutative",
                declaration.mul_commutative,
                proof.mul_commutative,
            ),
            (
                "nat.mul.associative",
                declaration.mul_associative,
                proof.mul_associative,
            ),
            (
                "nat.mul.exchange",
                declaration.mul_exchange,
                proof.mul_exchange,
            ),
            (
                "nat.mul.right_distributive",
                declaration.mul_right_distributive,
                proof.mul_right_distributive,
            ),
            (
                "nat.mul.left_distributive",
                declaration.mul_left_distributive,
                proof.mul_left_distributive,
            ),
        ]
        .into_iter()
    }
}

/// Userspace derivation of the natural-number semiring laws.
pub trait NaturalRingExt {
    /// Proves the semiring laws over an existing arithmetic package.
    ///
    /// # Errors
    ///
    /// Returns an error if `arithmetic` does not have the checked shape this
    /// derivation expects, or if any ordinary kernel operation rejects a step.
    fn natural_ring(
        &mut self,
        naturals: &Naturals,
        arithmetic: &NaturalArithmetic,
    ) -> Result<NaturalRing, NaturalError>;

    /// Proves the semiring laws using an explicit binder-name block.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as
    /// [`natural_ring`](Self::natural_ring), or when `base_name` is not above
    /// every name reachable from the inputs.
    fn natural_ring_at(
        &mut self,
        naturals: &Naturals,
        arithmetic: &NaturalArithmetic,
        base_name: u64,
    ) -> Result<NaturalRing, NaturalError>;
}

impl NaturalRingExt for Kernel {
    fn natural_ring(
        &mut self,
        naturals: &Naturals,
        arithmetic: &NaturalArithmetic,
    ) -> Result<NaturalRing, NaturalError> {
        let base_name = next_global_name(self)?;
        self.natural_ring_at(naturals, arithmetic, base_name)
    }

    fn natural_ring_at(
        &mut self,
        naturals: &Naturals,
        arithmetic: &NaturalArithmetic,
        base_name: u64,
    ) -> Result<NaturalRing, NaturalError> {
        let minimum = self.fresh_name(
            &naturals
                .declaration
                .references()
                .chain(arithmetic.declaration.references())
                .collect::<Vec<_>>(),
        )?;
        if base_name < minimum {
            return Err(NaturalError::WrongForm {
                expected: "a hygienic semiring binder-name block",
            });
        }
        let mut staged = self.fork();
        let ring = derive(&mut staged, naturals, arithmetic, base_name)?;
        *self = staged;
        Ok(ring)
    }
}

/// Working state for the derivation: the syntax it builds terms from, and the
/// laws proved so far.
struct Semiring<'a> {
    calc: Calc<'a>,
    signature: NaturalRingSignature,
    add_zero: ThmId,
    add_successor: ThmId,
    add_right_zero: ThmId,
    add_right_successor: ThmId,
    add_commutative: ThmId,
    add_associative: ThmId,
    add_exchange: ThmId,
    mul_zero: ThmId,
    mul_successor: ThmId,
    mul_right_zero: ThmId,
    mul_right_successor: ThmId,
    mul_commutative: ThmId,
    mul_right_distributive: ThmId,
}

fn derive(
    kernel: &mut Kernel,
    naturals: &Naturals,
    arithmetic: &NaturalArithmetic,
    base_name: u64,
) -> Result<NaturalRing, NaturalError> {
    let mut names = NaturalNameSupply::new(base_name);
    let declared = arithmetic.declaration;
    let signature = NaturalRingSignature {
        ty: naturals.ty,
        bool_ty: kernel.classifier(naturals.zero_ne_succ)?,
        zero: naturals.zero,
        succ: naturals.succ,
        one: declared.one,
        add: declared.add,
        mul: declared.mul,
    };
    let mut ring = Semiring {
        calc: Calc {
            naturals,
            bool_ty: signature.bool_ty,
            opaque: vec![declared.add, declared.mul, naturals.succ],
        },
        signature,
        add_zero: arithmetic.proof.add_zero,
        add_successor: arithmetic.proof.add_successor,
        add_right_zero: arithmetic.proof.add_right_zero,
        add_right_successor: arithmetic.proof.add_right_successor,
        add_commutative: arithmetic.proof.add_commutative,
        mul_zero: arithmetic.proof.mul_zero,
        mul_successor: arithmetic.proof.mul_successor,
        // Filled in as they are proved; each is used only afterwards.
        add_associative: arithmetic.proof.add_zero,
        add_exchange: arithmetic.proof.add_zero,
        mul_right_zero: arithmetic.proof.mul_zero,
        mul_right_successor: arithmetic.proof.mul_zero,
        mul_commutative: arithmetic.proof.mul_zero,
        mul_right_distributive: arithmetic.proof.mul_zero,
    };

    let inherited = ring.restate_equations(kernel, &mut names)?;
    let derived = ring.prove_derived(kernel, &mut names)?;
    Ok(assemble(base_name, signature, &inherited, &derived))
}

/// The seven recursion equations, restated so every law binds left to right.
struct Inherited {
    add_zero: Law,
    add_successor: Law,
    add_right_zero: Law,
    add_right_successor: Law,
    add_commutative: Law,
    mul_zero: Law,
    mul_successor: Law,
}

/// The eleven laws this module proves.
struct Derived {
    add_associative: Law,
    add_exchange: Law,
    add_interchange: Law,
    mul_right_zero: Law,
    mul_right_successor: Law,
    mul_one: Law,
    mul_right_one: Law,
    mul_commutative: Law,
    mul_associative: Law,
    mul_exchange: Law,
    mul_right_distributive: Law,
    mul_left_distributive: Law,
}

impl Semiring<'_> {
    fn restate_equations(
        &mut self,
        kernel: &mut Kernel,
        names: &mut NaturalNameSupply,
    ) -> Result<Inherited, NaturalError> {
        let a = self.calc.variable(kernel, names)?;
        let b = self.calc.variable(kernel, names)?;
        let inherited = Inherited {
            add_zero: self.restate(kernel, self.add_zero, &[a], &[a])?,
            add_successor: self.restate(kernel, self.add_successor, &[a, b], &[a, b])?,
            add_right_zero: self.restate(kernel, self.add_right_zero, &[a], &[a])?,
            add_right_successor: self.restate(
                kernel,
                self.add_right_successor,
                &[b, a],
                &[a, b],
            )?,
            add_commutative: self.restate(kernel, self.add_commutative, &[b, a], &[a, b])?,
            mul_zero: self.restate(kernel, self.mul_zero, &[a], &[a])?,
            mul_successor: self.restate(kernel, self.mul_successor, &[a, b], &[a, b])?,
        };
        self.add_zero = inherited.add_zero.1;
        self.add_successor = inherited.add_successor.1;
        self.add_right_zero = inherited.add_right_zero.1;
        self.add_right_successor = inherited.add_right_successor.1;
        self.add_commutative = inherited.add_commutative.1;
        self.mul_zero = inherited.mul_zero.1;
        self.mul_successor = inherited.mul_successor.1;
        Ok(inherited)
    }

    /// Proves the eleven laws in dependency order.
    fn prove_derived(
        &mut self,
        kernel: &mut Kernel,
        names: &mut NaturalNameSupply,
    ) -> Result<Derived, NaturalError> {
        let add_associative = self.prove_add_associative(kernel, names)?;
        self.add_associative = add_associative.1;
        let add_exchange = self.prove_exchange(
            kernel,
            names,
            self.signature.add,
            self.add_associative,
            self.add_commutative,
        )?;
        self.add_exchange = add_exchange.1;
        let add_interchange = self.prove_add_interchange(kernel, names)?;
        let mul_right_zero = self.prove_mul_right_zero(kernel, names)?;
        self.mul_right_zero = mul_right_zero.1;
        let mul_right_successor = self.prove_mul_right_successor(kernel, names)?;
        self.mul_right_successor = mul_right_successor.1;
        let mul_one = self.prove_mul_one(kernel, names)?;
        let mul_right_one = self.prove_mul_right_one(kernel, names)?;
        let mul_commutative = self.prove_mul_commutative(kernel, names)?;
        self.mul_commutative = mul_commutative.1;
        let mul_right_distributive = self.prove_mul_right_distributive(kernel, names)?;
        self.mul_right_distributive = mul_right_distributive.1;
        let mul_left_distributive = self.prove_mul_left_distributive(kernel, names)?;
        let mul_associative = self.prove_mul_associative(kernel, names)?;
        let mul_exchange = self.prove_exchange(
            kernel,
            names,
            self.signature.mul,
            mul_associative.1,
            self.mul_commutative,
        )?;
        Ok(Derived {
            add_associative,
            add_exchange,
            add_interchange,
            mul_right_zero,
            mul_right_successor,
            mul_one,
            mul_right_one,
            mul_commutative,
            mul_associative,
            mul_exchange,
            mul_right_distributive,
            mul_left_distributive,
        })
    }
}

fn assemble(
    base_name: u64,
    signature: NaturalRingSignature,
    inherited: &Inherited,
    derived: &Derived,
) -> NaturalRing {
    NaturalRing {
        declaration: NaturalRingDecl {
            base_name,
            add_zero: inherited.add_zero.0,
            add_successor: inherited.add_successor.0,
            add_right_zero: inherited.add_right_zero.0,
            add_right_successor: inherited.add_right_successor.0,
            add_commutative: inherited.add_commutative.0,
            add_associative: derived.add_associative.0,
            add_exchange: derived.add_exchange.0,
            add_interchange: derived.add_interchange.0,
            mul_zero: inherited.mul_zero.0,
            mul_successor: inherited.mul_successor.0,
            mul_right_zero: derived.mul_right_zero.0,
            mul_right_successor: derived.mul_right_successor.0,
            mul_one: derived.mul_one.0,
            mul_right_one: derived.mul_right_one.0,
            mul_commutative: derived.mul_commutative.0,
            mul_associative: derived.mul_associative.0,
            mul_exchange: derived.mul_exchange.0,
            mul_right_distributive: derived.mul_right_distributive.0,
            mul_left_distributive: derived.mul_left_distributive.0,
        },
        proof: NaturalRingProof {
            add_zero: inherited.add_zero.1,
            add_successor: inherited.add_successor.1,
            add_right_zero: inherited.add_right_zero.1,
            add_right_successor: inherited.add_right_successor.1,
            add_commutative: inherited.add_commutative.1,
            add_associative: derived.add_associative.1,
            add_exchange: derived.add_exchange.1,
            add_interchange: derived.add_interchange.1,
            mul_zero: inherited.mul_zero.1,
            mul_successor: inherited.mul_successor.1,
            mul_right_zero: derived.mul_right_zero.1,
            mul_right_successor: derived.mul_right_successor.1,
            mul_one: derived.mul_one.1,
            mul_right_one: derived.mul_right_one.1,
            mul_commutative: derived.mul_commutative.1,
            mul_associative: derived.mul_associative.1,
            mul_exchange: derived.mul_exchange.1,
            mul_right_distributive: derived.mul_right_distributive.1,
            mul_left_distributive: derived.mul_left_distributive.1,
        },
        signature,
    }
}

impl Semiring<'_> {
    fn sum(&self, kernel: &mut Kernel, left: Ref, right: Ref) -> Result<Ref, NaturalError> {
        apply2(kernel, self.signature.add, left, right)
    }

    fn product(&self, kernel: &mut Kernel, left: Ref, right: Ref) -> Result<Ref, NaturalError> {
        apply2(kernel, self.signature.mul, left, right)
    }

    fn next(&self, kernel: &mut Kernel, value: Ref) -> Result<Ref, NaturalError> {
        self.calc.next(kernel, value)
    }

    fn equation(&self, kernel: &mut Kernel, left: Ref, right: Ref) -> Result<Ref, NaturalError> {
        self.calc.equation(kernel, left, right)
    }

    fn symm(&self, kernel: &mut Kernel, theorem: ThmId) -> Result<ThmId, NaturalError> {
        self.calc.symm(kernel, theorem)
    }

    fn chain(&self, kernel: &mut Kernel, steps: &[ThmId]) -> Result<ThmId, NaturalError> {
        self.calc.chain(kernel, steps)
    }

    fn under_succ(&self, kernel: &mut Kernel, theorem: ThmId) -> Result<ThmId, NaturalError> {
        self.calc.under_succ(kernel, theorem)
    }

    fn add_left(
        &self,
        kernel: &mut Kernel,
        theorem: ThmId,
        right: Ref,
    ) -> Result<ThmId, NaturalError> {
        on_left(kernel, self.signature.add, theorem, right)
    }

    fn add_right(
        &self,
        kernel: &mut Kernel,
        left: Ref,
        theorem: ThmId,
    ) -> Result<ThmId, NaturalError> {
        on_right(kernel, self.signature.add, left, theorem)
    }

    fn mul_left(
        &self,
        kernel: &mut Kernel,
        theorem: ThmId,
        right: Ref,
    ) -> Result<ThmId, NaturalError> {
        on_left(kernel, self.signature.mul, theorem, right)
    }

    fn at(
        &self,
        kernel: &mut Kernel,
        law: ThmId,
        arguments: &[Ref],
    ) -> Result<ThmId, NaturalError> {
        self.calc.at(kernel, law, arguments)
    }

    fn restate(
        &self,
        kernel: &mut Kernel,
        law: ThmId,
        arguments: &[Ref],
        binders: &[Ref],
    ) -> Result<Law, NaturalError> {
        self.calc.restate(kernel, law, arguments, binders)
    }

    #[allow(clippy::too_many_arguments)]
    fn by_induction(
        &self,
        kernel: &mut Kernel,
        names: &mut NaturalNameSupply,
        binder: Ref,
        body: Ref,
        binders: &[Ref],
        base: impl FnOnce(&mut Kernel) -> Result<ThmId, NaturalError>,
        step: impl FnOnce(&mut Kernel, ThmId) -> Result<ThmId, NaturalError>,
    ) -> Result<Law, NaturalError> {
        self.calc
            .by_induction(kernel, names, binder, body, binders, base, step)
    }
}

/// The eleven derived laws. Each proof is a chain of rewrites; the comment on
/// a step names the term it produces.
impl Semiring<'_> {
    /// `∀a b c. (a + b) + c = a + (b + c)`, by induction on `a`.
    fn prove_add_associative(
        &self,
        kernel: &mut Kernel,
        names: &mut NaturalNameSupply,
    ) -> Result<Law, NaturalError> {
        let [a, b, c] = self.triple(kernel, names)?;
        let sum_ab = self.sum(kernel, a, b)?;
        let sum_bc = self.sum(kernel, b, c)?;
        let left = self.sum(kernel, sum_ab, c)?;
        let right = self.sum(kernel, a, sum_bc)?;
        let body = self.equation(kernel, left, right)?;
        self.by_induction(
            kernel,
            names,
            a,
            body,
            &[a, b, c],
            |kernel| {
                let zero_b = self.at(kernel, self.add_zero, &[b])?;
                let lifted = self.add_left(kernel, zero_b, c)?; // (0 + b) + c = b + c
                let zero_bc = self.at(kernel, self.add_zero, &[sum_bc])?;
                let reversed = self.symm(kernel, zero_bc)?; // b + c = 0 + (b + c)
                self.chain(kernel, &[lifted, reversed])
            },
            |kernel, hypothesis| {
                let successor = self.at(kernel, self.add_successor, &[a, b])?;
                let outer = self.add_left(kernel, successor, c)?; // succ (a + b) + c
                let shift = self.at(kernel, self.add_successor, &[sum_ab, c])?; // succ ((a + b) + c)
                let inner = self.under_succ(kernel, hypothesis)?; // succ (a + (b + c))
                let regroup = self.at(kernel, self.add_successor, &[a, sum_bc])?;
                let regroup = self.symm(kernel, regroup)?; // succ a + (b + c)
                self.chain(kernel, &[outer, shift, inner, regroup])
            },
        )
    }

    /// `∀a b c. (a ∘ b) ∘ c = (a ∘ c) ∘ b` for an associative, commutative `∘`.
    fn prove_exchange(
        &self,
        kernel: &mut Kernel,
        names: &mut NaturalNameSupply,
        operation: Ref,
        associative: ThmId,
        commutative: ThmId,
    ) -> Result<Law, NaturalError> {
        let [a, b, c] = self.triple(kernel, names)?;
        let regroup = self.at(kernel, associative, &[a, b, c])?; // a ∘ (b ∘ c)
        let swap = self.at(kernel, commutative, &[b, c])?;
        let swapped = on_right(kernel, operation, a, swap)?; // a ∘ (c ∘ b)
        let back = self.at(kernel, associative, &[a, c, b])?;
        let back = self.symm(kernel, back)?; // (a ∘ c) ∘ b
        let theorem = self.chain(kernel, &[regroup, swapped, back])?;
        quantify(kernel, theorem, &[a, b, c])
    }

    /// `∀a b c d. (a + b) + (c + d) = (a + c) + (b + d)`.
    ///
    /// Binary numerals add two at a time, so this is the law that lets two
    /// doubled halves recombine.
    fn prove_add_interchange(
        &self,
        kernel: &mut Kernel,
        names: &mut NaturalNameSupply,
    ) -> Result<Law, NaturalError> {
        let [a, b, c] = self.triple(kernel, names)?;
        let d = self.calc.variable(kernel, names)?;
        let left_pair = self.sum(kernel, a, b)?;
        let right_pair = self.sum(kernel, a, c)?;
        let flatten = self.at(kernel, self.add_associative, &[left_pair, c, d])?;
        let flatten = self.symm(kernel, flatten)?; // ((a + b) + c) + d
        let swap = self.at(kernel, self.add_exchange, &[a, b, c])?;
        let swap = self.add_left(kernel, swap, d)?; // ((a + c) + b) + d
        let regroup = self.at(kernel, self.add_associative, &[right_pair, b, d])?;
        let theorem = self.chain(kernel, &[flatten, swap, regroup])?;
        quantify(kernel, theorem, &[a, b, c, d])
    }

    /// `∀a. a * 0 = 0`, by induction on `a`.
    fn prove_mul_right_zero(
        &self,
        kernel: &mut Kernel,
        names: &mut NaturalNameSupply,
    ) -> Result<Law, NaturalError> {
        let zero = self.signature.zero;
        let a = names.variable(kernel, self.signature.ty)?;
        let left = self.product(kernel, a, zero)?;
        let body = self.equation(kernel, left, zero)?;
        self.by_induction(
            kernel,
            names,
            a,
            body,
            &[a],
            |kernel| self.at(kernel, self.mul_zero, &[zero]),
            |kernel, hypothesis| {
                let expand = self.at(kernel, self.mul_successor, &[a, zero])?; // a * 0 + 0
                let collapse = self.add_left(kernel, hypothesis, zero)?; // 0 + 0
                let unit = self.at(kernel, self.add_zero, &[zero])?; // 0
                self.chain(kernel, &[expand, collapse, unit])
            },
        )
    }

    /// `∀a b. a * succ b = a * b + a`, by induction on `a`.
    fn prove_mul_right_successor(
        &self,
        kernel: &mut Kernel,
        names: &mut NaturalNameSupply,
    ) -> Result<Law, NaturalError> {
        let zero = self.signature.zero;
        let a = names.variable(kernel, self.signature.ty)?;
        let b = names.variable(kernel, self.signature.ty)?;
        let next_b = self.next(kernel, b)?;
        let next_a = self.next(kernel, a)?;
        let product = self.product(kernel, a, b)?;
        let left = self.product(kernel, a, next_b)?;
        let right = self.sum(kernel, product, a)?;
        let body = self.equation(kernel, left, right)?;
        let with_b = self.sum(kernel, product, b)?;
        self.by_induction(
            kernel,
            names,
            a,
            body,
            &[a, b],
            |kernel| {
                let vanish = self.at(kernel, self.mul_zero, &[next_b])?; // 0
                let factor = self.at(kernel, self.mul_zero, &[b])?;
                let summand = self.add_left(kernel, factor, zero)?; // 0 + 0
                let unit = self.at(kernel, self.add_zero, &[zero])?; // 0
                let target = self.chain(kernel, &[summand, unit])?;
                let target = self.symm(kernel, target)?;
                self.chain(kernel, &[vanish, target])
            },
            |kernel, hypothesis| {
                let expand = self.at(kernel, self.mul_successor, &[a, next_b])?; // a * succ b + succ b
                let rewritten = self.add_left(kernel, hypothesis, next_b)?; // (a * b + a) + succ b
                let shift = self.at(kernel, self.add_right_successor, &[right, b])?;
                let swap = self.at(kernel, self.add_exchange, &[product, a, b])?;
                let swap = self.under_succ(kernel, swap)?; // succ ((a * b + b) + a)
                let target = self.at(kernel, self.mul_successor, &[a, b])?;
                let target = self.add_left(kernel, target, next_a)?; // (a * b + b) + succ a
                let target_shift = self.at(kernel, self.add_right_successor, &[with_b, a])?;
                let target_shift = self.symm(kernel, target_shift)?;
                let target = self.symm(kernel, target)?;
                self.chain(
                    kernel,
                    &[expand, rewritten, shift, swap, target_shift, target],
                )
            },
        )
    }

    /// `∀a. 1 * a = a`.
    fn prove_mul_one(
        &self,
        kernel: &mut Kernel,
        names: &mut NaturalNameSupply,
    ) -> Result<Law, NaturalError> {
        let zero = self.signature.zero;
        let a = names.variable(kernel, self.signature.ty)?;
        let expand = self.at(kernel, self.mul_successor, &[zero, a])?; // 0 * a + a
        let vanish = self.at(kernel, self.mul_zero, &[a])?;
        let collapse = self.add_left(kernel, vanish, a)?; // 0 + a
        let unit = self.at(kernel, self.add_zero, &[a])?; // a
        let theorem = self.chain(kernel, &[expand, collapse, unit])?;
        quantify(kernel, theorem, &[a])
    }

    /// `∀a. a * 1 = a`.
    fn prove_mul_right_one(
        &self,
        kernel: &mut Kernel,
        names: &mut NaturalNameSupply,
    ) -> Result<Law, NaturalError> {
        let zero = self.signature.zero;
        let a = names.variable(kernel, self.signature.ty)?;
        let expand = self.at(kernel, self.mul_right_successor, &[a, zero])?; // a * 0 + a
        let vanish = self.at(kernel, self.mul_right_zero, &[a])?;
        let collapse = self.add_left(kernel, vanish, a)?; // 0 + a
        let unit = self.at(kernel, self.add_zero, &[a])?; // a
        let theorem = self.chain(kernel, &[expand, collapse, unit])?;
        quantify(kernel, theorem, &[a])
    }

    /// `∀a b. a * b = b * a`, by induction on `a`.
    fn prove_mul_commutative(
        &self,
        kernel: &mut Kernel,
        names: &mut NaturalNameSupply,
    ) -> Result<Law, NaturalError> {
        let a = names.variable(kernel, self.signature.ty)?;
        let b = names.variable(kernel, self.signature.ty)?;
        let left = self.product(kernel, a, b)?;
        let right = self.product(kernel, b, a)?;
        let body = self.equation(kernel, left, right)?;
        self.by_induction(
            kernel,
            names,
            a,
            body,
            &[a, b],
            |kernel| {
                let vanish = self.at(kernel, self.mul_zero, &[b])?; // 0
                let target = self.at(kernel, self.mul_right_zero, &[b])?;
                let target = self.symm(kernel, target)?; // b * 0
                self.chain(kernel, &[vanish, target])
            },
            |kernel, hypothesis| {
                let expand = self.at(kernel, self.mul_successor, &[a, b])?; // a * b + b
                let rewritten = self.add_left(kernel, hypothesis, b)?; // b * a + b
                let target = self.at(kernel, self.mul_right_successor, &[b, a])?;
                let target = self.symm(kernel, target)?; // b * succ a
                self.chain(kernel, &[expand, rewritten, target])
            },
        )
    }

    /// `∀a b c. (a + b) * c = a * c + b * c`, by induction on `a`.
    fn prove_mul_right_distributive(
        &self,
        kernel: &mut Kernel,
        names: &mut NaturalNameSupply,
    ) -> Result<Law, NaturalError> {
        let [a, b, c] = self.triple(kernel, names)?;
        let sum_ab = self.sum(kernel, a, b)?;
        let left_share = self.product(kernel, a, c)?;
        let right_share = self.product(kernel, b, c)?;
        let left = self.product(kernel, sum_ab, c)?;
        let right = self.sum(kernel, left_share, right_share)?;
        let body = self.equation(kernel, left, right)?;
        self.by_induction(
            kernel,
            names,
            a,
            body,
            &[a, b, c],
            |kernel| {
                let unit = self.at(kernel, self.add_zero, &[b])?;
                let folded = self.mul_left(kernel, unit, c)?; // b * c
                let vanish = self.at(kernel, self.mul_zero, &[c])?;
                let summand = self.add_left(kernel, vanish, right_share)?; // 0 + b * c
                let target = self.at(kernel, self.add_zero, &[right_share])?; // b * c
                let target = self.chain(kernel, &[summand, target])?;
                let target = self.symm(kernel, target)?;
                self.chain(kernel, &[folded, target])
            },
            |kernel, hypothesis| {
                let successor = self.at(kernel, self.add_successor, &[a, b])?;
                let folded = self.mul_left(kernel, successor, c)?; // succ (a + b) * c
                let expand = self.at(kernel, self.mul_successor, &[sum_ab, c])?; // (a + b) * c + c
                let rewritten = self.add_left(kernel, hypothesis, c)?; // (a * c + b * c) + c
                let swap = self.at(kernel, self.add_exchange, &[left_share, right_share, c])?;
                let target = self.at(kernel, self.mul_successor, &[a, c])?;
                let target = self.add_left(kernel, target, right_share)?; // succ a * c + b * c
                let target = self.symm(kernel, target)?;
                self.chain(kernel, &[folded, expand, rewritten, swap, target])
            },
        )
    }

    /// `∀a b c. a * (b + c) = a * b + a * c`.
    fn prove_mul_left_distributive(
        &self,
        kernel: &mut Kernel,
        names: &mut NaturalNameSupply,
    ) -> Result<Law, NaturalError> {
        let [a, b, c] = self.triple(kernel, names)?;
        let sum_bc = self.sum(kernel, b, c)?;
        let first_term = self.product(kernel, a, b)?;
        let second_term = self.product(kernel, c, a)?;
        let swap = self.at(kernel, self.mul_commutative, &[a, sum_bc])?; // (b + c) * a
        let split = self.at(kernel, self.mul_right_distributive, &[b, c, a])?; // b * a + c * a
        let first = self.at(kernel, self.mul_commutative, &[b, a])?;
        let first = self.add_left(kernel, first, second_term)?; // a * b + c * a
        let second = self.at(kernel, self.mul_commutative, &[c, a])?;
        let second = self.add_right(kernel, first_term, second)?; // a * b + a * c
        let theorem = self.chain(kernel, &[swap, split, first, second])?;
        quantify(kernel, theorem, &[a, b, c])
    }

    /// `∀a b c. (a * b) * c = a * (b * c)`, by induction on `a`.
    fn prove_mul_associative(
        &self,
        kernel: &mut Kernel,
        names: &mut NaturalNameSupply,
    ) -> Result<Law, NaturalError> {
        let [a, b, c] = self.triple(kernel, names)?;
        let inner_left = self.product(kernel, a, b)?;
        let inner_right = self.product(kernel, b, c)?;
        let left = self.product(kernel, inner_left, c)?;
        let right = self.product(kernel, a, inner_right)?;
        let body = self.equation(kernel, left, right)?;
        self.by_induction(
            kernel,
            names,
            a,
            body,
            &[a, b, c],
            |kernel| {
                let inner = self.at(kernel, self.mul_zero, &[b])?;
                let folded = self.mul_left(kernel, inner, c)?; // 0 * c
                let vanish = self.at(kernel, self.mul_zero, &[c])?; // 0
                let target = self.at(kernel, self.mul_zero, &[inner_right])?;
                let target = self.symm(kernel, target)?; // 0 * (b * c)
                self.chain(kernel, &[folded, vanish, target])
            },
            |kernel, hypothesis| {
                let successor = self.at(kernel, self.mul_successor, &[a, b])?;
                let folded = self.mul_left(kernel, successor, c)?; // (a * b + b) * c
                let split = self.at(kernel, self.mul_right_distributive, &[inner_left, b, c])?; // (a * b) * c + b * c
                let rewritten = self.add_left(kernel, hypothesis, inner_right)?; // a * (b * c) + b * c
                let target = self.at(kernel, self.mul_successor, &[a, inner_right])?;
                let target = self.symm(kernel, target)?; // succ a * (b * c)
                self.chain(kernel, &[folded, split, rewritten, target])
            },
        )
    }

    /// Allocates three fresh natural-number variables.
    fn triple(
        &self,
        kernel: &mut Kernel,
        names: &mut NaturalNameSupply,
    ) -> Result<[Ref; 3], NaturalError> {
        let first = names.variable(kernel, self.signature.ty)?;
        let second = names.variable(kernel, self.signature.ty)?;
        let third = names.variable(kernel, self.signature.ty)?;
        Ok([first, second, third])
    }
}
