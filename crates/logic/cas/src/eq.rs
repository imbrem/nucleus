//! Propositions about blob expressions, and the decision procedure for them.
//!
//! [`BlobEq`] is the one proposition today, and it is *valid* when its two
//! sides denote the same thing in every model — a model being a total,
//! injective `σ : O256 -> Bytes` extending the CAS.
//!
//! The crate docs define a model, give the weak (Kleene) reading of "the same
//! thing", and state the standing collision-freedom hypothesis that all of this
//! rests on, under "Standing assumption: the CAS is collision-free". It is
//! stated there once; no rule below repeats it and no rule's name carries it.
//!
//! Three consequences are load-bearing and easy to get wrong:
//!
//! - Two expressions undefined in every model are equal, because validity
//!   compares two `Option`s. Undefinedness comes only from an out-of-range
//!   slice and from a `Cat` with an undefined side — never from a digest —
//!   and it propagates outward, so a rule may never refute merely because one
//!   side failed to evaluate.
//! - Distinct digests are refutable, and this is what interpreting in a model
//!   buys. `σ` is injective, so `h1 != h2` gives `σ h1 != σ h2` in every model:
//!   the two sides differ everywhere rather than merely somewhere, which is
//!   what refuting validity asks for. [`BlobProp::decide`] answers `Some(false)`
//!   for that pair. Equal digests go to REFL, and nothing weaker than a bare
//!   digest on both sides is refutable this way: `Slice(Blake3 h1, s)` and
//!   `Slice(Blake3 h2, s)` may well agree, injectivity notwithstanding.
//! - Length disagreement is a sound refutation, but only because
//!   [`BlobExpr::len`] certifies definedness: `Some(n)` says the expression is
//!   defined in every model and is `n` bytes long in every one of them.
//!
//! Every `Some(false)` this module produces is in fact the stronger claim —
//! the sides differ in every model, not merely in one — which is what a future
//! n-ary distinctness proposition will want to consume.
//!
//! Congruence gives equality and never disequality: `Cat("ab", "c")` and
//! `Cat("a", "bc")` are equal with unequal operands, so no rule here concludes
//! `false` from mismatched structure.
//!
//! # The calculus
//!
//! [`BlobFact`] is the LCF boundary above the proposition. Its single field is
//! private and only the rules in this module fill it, so holding one *is*
//! holding a proof. The rules are
//!
//! - EVALUATION, [`BlobFact::check`], which turns a proposition the decision
//!   procedure settles affirmatively into a fact;
//! - REFL, SYMM and TRANS — [`BlobFact::refl`], [`BlobFact::symm`],
//!   [`BlobFact::trans`];
//! - CONGRUENCE, [`BlobFact::cat`] and [`BlobFact::slice`], one per operator.
//!
//! Every one of them is total except [`BlobFact::check`], which declines
//! wherever answering would be a guess, and [`BlobFact::trans`], which declines
//! when the middle terms are different expressions.
//!
//! The congruence rules build a bigger expression and are total in doing so;
//! what happens past [`MAX_TREE_NODES`](crate::MAX_TREE_NODES) is that
//! [`BlobProp::decide`] stops answering questions about the conclusion, never
//! that the conclusion stops following. [`BlobFact::erase`] re-types a fact
//! without touching its claim.
//!
//! Nothing else can introduce a fact within this layer. The one introduction
//! form from *outside* it is the bridge,
//! [`CasRangeFact::to_blob_fact`](crate::CasRangeFact::to_blob_fact), which is
//! an ordinary rule: a model extends the CAS by definition, so a checked pair
//! makes its equality valid with no assumption beyond the standing one.
//! Reading a fact back out through [`BlobFact::to_range_fact`] is ordinary
//! too.
//!
//! Cancellation and n-ary distinctness are deferred. Each has a `DEFERRED:`
//! comment below the rules saying what it would look like and why it is sound.
//!
//! Lean: `Nucleus.BlobEq` (the structure) and `Nucleus.BlobEq.Valid` (the
//! proposition).

use std::{cmp::Ordering, fmt::Debug};

use crate::{
    BlobCat, BlobExpr, BlobLike, BlobRange, BlobSlice, BlobSpan, Bytes, CasRangeAssertion,
    CasRangeFact, MAX_TREE_NODES, O256, cmp_length,
};

mod sealed {
    pub trait BlobProp {}

    impl<L: crate::BlobLike, R: crate::BlobLike> BlobProp for super::BlobEq<L, R> {}
}

/// A proposition about [`BlobLike`]s.
///
/// Sealed for soundness, and this is the sharpest sealing argument in the
/// crate: the LCF introduction rule turns `Some(true)` into a checked fact, so
/// an outside implementor returning `Some(true)` unconditionally would forge
/// every fact in the crate.
///
/// Lean: no counterpart by design. The trait exists so that one LCF wrapper can
/// serve several propositions in a language where that has to be a type; Lean
/// quantifies over `Prop` directly, so each implementor is simply one Lean
/// predicate (`Nucleus.BlobEq.Valid` today, `Nucleus.BlobDistinct.Valid` later)
/// and the abstraction itself has nothing left to state.
///
/// ```compile_fail
/// use covalence_logic_cas::BlobProp;
///
/// #[derive(Clone, Debug)]
/// struct Forged;
///
/// impl BlobProp for Forged {
///     fn decide(&self) -> Option<bool> {
///         Some(true)
///     }
/// }
/// ```
pub trait BlobProp: sealed::BlobProp + Clone + Debug {
    /// Decides this proposition, when the rules settle it.
    ///
    /// `Some(true)` means valid — it holds in every model. `Some(false)` means
    /// refuted, and every branch that answers it here refutes in the strong
    /// way, by making the two sides differ in every model rather than in one.
    /// `None` means the rules do not settle it.
    ///
    /// It never guesses, because `None` is always available and always sound.
    ///
    /// Lean: `Nucleus.BlobEq.decide?`, proved both ways by
    /// `Nucleus.BlobEq.valid_of_decide?_true` and
    /// `Nucleus.BlobEq.not_valid_of_decide?_false` — the two halves of "never
    /// guesses". The digest branch is `not_valid_of_decide?_false`'s only
    /// interesting case, and it is two lines from the model's injectivity field
    /// (`Nucleus.BlobExpr.denote_blake3_ne`) rather than a separating-model
    /// construction.
    #[must_use]
    fn decide(&self) -> Option<bool>;
}

/// The proposition that two values denote the same byte string in every model.
///
/// Public fields: an unchecked claim, like
/// [`CasRangeAssertion`](crate::CasRangeAssertion). The LCF boundary is the
/// checked fact that will wrap a decided proposition, not this.
///
/// The two operand types are a Rust-only convenience. They keep a carrier such
/// as [`O256`](crate::O256) or [`Bytes`](crate::Bytes) from having to be
/// reified into a [`BlobExpr`](crate::BlobExpr) before a claim can be made
/// about it, and they let the congruence rules state their result type.
///
/// Lean has one type, so `Nucleus.BlobEq` has no parameters.
///
/// Lean: `Nucleus.BlobEq` (the structure) and `Nucleus.BlobEq.Valid` (the
/// proposition), mirroring `CasAssertion` / `CasAssertion.Valid`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BlobEq<L, R> {
    /// The left-hand value.
    pub lhs: L,
    /// The right-hand value.
    pub rhs: R,
}

impl<L: BlobLike, R: BlobLike> BlobEq<L, R> {
    /// Claims that `lhs` and `rhs` denote the same byte string. Unchecked.
    ///
    /// Lean: `Nucleus.BlobEq.mk`.
    #[must_use]
    pub const fn new(lhs: L, rhs: R) -> Self {
        Self { lhs, rhs }
    }
}

impl<L: BlobLike, R: BlobLike> BlobProp for BlobEq<L, R> {
    /// Decides this equality by reflexivity, by digest, by length, or by
    /// evaluation, in that order.
    ///
    /// | Case | Answer |
    /// | ---- | ------ |
    /// | either side passes [`MAX_TREE_NODES`](crate::MAX_TREE_NODES) | `None` |
    /// | the two sides are the same expression | `Some(true)` |
    /// | `Blake3(h1)` against `Blake3(h2)`, `h1 != h2` | `Some(false)` |
    /// | both lengths known and different | `Some(false)` |
    /// | both sides evaluate | `Some(l == r)` |
    /// | anything else | `None` |
    ///
    /// There is deliberately no structural-mismatch branch — see the module
    /// docs for the `Cat` trap — and the digest branch fires only on two bare
    /// digests, never on slices or concatenations of them.
    fn decide(&self) -> Option<bool> {
        // SIZE. First, ahead even of REFL, because REFL is the expensive
        // branch: `==` walks both trees, which is exponential in a shared
        // DAG's depth and declines at no point.
        //
        // Declining is sound for every proposition in this calculus, so an
        // expression too large to walk is simply not decided. That costs
        // completeness alone: REFL as a rule is still total, and
        // `BlobFact::refl` still mints the fact this branch will no longer
        // confirm.
        if self.lhs.size() > MAX_TREE_NODES || self.rhs.size() > MAX_TREE_NODES {
            return None;
        }
        let (lhs, rhs) = (self.lhs.to_expr(), self.rhs.to_expr());
        // REFL. An expression denotes what it denotes, in every model, even
        // when its length and bytes are both unknown.
        if lhs == rhs {
            return Some(true);
        }
        // DIGEST. A model is injective, so `h1 != h2` gives `σ h1 != σ h2` in
        // every model: the two sides differ everywhere rather than merely
        // somewhere, which is exactly what refuting validity needs. No model
        // construction is involved, and neither side has to be resolvable —
        // this is the one refutation that survives a digest.
        //
        // Written to answer `left == right` rather than a bare `false`, so
        // that it stays correct if it is ever reordered above REFL. Reaching
        // it with equal hashes is impossible today.
        //
        // The pattern matches the algorithm as well as the hash. A future
        // `Sha256` variant would be a second namespace with its own `σ`,
        // saying nothing about this one, so a cross-algorithm pair must go on
        // falling through to the branches below, which cannot settle it.
        //
        // A `Sha256`/`Sha256` pair falls through too until someone writes its
        // arm. That is incompleteness, never unsoundness, which is why this
        // one place may fall through rather than matching every variant.
        if let (BlobExpr::Blake3(left), BlobExpr::Blake3(right)) = (&lhs, &rhs) {
            return Some(left == right);
        }
        // LENGTH. Sound because `Some` certifies definedness: both sides are
        // defined in every model, and no byte string has two lengths. Cheap,
        // so it runs before evaluation. `cmp_length` rather than `==` so that
        // two unknown lengths never look alike.
        if matches!(
            cmp_length(&lhs, &rhs),
            Some(Ordering::Less | Ordering::Greater)
        ) {
            return Some(false);
        }
        // EVALUATION. `eval = Some v` pins the denotation to `v` in every
        // model, so this settles the question in both directions.
        Some(lhs.eval()? == rhs.eval()?)
    }
}

/// A checked proposition about blob expressions: the LCF wrapper.
///
/// The private field is the trust boundary. Safe code can read, clone and
/// compare a fact, but only the rules below can build one, so a `BlobFact` in
/// hand is a proof that its proposition holds. Those rules are
///
/// - [`Self::check`], EVALUATION, the only introduction form that inspects
///   anything;
/// - [`Self::refl`], [`Self::symm`] and [`Self::trans`], the equivalence rules;
/// - [`Self::cat`] and [`Self::slice`], congruence for the two operators.
///
/// [`Self::erase`] re-types a fact without changing its claim.
///
/// The wrapper is generic in the *proposition* rather than in a pair of
/// operands. That is what lets the deferred `BlobDistinct` inherit
/// [`Self::check`] with no new introduction rule and no new soundness argument.
///
/// # Naming
///
/// The obvious name for this wrapper would be `CasFact<P: BlobProp>`, but
/// [`CasFact`](crate::CasFact) already names a fact of a different shape: a
/// hash, a range and the bytes filling it, where this is a proposition about
/// two expressions of which only some have that shape.
///
/// The two say the same thing where they overlap — see [`Self::to_range_fact`]
/// and [`CasRangeFact::to_blob_fact`](crate::CasRangeFact::to_blob_fact) — but
/// repointing the name would leave every existing consumer holding a value
/// with different fields. See the crate docs.
///
/// Lean: `Nucleus.BlobEqFact`, which specialises the wrapper to equality,
/// carrying a `BlobEq.Valid` proof where this carries a private field. It is
/// also indexed by the store it was checked against, which this is not.
///
/// ```compile_fail
/// use covalence_logic_cas::{BlobEq, BlobExpr, BlobFact, Bytes};
///
/// let prop = BlobEq::new(BlobExpr::Bytes(Bytes::new()), BlobExpr::Zero(9));
/// let forged = BlobFact(prop);
/// ```
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BlobFact<P: BlobProp>(P);

impl<P: BlobProp> BlobFact<P> {
    /// Introduces a fact. Every caller is a checking rule of this crate.
    ///
    /// Lean: `Nucleus.BlobEqFact.mk`, whose second field is the `Valid` proof
    /// this erases.
    pub(crate) const fn trust(prop: P) -> Self {
        Self(prop)
    }

    /// Borrows the proposition this fact establishes.
    ///
    /// Lean: `Nucleus.BlobEqFact.prop`.
    #[must_use]
    pub const fn prop(&self) -> &P {
        &self.0
    }

    /// RULE: EVALUATION. Checks a proposition, and introduces a fact when the
    /// decision procedure proves it.
    ///
    /// Sound because [`BlobProp::decide`] never guesses: `Some(true)` means
    /// provable, so it *is* the proof.
    ///
    /// This declines in both of the other two cases, and they are not the same
    /// thing. `None` is "the rules do not settle it", and every reason for it
    /// is listed on [`BlobProp::decide`]. `Some(false)` is a refutation, which
    /// this crate has no fact type for.
    ///
    /// That includes the digest branch, decided rather than deferred yet still
    /// minting nothing: a refutation is not a `BlobFact` of anything until a
    /// distinctness proposition exists to carry it.
    ///
    /// Generic over every present and future [`BlobProp`], which is the whole
    /// reason `decide` lives on the proposition rather than being baked into an
    /// equality-specific rule.
    ///
    /// Lean: `Nucleus.BlobEqFact.check?`, resting on
    /// `Nucleus.BlobEq.valid_of_decide?_true`. It is specialised to equality
    /// there, since Lean has no `BlobProp` class to be generic over.
    ///
    /// ```
    /// use covalence_logic_cas::{BlobEq, BlobExpr, BlobFact, Bytes};
    ///
    /// let bytes = |value| BlobExpr::Bytes(Bytes::from_static(value));
    /// let proved = BlobEq::new(BlobExpr::cat(bytes(b"ab"), bytes(b"c")), bytes(b"abc"));
    /// assert!(BlobFact::check(proved).is_some());
    ///
    /// // Refuted, so there is no fact to introduce.
    /// assert!(BlobFact::check(BlobEq::new(bytes(b"abc"), bytes(b"abd"))).is_none());
    /// ```
    #[must_use]
    pub fn check(prop: P) -> Option<Self> {
        match prop.decide() {
            Some(true) => Some(Self(prop)),
            // `Some(false)` refutes and `None` is unknown; neither is a fact.
            Some(false) | None => None,
        }
    }
}

impl<B: BlobLike> BlobFact<BlobEq<B, B>> {
    /// RULE: REFL. Total.
    ///
    /// Sound with no side condition whatsoever: in each model an expression
    /// denotes what it denotes.
    ///
    /// It needs no evaluation, no length and no definedness, so it holds for a
    /// digest this crate cannot resolve, for an out-of-range slice and for a
    /// concatenation too long to measure — none of which has a length or bytes
    /// here, and the middle one of which is undefined in every model. Only the
    /// weak reading of validity makes that middle case work; see the crate
    /// docs.
    ///
    /// Lean: `Nucleus.BlobEq.valid_refl`.
    #[must_use]
    pub fn refl(blob: B) -> Self {
        Self::trust(BlobEq::new(blob.clone(), blob))
    }
}

impl<L: BlobLike, R: BlobLike> BlobFact<BlobEq<L, R>> {
    /// RULE: SYMM. Total.
    ///
    /// Sound because equality of denotations is symmetric in each model.
    ///
    /// Lean: `Nucleus.BlobEq.valid_symm`.
    #[must_use]
    pub fn symm(&self) -> BlobFact<BlobEq<R, L>> {
        BlobFact::trust(BlobEq::new(self.0.rhs.clone(), self.0.lhs.clone()))
    }

    /// RULE: TRANS. Composes two facts sharing a middle expression.
    ///
    /// Sound unconditionally: equality of denotations is transitive in each
    /// model, needing no definedness — two undefined middles compose as
    /// happily as two defined ones.
    ///
    /// `None` when the middle terms are different expressions. This check is
    /// the whole of the side condition, and the types supply none of it: `M` is
    /// unconstrained by `R`, so without the check `a = b` and `c = d` would
    /// compose into `a = d` for any `b` and `c` whatsoever.
    ///
    /// The comparison is on the reified expressions rather than on the
    /// carriers, so the two spellings of a whole-blob claim do compose:
    /// `BlobExpr::slice` normalises `0..` away, so a `BlobSlice<O256,
    /// RangeFull>` middle meets an [`O256`](crate::O256) one.
    ///
    /// Lean: `Nucleus.BlobEq.valid_trans`, whose `shared` hypothesis is exactly
    /// this equality of middle terms.
    #[must_use]
    pub fn trans<M: BlobLike, T: BlobLike>(
        &self,
        next: &BlobFact<BlobEq<M, T>>,
    ) -> Option<BlobFact<BlobEq<L, T>>> {
        if self.0.rhs.to_expr() == next.0.lhs.to_expr() {
            Some(BlobFact::trust(BlobEq::new(
                self.0.lhs.clone(),
                next.0.rhs.clone(),
            )))
        } else {
            None
        }
    }

    /// RULE: CONGRUENCE, for concatenation.
    ///
    /// Sound because in each model the denotation of `Cat(a, b)` depends on
    /// `a` and `b` only through what they denote there, so equal parts give
    /// equal wholes — including when a part is undefined, which makes both
    /// wholes undefined together.
    ///
    /// This gives equality only. There is no converse arm and none may be
    /// added: `Cat("ab", "c")` and `Cat("a", "bc")` are equal with unequal
    /// operands, so unequal parts say nothing about the wholes. The sound
    /// partial converse is cancellation, which needs a length precondition and
    /// is deferred; see the `DEFERRED:` comment below the rules.
    ///
    /// Total. Building a conclusion past
    /// [`MAX_TREE_NODES`](crate::MAX_TREE_NODES) is allowed — the conclusion
    /// follows whatever its size — and the consequence is only that
    /// [`BlobProp::decide`] will decline to say anything about it.
    ///
    /// Lean: `Nucleus.BlobEq.valid_cat`, total there too, and with the same
    /// absence of a converse pinned by `Nucleus.exists_valid_cat_of_operands_ne`.
    #[must_use]
    pub fn cat<L2: BlobLike, R2: BlobLike>(
        &self,
        tail: &BlobFact<BlobEq<L2, R2>>,
    ) -> BlobFact<BlobEq<BlobCat<L, L2>, BlobCat<R, R2>>> {
        BlobFact::trust(BlobEq::new(
            BlobCat::new(self.0.lhs.clone(), tail.0.lhs.clone()),
            BlobCat::new(self.0.rhs.clone(), tail.0.rhs.clone()),
        ))
    }

    /// RULE: CONGRUENCE, for slicing.
    ///
    /// Sound because slicing is a function of the byte string and the span:
    /// in each model equal subjects give equal results, and a span out of
    /// range on one side is out of range on the other, so both sides are
    /// undefined together.
    ///
    /// Taking one span, rather than one per side, is what makes the unsound
    /// shape unrepresentable: `Slice(a, s) = Slice(b, t)` does not follow from
    /// `a = b` for `s ≠ t`. As with [`Self::cat`], this yields equality only.
    ///
    /// Total, for the reason given on [`Self::cat`].
    ///
    /// Lean: `Nucleus.BlobEq.valid_slice`, total there too, and taking one
    /// span for both sides for the same reason.
    #[must_use]
    pub fn slice<S: BlobRange>(
        &self,
        span: S,
    ) -> BlobFact<BlobEq<BlobSlice<L, S>, BlobSlice<R, S>>> {
        BlobFact::trust(BlobEq::new(
            BlobSlice::new(self.0.lhs.clone(), span.clone()),
            BlobSlice::new(self.0.rhs.clone(), span),
        ))
    }

    /// Reifies both sides, keeping the claim.
    ///
    /// Total, and sound because [`BlobLike::to_expr`] is denotation-preserving
    /// by definition: it is the coercion the whole trait is defined in terms of.
    /// Use it to hold facts of different carrier types together, the way
    /// [`CasRangeFact::erase`](crate::CasRangeFact::erase) is used for range
    /// shapes.
    ///
    /// Lean: no counterpart by design. Erasure is re-typing and nothing else,
    /// needed because a carrier is a static type here; Lean has the single type
    /// `Nucleus.BlobExpr`, so every Lean fact is already in the erased form and
    /// there is no step to state.
    #[must_use]
    pub fn erase(&self) -> BlobFact<BlobEq<BlobExpr, BlobExpr>> {
        BlobFact::trust(BlobEq::new(self.0.lhs.to_expr(), self.0.rhs.to_expr()))
    }
}

// DEFERRED: CANCELLATION. One impl block over
// `BlobFact<BlobEq<BlobCat<A, B>, BlobCat<C, D>>>`, the only other caller of
// `cmp_length`, offering `cancel_tails` and `cancel_heads`. It adds no trait
// method, no variant, and touches none of the rules above, and it is not
// `cat` run backwards: nothing in it concludes disequality.
//
// Lean already proves it, as `Nucleus.BlobEq.valid_cancel_of_cmpLength?_heads`
// and `_tails` with `valid_cancel_same_head` and `_tail` as corollaries, so the
// rule is safe to add. The precondition, the definedness side condition and the
// digest case it does not yet reach are set out in issue #1135.
//
// Route (iii) is an equality fact as the premise, in place of syntactic
// sharing. It stays unsound, for the same reason route (ii) needs definedness:
// `BlobEq a c` is satisfied by two expressions undefined in every model, and
// then `Cat(a, b) = Cat(c, d)` holds for arbitrary `b != d`.
//
// DEFERRED: N-ARY DISTINCTNESS. The binary case is not deferred:
// `BlobEq(Blake3 h1, Blake3 h2)` with `h1 != h2` is refuted by `decide` above,
// because a model is injective. What is left is the n-ary proposition
//
//   BlobDistinct [e1, ..., en]  :=  pairwise different in every model
//
// as a second `BlobProp`, which inherits the generic introduction rule for
// free and can decide a list of digests in one sorted pass rather than n²
// calls to `decide`.
//
// Two things to carry over when it lands.
//
// - It must consume the strong refutation — differing in every model, which is
//   what every `Some(false)` above establishes — since "not valid" alone does
//   not compose pairwise.
// - It must match the same algorithm on both sides. `Blake3(h)` and a future
//   `Sha256(h)` carrying identical bytes are interpreted by different maps and
//   say nothing about each other, so the rule is "same namespace, different
//   digest implies different blob", with unknown as the fail-safe default.
//
// The bridge between the two layers is below. Both directions are ordinary
// rules, carrying no hypothesis of their own: a model extends the CAS by
// definition, so a checked pair makes its equality valid, and conversely an
// equality about `Blake3(h)` can only be valid when the CAS pins `h`, an
// unpinned hash being free to read differently in some other model.
//
// They are still asymmetric in one way that has nothing to do with trust:
// going up is total, and coming back down is partial in the shapes it can
// express.

impl<R: BlobRange> CasRangeFact<R> {
    /// Reads this fact as a blob-expression equality.
    ///
    /// A whole-blob [`CasFact`](crate::CasFact) comes out as
    /// `Blake3(h) = Bytes(b)` once erased, because
    /// [`BlobExpr::slice`](crate::BlobExpr::slice) normalises the whole-blob
    /// span away; a fact about `3..9` comes out as
    /// `Slice(Blake3(h), 3..9) = Bytes(b)`. [`BlobFact::to_range_fact`] reads
    /// either shape back.
    ///
    /// # Trust
    ///
    /// Ordinary, and total. It carries no hypothesis of its own: a model *is*
    /// a map extending the CAS, so `σ h = b` holds by definition for a checked
    /// pair `(h, b)`, and for a sub-range fact the same definition pins `σ h`
    /// on that range.
    ///
    /// Collision-freedom is not this rule's concern. It is the standing
    /// assumption of the whole calculus, stated once in the crate docs, and
    /// `refl` is just as vacuous without it as this is.
    ///
    /// Lean: `Nucleus.BlobEq.valid_ofCasRange_of_mem`, whose hypotheses are
    /// that the pair is in the store and that slicing its blob yields these
    /// bytes — nothing about the naming function beyond the check the pair
    /// already carries. `Nucleus.BlobEq.valid_ofCasRange` is the *unstored*
    /// variant, and it is the one that has to assume the section property.
    ///
    /// ```
    /// use covalence_logic_cas::{BlobExpr, Bytes, CasFact};
    ///
    /// let blob = Bytes::from_static(b"0123456789");
    /// let fact = CasFact::from_bytes(blob.clone());
    /// let equality = fact.to_blob_fact().erase();
    ///
    /// assert_eq!(equality.prop().lhs, BlobExpr::Blake3(fact.hash()));
    /// assert_eq!(equality.prop().rhs, BlobExpr::Bytes(blob));
    /// ```
    #[must_use]
    pub fn to_blob_fact(&self) -> BlobFact<BlobEq<BlobSlice<O256, R>, Bytes>> {
        BlobFact::trust(BlobEq::new(
            // A digest is a leaf, so this is two nodes: far under the limit
            // past which `BlobProp::decide` would decline to read it back.
            BlobSlice::new(self.hash(), self.range().clone()),
            self.bytes().clone(),
        ))
    }
}

impl BlobFact<BlobEq<BlobExpr, BlobExpr>> {
    /// Recovers a range fact from an equality that has a range fact's shape.
    ///
    /// Ordinary, exactly like [`CasRangeFact::to_blob_fact`] going the other
    /// way. A `BlobFact` is a proof that its equality holds in every model, and
    /// a *contentful* equality about `Blake3(h)` can only hold in every model
    /// when the CAS pins `h` there: an unpinned hash is free, so some other
    /// model reads different bytes at it and refutes the claim.
    ///
    /// So the premise already says what a [`CasRangeFact`] asserts, and this
    /// rule only rearranges it into the other layer's shape.
    ///
    /// "Contentful" excludes exactly one family, and the exclusion is real
    /// rather than bookkeeping: the empty closed window,
    /// `Slice(Blake3(h), k..k) = Bytes("")`. Every byte string selects nothing
    /// on `[k, k)`, so at `k = 0` that equality holds in every model of every
    /// store while naming nothing at all. Every other shape is contentful —
    /// every open span, every window of nonzero width, every backwards or
    /// mis-widthed one — so nothing this crate reasons about is excluded.
    ///
    /// This rule does not test for that shape, and nothing mints such a premise
    /// for an address the crate does not already hold a fact about.
    /// [`BlobProp::decide`](crate::BlobProp::decide) cannot settle a slice of a
    /// digest, which has neither a known length nor an evaluation, and the only
    /// other route to the shape is [`CasRangeFact::to_blob_fact`], whose subject
    /// is pinned by the very fact it came from — the case
    /// `Nucleus.CasRange.of_valid_of_pins` covers with no side condition. Making
    /// that a check rather than a property of what is derivable, by refusing an
    /// empty closed span against empty bytes, is a follow-up.
    ///
    /// Partial for three separate reasons, none of which is a guess:
    ///
    /// - the erased span need not fit `R`, the same partiality
    ///   [`CasRangeFact::fuse`] already handles — a closed span is no
    ///   `RangeFrom`, and a nonzero start is no `RangeTo`;
    /// - the left side must be a digest or a slice of one, and the right side
    ///   literal bytes. A nested slice, a concatenation, a run of zeros or a
    ///   non-literal right-hand side falls through to `None` rather than a
    ///   guessed fact. Use [`BlobFact::symm`] first for the mirrored shape;
    /// - a closed span must agree with the bytes' width.
    ///
    /// That last check is redundant under [`BlobEq`] today: a closed slice of
    /// the wrong width is either undefined or of a different length in every
    /// model, while the literal bytes are always defined, so no such equality
    /// is valid in the first place.
    ///
    /// It is kept because [`CasRangeFact::extent`] assumes the agreement and
    /// this is trusted code minting a fact of the other layer. It also rejects
    /// a backwards span, which reaches here through [`BlobRange::span`]'s
    /// bypass of `BlobSpan::new`.
    ///
    /// Lean: `Nucleus.CasRange.of_valid_of_contentful`, which is this rule: a
    /// valid equality of range-fact shape over a contentful span yields
    /// `Nucleus.CasRange.Valid`, with no section property and no injectivity.
    /// The step it takes is the one this rule's argument takes,
    /// `Nucleus.Cas.pins_of_valid_blake3` — an unpinned address is free, so
    /// redirecting it to a byte string long enough to be fresh refutes the
    /// equality. `Nucleus.CasRange.of_valid_of_pins` is the variant that takes
    /// the pin rather than deriving it, and `Nucleus.CasRange.Contentful` is the
    /// side condition, discharged by `contentful_of_open` for any open span and
    /// by `contentful_of_ne_empty` for any nonempty bytes.
    ///
    /// The side condition is not slack. `Nucleus.BlobEq.valid_emptyWindow`
    /// proves the empty closed window valid at every address of every store, and
    /// `Nucleus.exists_valid_not_casRange` exhibits a store that has a model,
    /// where the equality holds, the address is unpinned, and the range claim is
    /// false — so a hypothesis-free reading of this rule is refutable, not
    /// merely unproved.
    ///
    /// `Nucleus.CasRange.of_valid` reaches the same conclusion for any span at
    /// all, but only through a model that is a section
    /// (`Nucleus.Model.IsSection`), which this crate does not assume.
    ///
    /// ```
    /// use std::ops::{RangeFrom, RangeFull};
    ///
    /// use covalence_logic_cas::{Bytes, CasFact};
    ///
    /// let fact = CasFact::from_bytes(Bytes::from_static(b"0123456789"));
    /// let equality = fact.to_blob_fact().erase();
    ///
    /// assert_eq!(equality.to_range_fact::<RangeFull>(), Some(fact.clone()));
    /// // A whole-blob span is no closed range, and vice versa.
    /// assert_eq!(
    ///     fact.slice(3..9).unwrap().to_blob_fact().erase()
    ///         .to_range_fact::<RangeFrom<u64>>(),
    ///     None
    /// );
    /// ```
    #[must_use]
    pub fn to_range_fact<R: BlobRange>(&self) -> Option<CasRangeFact<R>> {
        let BlobExpr::Bytes(bytes) = &self.0.rhs else {
            return None;
        };
        // The subject is either a slice of a digest or, for the whole blob,
        // the digest itself: `BlobExpr::slice` normalises the whole-blob span
        // away, so both spellings must be read here. Every arm is written out
        // so that a second digest variant breaks the build rather than falling
        // into a catch-all that would mint a BLAKE3-addressed fact from it.
        let (hash, span) = match &self.0.lhs {
            BlobExpr::Blake3(hash) => (*hash, BlobSpan::WHOLE),
            BlobExpr::Slice(slice) => match &**slice.blob() {
                BlobExpr::Blake3(hash) => (*hash, *slice.span()),
                BlobExpr::Slice(_) | BlobExpr::Cat(_) | BlobExpr::Bytes(_) | BlobExpr::Zero(_) => {
                    return None;
                }
            },
            BlobExpr::Cat(_) | BlobExpr::Bytes(_) | BlobExpr::Zero(_) => return None,
        };
        // A closed span pins the width, and `CasRangeFact::extent` reads that
        // width off the bytes instead. `checked_sub` also turns a backwards
        // span into a refusal rather than a panic.
        let width = u64::try_from(bytes.len()).ok()?;
        if let Some(end) = span.end()
            && end.checked_sub(span.start()) != Some(width)
        {
            return None;
        }
        // An empty closed window establishes nothing about the address.
        // `Slice(Blake3(h), k..k)` equals `Bytes("")` in every model of every
        // store, because every byte string selects nothing on an empty range,
        // so the premise holds even when `h` names nothing at all. A
        // `CasRangeFact` is a naming claim, so this shape must be refused.
        //
        // Lean: `Nucleus.CasRange.Contentful` is the side condition, and
        // `Nucleus.exists_valid_not_casRange` is the counterexample to
        // dropping it. Every other shape is contentful, so this costs nothing.
        if span.end() == Some(span.start()) && bytes.is_empty() {
            return None;
        }
        let range = R::from_bounds(span.start(), span.end())?;
        Some(CasRangeFact::trust(CasRangeAssertion {
            hash,
            range,
            bytes: bytes.clone(),
        }))
    }
}

#[cfg(test)]
mod tests {
    use std::{
        ops::{Range, RangeFrom, RangeFull, RangeTo},
        sync::Arc,
    };

    use super::*;
    use crate::{CasFact, MAX_EVAL_BYTES};

    fn bytes(value: &'static [u8]) -> BlobExpr {
        BlobExpr::Bytes(Bytes::from_static(value))
    }

    fn decide(lhs: BlobExpr, rhs: BlobExpr) -> Option<bool> {
        BlobEq::new(lhs, rhs).decide()
    }

    #[test]
    fn identical_expressions_are_equal_without_evaluating() {
        // Reflexivity needs no definedness: an unreadable digest, an
        // out-of-range slice and an over-long concatenation are all equal to
        // themselves even though none of them has a length or bytes here, and
        // the middle one is undefined in every model.
        let digest = BlobExpr::Blake3(O256::from_bytes(b"blob"));
        assert_eq!(decide(digest.clone(), digest.clone()), Some(true));

        let out_of_range = BlobExpr::slice(bytes(b"ab"), 5..9);
        assert_eq!(out_of_range.len(), None);
        assert_eq!(decide(out_of_range.clone(), out_of_range), Some(true));

        let left = BlobExpr::cat(bytes(b"ab"), digest.clone());
        let right = BlobExpr::cat(bytes(b"ab"), digest);
        assert_eq!(left.len(), None);
        assert_eq!(decide(left, right), Some(true));
    }

    #[test]
    fn evaluation_settles_equality_in_both_directions() {
        assert_eq!(
            decide(BlobExpr::cat(bytes(b"ab"), bytes(b"c")), bytes(b"abc")),
            Some(true)
        );
        assert_eq!(decide(BlobExpr::Zero(2), bytes(b"\0\0")), Some(true));
        assert_eq!(decide(bytes(b"abc"), bytes(b"abd")), Some(false));
        assert_eq!(
            decide(BlobExpr::slice(bytes(b"0123456789"), 3..6), bytes(b"345")),
            Some(true)
        );
    }

    /// Congruence gives equality, never disequality. Unequal
    /// `Cat` operands with equal wholes must decide `true`, not `false`.
    #[test]
    fn congruence_never_yields_disequality() {
        assert_eq!(
            decide(
                BlobExpr::cat(bytes(b"ab"), bytes(b"c")),
                BlobExpr::cat(bytes(b"a"), bytes(b"bc"))
            ),
            Some(true)
        );
        // The same trap for `Slice`: different subjects, same bytes.
        assert_eq!(
            decide(
                BlobExpr::slice(bytes(b"xabcx"), 1..4),
                BlobExpr::slice(bytes(b"yabcy"), 1..4)
            ),
            Some(true)
        );
    }

    /// Known, differing lengths refute, and do so without
    /// materialising either side.
    #[test]
    fn known_differing_lengths_decide_false() {
        assert_eq!(decide(BlobExpr::Zero(1 << 40), bytes(b"abc")), Some(false));
        assert_eq!(decide(BlobExpr::Zero(u64::MAX), bytes(b"")), Some(false));
        assert_eq!(
            decide(
                BlobExpr::cat(BlobExpr::Zero(1 << 40), bytes(b"a")),
                BlobExpr::Zero(1 << 40)
            ),
            Some(false)
        );
    }

    /// Distinct digests refute. A model is injective, so
    /// `h1 != h2` gives `σ h1 != σ h2` in every model, and the sides differ
    /// everywhere rather than merely somewhere.
    #[test]
    fn distinct_digests_decide_false() {
        let left = BlobExpr::Blake3(O256::from_bytes(b"left"));
        let right = BlobExpr::Blake3(O256::from_bytes(b"right"));

        assert_eq!(decide(left.clone(), right.clone()), Some(false));
        assert_eq!(decide(right.clone(), left.clone()), Some(false));
        // A refutation is not a fact: there is no `BlobFact` for `!=`.
        assert_eq!(BlobFact::check(BlobEq::new(left.clone(), right)), None);

        // Equal digests go to REFL, never to `false`. This is the branch's
        // one trap, and the same claim holds through the carriers.
        assert_eq!(decide(left.clone(), left.clone()), Some(true));
        let hash = O256::from_bytes(b"left");
        assert_eq!(BlobEq::new(hash, hash).decide(), Some(true));
        assert_eq!(
            BlobEq::new(hash, O256::from_bytes(b"right")).decide(),
            Some(false)
        );

        // A digest against anything that is not a digest stays unknown: this
        // crate cannot read a store, so `σ h` may or may not be those bytes.
        assert_eq!(decide(left.clone(), bytes(b"abc")), None);
        assert_eq!(decide(left, BlobExpr::Zero(32)), None);
    }

    /// Injectivity refutes two bare digests and nothing more. `σ h1 != σ h2`
    /// says nothing about their prefixes, their suffixes or anything built
    /// from them, so every derived shape must fall through to `None`.
    #[test]
    fn only_bare_digests_are_refuted_by_injectivity() {
        let left = BlobExpr::Blake3(O256::from_bytes(b"left"));
        let right = BlobExpr::Blake3(O256::from_bytes(b"right"));

        // Two different blobs can share a prefix, so this is not refutable.
        assert_eq!(
            decide(
                BlobExpr::slice(left.clone(), 0..4),
                BlobExpr::slice(right.clone(), 0..4)
            ),
            None
        );
        // This one is false in every model — appending the same suffix cannot
        // merge two different byte strings — but no rule here sees it. That is
        // incompleteness, and the deferred cancellation rule is where
        // recovering it would go.
        assert_eq!(
            decide(
                BlobExpr::cat(left.clone(), bytes(b"a")),
                BlobExpr::cat(right, bytes(b"a"))
            ),
            None
        );
        // And a digest against a slice of itself is unknown, not false.
        assert_eq!(decide(left.clone(), BlobExpr::slice(left, 0..4)), None);
    }

    /// The bug the bounds-checked slice length exists to prevent. Both sides
    /// are undefined in every model, so under the weak reading they are equal;
    /// a `len` reporting the raw span width would answer `Some(false)` here,
    /// which is a false fact. `decide` answers `None`, which is the sound
    /// incomplete answer.
    #[test]
    fn two_out_of_range_slices_of_different_width_are_equal() {
        let wide = BlobExpr::slice(bytes(b"ab"), 5..9);
        let narrow = BlobExpr::slice(bytes(b"ab"), 5..7);

        assert_eq!(wide.len(), None);
        assert_eq!(narrow.len(), None);
        assert_eq!(decide(wide, narrow), None);
    }

    /// The blob named by `h` is not the 32 bytes of `h`. Nothing
    /// refutes it either — `σ h` could be any byte string at all, those 32
    /// included. The section property considered in the crate docs is exactly
    /// what would decide this one.
    #[test]
    fn digest_bytes_are_not_the_named_blob() {
        let hash = O256::from_bytes(b"abc");
        let digest = BlobExpr::Bytes(Bytes::copy_from_slice(hash.as_bytes()));

        assert_eq!(decide(BlobExpr::Blake3(hash), digest), None);
    }

    /// No guessing. Anything a digest is involved in is unknown
    /// unless reflexivity or the digest branch already settled it.
    #[test]
    fn decide_never_guesses_on_a_digest() {
        let hash = O256::from_bytes(b"blob");
        let digest = BlobExpr::Blake3(hash);

        assert_eq!(decide(digest.clone(), BlobExpr::Zero(32)), None);
        assert_eq!(
            decide(BlobExpr::slice(digest.clone(), 0..4), bytes(b"abcd")),
            None
        );
        assert_eq!(
            decide(
                BlobExpr::cat(digest.clone(), bytes(b"a")),
                BlobExpr::cat(digest, bytes(b"b"))
            ),
            None
        );
    }

    /// The proposition is stated over carriers, not only over reified
    /// expressions, and every carrier decides the same way its expression does.
    #[test]
    fn carriers_decide_like_their_expressions() {
        let hash = O256::from_bytes(b"blob");
        let raw = Bytes::from_static(b"0123456789");

        // A whole-blob claim normalises the span away, so the two spellings of
        // "all of the blob at `h`" are reflexively equal.
        let whole = BlobSlice::new(hash, ..);
        assert_eq!(BlobEq::new(whole, hash).decide(), Some(true));

        // A carrier claim and its reified form agree.
        let sliced = BlobSlice::new(raw.clone(), 3..6);
        assert_eq!(
            BlobEq::new(sliced, Bytes::from_static(b"345")).decide(),
            Some(true)
        );

        let joined = BlobCat::new(Bytes::from_static(b"ab"), Bytes::from_static(b"c"));
        assert_eq!(
            BlobEq::new(joined, Bytes::from_static(b"abc")).decide(),
            Some(true)
        );

        // A digest carrier against bytes stays unknown rather than guessing...
        assert_eq!(BlobEq::new(hash, raw).decide(), None);
        // ...while two digest carriers refute, exactly as their expressions do.
        assert_eq!(
            BlobEq::new(hash, O256::from_bytes(b"other")).decide(),
            decide(digest(b"blob"), digest(b"other"))
        );
    }

    fn digest(name: &'static [u8]) -> BlobExpr {
        BlobExpr::Blake3(O256::from_bytes(name))
    }

    /// A hyperblob: 65 [`Arc`]-shared nodes denoting a tree of `2^64` leaves,
    /// whose length passes `u64` and whose size pins at [`u32::MAX`]. Building
    /// it is cheap; walking it is not, which is the whole point.
    fn overflowing_nest() -> BlobExpr {
        let mut expr = bytes(b"0123456789abcdef");
        for _ in 0..64 {
            let node = Arc::new(expr);
            expr = BlobExpr::Cat(BlobCat::new(Arc::clone(&node), node));
        }
        expr
    }

    /// The proposition `head` proves, used wherever a test needs a real fact
    /// whose two sides are different expressions: `Cat("ab", "c") = "abc"`.
    fn head() -> BlobFact<BlobEq<BlobExpr, BlobExpr>> {
        BlobFact::check(BlobEq::new(
            BlobExpr::cat(bytes(b"ab"), bytes(b"c")),
            bytes(b"abc"),
        ))
        .unwrap()
    }

    /// RULE EVALUATION introduces a fact only from a proof, and declines in
    /// both of the other two cases — which are not the same thing.
    #[test]
    fn check_introduces_a_fact_only_from_a_proof() {
        let proved = BlobEq::new(BlobExpr::cat(bytes(b"ab"), bytes(b"c")), bytes(b"abc"));
        assert_eq!(proved.decide(), Some(true));
        assert_eq!(BlobFact::check(proved.clone()).unwrap().prop(), &proved);

        // Refuted. `Some(false)` is not a fact either: this crate has no fact
        // type for a refutation, which is the deferred `BlobDistinct`.
        let refuted = BlobEq::new(bytes(b"abc"), bytes(b"abd"));
        assert_eq!(refuted.decide(), Some(false));
        assert_eq!(BlobFact::check(refuted), None);

        // Unknown.
        let unknown = BlobEq::new(digest(b"blob"), bytes(b"abc"));
        assert_eq!(unknown.decide(), None);
        assert_eq!(BlobFact::check(unknown), None);
    }

    /// EVALUATION declines behind a digest. `Blake3(h)` is defined in every
    /// model, but this crate cannot read a store, so neither its length nor
    /// its bytes are available and every observation needing one is unknown
    /// rather than guessed.
    #[test]
    fn evaluation_declines_behind_a_digest() {
        let hash = O256::from_bytes(b"blob");
        let named = BlobExpr::Blake3(hash);

        // Not against the 32 bytes of the digest itself...
        let digest_bytes = BlobExpr::Bytes(Bytes::copy_from_slice(hash.as_bytes()));
        assert_eq!(
            BlobFact::check(BlobEq::new(named.clone(), digest_bytes)),
            None
        );
        // ...nor against a run of zeros, since an unknown length agrees with
        // nothing and so settles neither direction...
        assert_eq!(
            BlobFact::check(BlobEq::new(named.clone(), BlobExpr::Zero(32))),
            None
        );
        // ...nor through a slice of it, which inherits the unknown length...
        assert_eq!(
            BlobFact::check(BlobEq::new(
                BlobExpr::slice(named.clone(), 0..4),
                bytes(b"abcd")
            )),
            None
        );
        // ...and against another digest it declines for the opposite reason:
        // that one is refuted, and a refutation is not a fact either.
        let distinct = BlobEq::new(named.clone(), digest(b"other"));
        assert_eq!(distinct.decide(), Some(false));
        assert_eq!(BlobFact::check(distinct), None);

        // REFL applies anyway, and is where a fact about a digest comes from.
        assert!(BlobFact::check(BlobEq::new(named.clone(), named.clone())).is_some());
        assert_eq!(
            BlobFact::refl(named.clone()).prop(),
            &BlobEq::new(named.clone(), named)
        );
    }

    /// EVALUATION declines on an out-of-range slice, which denotes nothing
    /// rather than a clamped prefix. Two such slices of differing width are
    /// therefore equal, so refuting them from their span widths would be a
    /// false fact — and proving them would be a guess.
    #[test]
    fn evaluation_declines_on_an_out_of_range_slice() {
        let wide = BlobExpr::slice(bytes(b"ab"), 5..9);
        let narrow = BlobExpr::slice(bytes(b"ab"), 5..7);
        assert_eq!((wide.len(), narrow.len()), (None, None));
        assert_eq!(BlobFact::check(BlobEq::new(wide.clone(), narrow)), None);

        // Not clamped to the bytes that are there, either.
        assert_eq!(
            BlobFact::check(BlobEq::new(
                BlobExpr::slice(bytes(b"ab"), 1..4),
                bytes(b"b")
            )),
            None
        );

        // A backwards span reaches here through `BlobRange::span`, which
        // bypasses `BlobSpan::new`. It denotes nothing, and must not panic.
        #[allow(clippy::reversed_empty_ranges, reason = "the rule must survive this")]
        let backwards = BlobExpr::slice(bytes(b"0123456789"), 7..3);
        assert_eq!(
            BlobFact::check(BlobEq::new(backwards, bytes(b""))),
            None,
            "an empty answer here would be a clamped slice"
        );

        // REFL is total on one, since it needs no definedness.
        assert_eq!(
            BlobFact::refl(wide.clone()).prop(),
            &BlobEq::new(wide.clone(), wide)
        );
    }

    /// The `Cat` trap, from both sides. Unequal `Cat` operands say nothing
    /// about the wholes, so evaluation must never refute from a structural
    /// mismatch; and a shared operand does not license cancelling it.
    #[test]
    fn evaluation_declines_rather_than_refuting_a_cat_split() {
        // Different splits of the same bytes are equal, and are settled by
        // evaluating them rather than refuted by comparing their structure.
        let left = BlobExpr::cat(bytes(b"ab"), bytes(b"c"));
        let right = BlobExpr::cat(bytes(b"a"), bytes(b"bc"));
        assert_ne!(left, right);
        assert!(BlobFact::check(BlobEq::new(left, right)).is_some());

        // Slicing has the same trap: different subjects, same bytes.
        assert!(
            BlobFact::check(BlobEq::new(
                BlobExpr::slice(bytes(b"xabcx"), 1..4),
                BlobExpr::slice(bytes(b"yabcy"), 1..4),
            ))
            .is_some()
        );

        // With a digest in the shared head the wholes are unknown. The
        // proposition is in fact false in every model — `σ h` is defined
        // there, so the two tails would have to agree — but seeing that is
        // route (ii) of the deferred cancellation rule, which wants a
        // definedness observation `len` cannot supply for a digest. `None` is
        // incompleteness, not a soundness limit.
        let shared = digest(b"blob");
        let equation = BlobEq::new(
            BlobExpr::cat(shared.clone(), bytes(b"ab")),
            BlobExpr::cat(shared, bytes(b"cd")),
        );
        assert_eq!(equation.decide(), None);
        assert_eq!(BlobFact::check(equation), None);
    }

    /// EVALUATION declines past its budget and past `u64`. Both are
    /// incompleteness, never unsoundness: declining is always sound.
    #[test]
    fn evaluation_declines_past_the_budget_and_past_u64() {
        // True, and its lengths agree, but materialising it is refused.
        let huge = BlobExpr::Zero(MAX_EVAL_BYTES + 1);
        let split = BlobExpr::cat(BlobExpr::Zero(MAX_EVAL_BYTES), BlobExpr::Zero(1));
        assert_eq!(cmp_length(&huge, &split), Some(Ordering::Equal));
        assert_eq!(BlobFact::check(BlobEq::new(huge, split)), None);

        // The same shape inside the budget is proved.
        assert!(
            BlobFact::check(BlobEq::new(
                BlobExpr::Zero(4),
                BlobExpr::cat(BlobExpr::Zero(3), BlobExpr::Zero(1)),
            ))
            .is_some()
        );

        // A hyperblob has no length either, so nothing about it is decided.
        let nest = overflowing_nest();
        assert_eq!(nest.len(), None);
        let equation = BlobEq::new(
            BlobExpr::cat(nest.clone(), bytes(b"x")),
            BlobExpr::cat(bytes(b"x"), nest),
        );
        assert_eq!(equation.decide(), None);
        assert_eq!(BlobFact::check(equation), None);
    }

    /// `decide` declines past [`MAX_TREE_NODES`] before its REFL branch, so
    /// the exponential structural comparison is never entered on a hyperblob.
    /// Declining is sound for every proposition here, so this is pure
    /// incompleteness — and REFL as a rule is unaffected, which is where a
    /// fact about a hyperblob still comes from.
    #[test]
    fn decide_declines_past_the_tree_limit_even_for_refl() {
        let nest = overflowing_nest();
        assert!(nest.size() > MAX_TREE_NODES);

        assert_eq!(BlobEq::new(nest.clone(), nest.clone()).decide(), None);
        assert!(BlobFact::check(BlobEq::new(nest.clone(), nest.clone())).is_none());
        // The rule is total, and needs no observation at all.
        assert_eq!(
            BlobFact::refl(nest.clone()).prop(),
            &BlobEq::new(nest.clone(), nest)
        );
    }

    /// REFL is total, over carriers as well as expressions, and holds exactly
    /// where every other observation is unknown.
    #[test]
    fn refl_holds_where_nothing_else_does() {
        let hash = O256::from_bytes(b"blob");
        assert_eq!(BlobFact::refl(hash).prop(), &BlobEq::new(hash, hash));

        let unreadable = BlobExpr::slice(digest(b"blob"), 3..9);
        assert_eq!((unreadable.len(), unreadable.eval()), (None, None));
        assert_eq!(
            BlobFact::refl(unreadable.clone()).prop(),
            &BlobEq::new(unreadable.clone(), unreadable)
        );

        let nest = overflowing_nest();
        assert_eq!(
            BlobFact::refl(nest.clone()).prop(),
            &BlobEq::new(nest.clone(), nest)
        );
    }

    /// SYMM is total and is its own inverse.
    #[test]
    fn symm_swaps_the_sides() {
        let fact = head();
        let swapped = fact.symm();
        assert_eq!(
            swapped.prop(),
            &BlobEq::new(bytes(b"abc"), BlobExpr::cat(bytes(b"ab"), bytes(b"c")))
        );
        assert_eq!(swapped.symm(), fact);

        // Total: no definedness needed, so it applies to a digest fact too.
        let hash = O256::from_bytes(b"blob");
        assert_eq!(BlobFact::refl(hash).symm().prop(), &BlobEq::new(hash, hash));
    }

    /// TRANS composes only across a shared middle *expression*. The type
    /// parameters force nothing between the two middles, so this check is what
    /// keeps `a = b` and `c = d` from composing into `a = d`.
    #[test]
    fn trans_refuses_mismatched_middle_terms() {
        let first = head();
        let second = BlobFact::check(BlobEq::new(
            bytes(b"abc"),
            BlobExpr::slice(bytes(b"xabcx"), 1..4),
        ))
        .unwrap();

        let composed = first.trans(&second).unwrap();
        assert_eq!(
            composed.prop(),
            &BlobEq::new(
                BlobExpr::cat(bytes(b"ab"), bytes(b"c")),
                BlobExpr::slice(bytes(b"xabcx"), 1..4)
            )
        );

        // A different middle of the same type does not compose.
        assert_eq!(first.trans(&BlobFact::refl(bytes(b"zz"))), None);

        // The middles are compared as expressions, not as carriers, so the two
        // spellings of a whole-blob claim meet: `BlobExpr::slice` normalises
        // the `0..` span away.
        let hash = O256::from_bytes(b"blob");
        let whole = BlobSlice::new(hash, ..);
        let crossed = BlobFact::refl(whole).trans(&BlobFact::refl(hash)).unwrap();
        assert_eq!(crossed.prop(), &BlobEq::new(whole, hash));

        // Unrelated carriers of unrelated types still do not compose.
        assert_eq!(
            BlobFact::refl(hash).trans(&BlobFact::refl(bytes(b"zz"))),
            None
        );
    }

    /// CONGRUENCE for `Cat` is total, and proves what evaluation cannot: the
    /// conclusion has no length and no bytes, so `decide` is `None` on the very
    /// proposition the rule has just established.
    #[test]
    fn cat_congruence_proves_what_evaluation_cannot() {
        let joined = head().cat(&BlobFact::refl(digest(b"blob")));
        let prop = joined.prop();

        assert_eq!(prop.decide(), None);
        assert_eq!(
            prop.lhs.to_expr(),
            BlobExpr::cat(BlobExpr::cat(bytes(b"ab"), bytes(b"c")), digest(b"blob"))
        );
        assert_eq!(
            prop.rhs.to_expr(),
            BlobExpr::cat(bytes(b"abc"), digest(b"blob"))
        );
        // Equality only: the rule runs in this direction alone, and the
        // deferred cancellation rule is where the partial converse will go.
        assert_eq!(cmp_length(&prop.lhs, &prop.rhs), None);
    }

    /// CONGRUENCE for `Slice` takes one span, so the unsound shape — a
    /// different span on each side — is unrepresentable rather than rejected.
    #[test]
    fn slice_congruence_takes_one_span() {
        let fact = head();
        let narrowed = fact.slice(1..3);
        assert_eq!(narrowed.prop().lhs.span(), &(1..3));
        assert_eq!(narrowed.prop().rhs.span(), &(1..3));
        // Both sides still evaluate here, so this one is decidable too.
        assert_eq!(narrowed.prop().decide(), Some(true));

        // Slicing something unreadable is not: like `cat`, the rule proves what
        // evaluation declines to.
        let unreadable = fact.cat(&BlobFact::refl(digest(b"blob"))).slice(0..2);
        assert_eq!(unreadable.prop().decide(), None);
        assert_eq!(
            unreadable.prop().lhs.to_expr(),
            BlobExpr::slice(
                BlobExpr::cat(BlobExpr::cat(bytes(b"ab"), bytes(b"c")), digest(b"blob")),
                0..2
            )
        );
    }

    /// Erasure keeps the claim and gives up only the carrier types.
    #[test]
    fn erasing_keeps_the_claim() {
        let hash = O256::from_bytes(b"blob");
        let whole = BlobSlice::new(hash, ..);
        let erased = BlobFact::refl(whole).erase();

        assert_eq!(
            erased.prop(),
            &BlobEq::new(BlobExpr::Blake3(hash), BlobExpr::Blake3(hash))
        );
        // `to_expr` is denotation-preserving, so the erased claim decides alike.
        assert_eq!(
            erased.prop().decide(),
            BlobFact::refl(whole).prop().decide()
        );

        // And a fact over mixed carriers erases into one uniform type.
        let mixed = head()
            .cat(&BlobFact::refl(Bytes::from_static(b"z")))
            .erase();
        assert_eq!(
            mixed.prop().lhs,
            BlobExpr::cat(BlobExpr::cat(bytes(b"ab"), bytes(b"c")), bytes(b"z"))
        );
        assert_eq!(mixed.prop().decide(), Some(true));
    }

    /// The bridge round-trips every range shape, and the two spellings of a
    /// whole-blob claim meet in the middle: `to_blob_fact` builds a
    /// `BlobSlice<O256, RangeFull>`, which erases to a bare `Blake3(h)`.
    #[test]
    fn range_fact_bridge_round_trips() {
        let blob = Bytes::from_static(b"0123456789");
        let whole = CasFact::from_bytes(blob.clone());
        let hash = whole.hash();

        // Whole blob: the span normalises away, so the equality is against the
        // digest itself rather than a slice of it.
        let equality = whole.to_blob_fact().erase();
        assert_eq!(
            equality.prop(),
            &BlobEq::new(BlobExpr::Blake3(hash), BlobExpr::Bytes(blob.clone()))
        );
        assert_eq!(equality.to_range_fact::<RangeFull>(), Some(whole.clone()));

        // A closed sub-range keeps its span.
        let middle = whole.slice(3..9).unwrap();
        let equality = middle.to_blob_fact().erase();
        assert_eq!(
            equality.prop(),
            &BlobEq::new(
                BlobExpr::slice(BlobExpr::Blake3(hash), 3..9),
                BlobExpr::Bytes(Bytes::from_static(b"345678"))
            )
        );
        assert_eq!(equality.to_range_fact::<Range<u64>>(), Some(middle));

        // A length-only fact — an open span with no bytes — round-trips too,
        // and still knows how long the blob is.
        let length_only = whole.slice(10..).unwrap();
        assert!(length_only.bytes().is_empty());
        let equality = length_only.to_blob_fact().erase();
        assert_eq!(
            equality.prop(),
            &BlobEq::new(
                BlobExpr::slice(BlobExpr::Blake3(hash), 10..),
                BlobExpr::Bytes(Bytes::new())
            )
        );
        let recovered = equality.to_range_fact::<RangeFrom<u64>>().unwrap();
        assert_eq!(recovered, length_only);
        assert_eq!(recovered.blob_len(), Some(10));

        // And a prefix, whose start is zero but whose end is closed.
        let prefix = whole.slice(..4).unwrap();
        let equality = prefix.to_blob_fact().erase();
        assert_eq!(equality.to_range_fact::<RangeTo<u64>>(), Some(prefix));
    }

    /// The bridge is a genuine introduction rule: the equality it mints is
    /// valid — the CAS pins that hash, and every model extends the CAS — yet
    /// nothing in the calculus can decide it, because `decide` cannot read a
    /// store. The store is the only source of this fact.
    #[test]
    fn bridged_equality_is_not_decidable_on_its_own() {
        let fact = CasFact::from_bytes(Bytes::from_static(b"0123456789"));
        let prop = fact.to_blob_fact().erase().prop().clone();

        // Unknown: `Blake3(h)` is defined in every model, but which bytes it
        // denotes is invisible from here, so `decide` refuses to guess.
        assert_eq!(prop.decide(), None);
        assert_eq!(BlobFact::check(prop), None);
    }

    /// An empty closed window proves nothing about the address it names.
    ///
    /// `Slice(Blake3(h), k..k) = Bytes("")` is valid in every model of every
    /// store, since every byte string selects nothing on an empty range. A
    /// `CasRangeFact` asserts that a blob named `h` exists, so minting one
    /// here would be a naming claim the premise does not support.
    ///
    /// Lean: `Nucleus.BlobEq.valid_emptyWindow` proves the premise holds
    /// unconditionally, and `Nucleus.exists_valid_not_casRange` is the
    /// refutation of the conclusion.
    #[test]
    fn an_empty_closed_window_mints_no_naming_claim() {
        let hash = O256::from_bytes(b"never stored");

        for start in [0, 7, u64::MAX] {
            let empty = BlobFact::trust(BlobEq::new(
                BlobExpr::slice(BlobExpr::Blake3(hash), start..start),
                bytes(b""),
            ));
            assert_eq!(empty.to_range_fact::<Range<u64>>(), None);
            assert_eq!(empty.to_range_fact::<RangeFull>(), None);
        }

        // Everything else is contentful, so the guard costs nothing. An empty
        // range that is open still reaches the end of the blob, which is a
        // claim about the blob rather than about nothing.
        let open = BlobFact::trust(BlobEq::new(
            BlobExpr::slice(BlobExpr::Blake3(hash), 4..),
            bytes(b""),
        ));
        assert!(open.to_range_fact::<RangeFrom<u64>>().is_some());

        // And a window of nonzero width is unaffected.
        let wide = BlobFact::trust(BlobEq::new(
            BlobExpr::slice(BlobExpr::Blake3(hash), 3..9),
            bytes(b"345678"),
        ));
        assert!(wide.to_range_fact::<Range<u64>>().is_some());
    }

    /// Coming back down is partial in the shapes it can express, and each
    /// refusal is a `None` rather than a guessed fact.
    #[test]
    fn to_range_fact_refuses_shapes_that_are_not_range_facts() {
        let hash = O256::from_bytes(b"blob");
        let named = BlobExpr::Blake3(hash);

        // A span the requested shape cannot hold. `CasRangeFact::fuse` is
        // partial for the same reason.
        let closed = BlobFact::trust(BlobEq::new(
            BlobExpr::slice(named.clone(), 3..9),
            bytes(b"345678"),
        ));
        assert!(closed.to_range_fact::<Range<u64>>().is_some());
        assert_eq!(closed.to_range_fact::<RangeFrom<u64>>(), None);
        assert_eq!(closed.to_range_fact::<RangeTo<u64>>(), None);
        assert_eq!(closed.to_range_fact::<RangeFull>(), None);

        // A right-hand side that is not literal bytes.
        assert_eq!(
            BlobFact::refl(named.clone()).to_range_fact::<RangeFull>(),
            None
        );
        assert_eq!(
            BlobFact::trust(BlobEq::new(named.clone(), BlobExpr::Zero(0)))
                .to_range_fact::<RangeFull>(),
            None
        );

        // A subject that is not a digest, or not a slice of one.
        assert_eq!(
            BlobFact::refl(bytes(b"abc")).to_range_fact::<RangeFull>(),
            None
        );
        assert_eq!(
            BlobFact::trust(BlobEq::new(
                BlobExpr::cat(named.clone(), bytes(b"a")),
                bytes(b"abc")
            ))
            .to_range_fact::<RangeFull>(),
            None
        );
        // A nested slice: the span is in the inner slice's coordinates, not
        // the blob's, so there is no range fact to mint without fusing them.
        assert_eq!(
            BlobFact::trust(BlobEq::new(
                BlobExpr::slice(BlobExpr::slice(named.clone(), 3..9), 1..3),
                bytes(b"45")
            ))
            .to_range_fact::<Range<u64>>(),
            None
        );

        // The mirrored equality is not this shape; `symm` is how to get it.
        let mirrored = BlobFact::trust(BlobEq::new(bytes(b"abc"), named));
        assert_eq!(mirrored.to_range_fact::<RangeFull>(), None);
        assert!(mirrored.symm().to_range_fact::<RangeFull>().is_some());
    }

    /// The defensive width check. Redundant under `BlobEq` — no valid
    /// equality has this shape, since a closed slice of the wrong width is
    /// undefined or of another length in every model while literal bytes are
    /// always defined — but `CasRangeFact::extent` reads the width off the
    /// bytes, so trusted code minting a fact of the other layer re-checks it.
    #[test]
    fn to_range_fact_refuses_a_span_the_bytes_do_not_fill() {
        let named = BlobExpr::Blake3(O256::from_bytes(b"blob"));

        let mismatched = BlobFact::trust(BlobEq::new(
            BlobExpr::slice(named.clone(), 3..9),
            bytes(b"abc"),
        ));
        assert_eq!(mismatched.to_range_fact::<Range<u64>>(), None);

        // A backwards span reaches here through `BlobRange::span`, which
        // bypasses `BlobSpan::new`. It must refuse, not panic or wrap.
        #[allow(clippy::reversed_empty_ranges, reason = "the rule must survive this")]
        let backwards = BlobFact::trust(BlobEq::new(BlobExpr::slice(named, 9..3), bytes(b"")));
        assert_eq!(backwards.to_range_fact::<Range<u64>>(), None);
        assert_eq!(backwards.to_range_fact::<BlobSpan>(), None);
    }

    /// An open span carries no width to check, so the bytes are whatever the
    /// fact says they are — and that is exactly the length claim.
    #[test]
    fn open_spans_round_trip_through_the_erased_shape() {
        let fact = CasFact::from_bytes(Bytes::from_static(b"0123456789"))
            .slice(4..)
            .unwrap();
        let erased = fact.erase();

        let equality = erased.to_blob_fact().erase();
        let recovered = equality.to_range_fact::<BlobSpan>().unwrap();
        assert_eq!(recovered, erased);
        assert_eq!(recovered.bytes(), &Bytes::from_static(b"456789"));
        assert_eq!(recovered.blob_len(), Some(10));
    }
}
