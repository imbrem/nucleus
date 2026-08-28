//! Expressions denoting byte strings, and the length observation they support.
//!
//! A [`BlobExpr`] is *syntax*. Its meaning is a **partial function of a
//! model** — a total map `σ : O256 -> Bytes` that extends the CAS, agreeing
//! with it on every checked pair. The crate docs state what a model is, and
//! what rests on one existing, under "Standing assumption: the CAS is
//! collision-free"; it is stated there once and no rule below repeats it.
//!
//! | Expression | `denote σ` |
//! | ---------- | ---------- |
//! | `Blake3(h)` | `Some(σ h)` — ALWAYS defined; *which* bytes depends on `σ` |
//! | `Bytes(v)` | `Some(v)` |
//! | `Zero(n)` | `Some` of `n` zero bytes |
//! | `Cat(x, y)` | the two denotations concatenated, when both are defined |
//! | `Slice(e, s)` | the `s` sub-range of `denote σ e`, when `s` is in range |
//!
//! An expression denotes at most ONE byte string in a given model, so
//! undefinedness is the only three-valuedness here, and it has exactly two
//! sources: a slice whose span runs past its subject, and a concatenation with
//! an undefined side. A DIGEST IS NOT ONE OF THEM. `Blake3(h)` denotes a byte
//! string in every model even when the CAS holds nothing for `h`: an unpinned
//! hash is simply free, and different models choose differently for it. What
//! no observation in this module can do is say *which* byte string, which is
//! why a digest has neither a length nor a value here.
//!
//! Out-of-range slicing is undefined rather than clamped, uniformly in
//! [`BlobExpr::len`] and [`BlobExpr::eval`]; a truncating slice would make
//! false facts derivable.
//!
//! `Blake3(h)` is the blob *named by* `h`, never the 32 bytes of the digest.
//! Those bytes are `BlobExpr::Bytes(h.as_bytes())`, and nothing here relates
//! the two.
//!
//! # Hyperblobs are built, and then declined
//!
//! `Cat` is the only branching node and its children are [`Arc`]-shared, so a
//! DAG of `n + 1` nodes denotes a TREE of `2^n`. Every traversal in this crate
//! walks the tree rather than the DAG — [`BlobExpr::len`], [`BlobExpr::eval`],
//! `==`, [`BlobLike::to_expr`], and the `Drop` glue that frees the [`Arc`]
//! chain.
//!
//! Nothing refuses to BUILD such an expression. Every constructor here is
//! TOTAL, and deliberately so: a `Result` on `cat` and `slice` would poison
//! every call site, every trait bound and every test to solve a problem this
//! calculus does not have. An expression too large to walk is a DEGENERATE
//! INPUT, and dying on one — a stack overflow in `Drop`, a comparison that
//! runs for a week — is ACCEPTABLE. A WRONG ANSWER is not, and there is
//! exactly one way to get one here: a measurement that wraps, so that a
//! colossal expression reports a small length and satisfies a
//! length-agreement precondition that is false.
//!
//! So the arithmetic never wraps, and the observations decline:
//!
//! - every branching value carries its [`BlobLike::size`], the node count of
//!   its expression viewed as a TREE, added with SATURATING arithmetic. A size
//!   pinned at [`u32::MAX`] reads as "at least this big", which is all any
//!   check below asks of it.
//! - lengths are summed with `checked_add`, so a length past `u64` is `None`
//!   rather than a wrapped small number.
//! - [`BlobExpr::len`], [`BlobExpr::eval`] and
//!   [`BlobProp::decide`](crate::BlobProp::decide) answer `None` once that
//!   size passes [`MAX_TREE_NODES`]. `None` means "no answer here", which is
//!   sound for every rule in this calculus, so declining needs no
//!   justification beyond being available.
//!
//! `==` and `Drop` are left alone on purpose. A limit inside `==` would change
//! what equality MEANS, and `Drop` cannot decline at all — it aborts the
//! process rather than unwinding, so no `Result` and no `catch_unwind` could
//! contain it. Both may therefore be slow, or may die, on an expression that
//! nothing above would answer a question about anyway.
//!
//! Lean: `Nucleus.BlobExpr` and `Nucleus.BlobExpr.denote`, the latter a
//! function of a `Nucleus.Model` rather than the superseded `Nucleus.Denotes`
//! relation. Owed. The limit is Rust-only: Lean's expressions are finite trees
//! already, with no sharing to expand and no stack to overflow.

use std::{cmp::Ordering, fmt::Debug, sync::Arc};

use bytes::BytesMut;

use crate::{BlobRange, BlobSpan, Bytes, O256};

mod sealed {
    pub trait BlobLike {}

    impl BlobLike for covalence_lib_hash::O256 {}
    impl BlobLike for bytes::Bytes {}
    impl BlobLike for super::BlobExpr {}
    impl<B: BlobLike> BlobLike for std::sync::Arc<B> {}
    impl<B: BlobLike, S: crate::BlobRange> BlobLike for super::BlobSlice<B, S> {}
    impl<L: BlobLike, R: BlobLike> BlobLike for super::BlobCat<L, R> {}
}

/// A value denoting a byte string.
///
/// Sealed for soundness, exactly as [`BlobRange`] is: the calculus reads
/// [`Self::len`] and [`Self::eval`] and then stores the answer inside a
/// checked fact. An outside implementor that misreported a length would
/// satisfy a length-agreement precondition that is false; one that misreported
/// bytes would forge an equality.
///
/// Lean: no counterpart. Lean has one type, `Nucleus.BlobExpr`;
/// [`Self::to_expr`] is the Rust-only coercion into it, and every other method
/// is defined as the corresponding `BlobExpr` function of that coercion.
///
/// ```compile_fail
/// use covalence_logic_cas::{BlobExpr, BlobLike, Bytes};
///
/// #[derive(Clone, Debug)]
/// struct Forged;
///
/// impl BlobLike for Forged {
///     fn to_expr(&self) -> BlobExpr {
///         BlobExpr::Bytes(Bytes::new())
///     }
///
///     fn len(&self) -> Option<u64> {
///         Some(0)
///     }
/// }
/// ```
#[allow(
    clippy::len_without_is_empty,
    reason = "emptiness is three-valued here: an expression's length may be \
              unknown, so a `bool` answer would have to guess"
)]
pub trait BlobLike: sealed::BlobLike + Clone + Debug {
    /// This value as an expression. The only required method.
    ///
    /// Lean: the identity; every `BlobLike` erases into `Nucleus.BlobExpr`.
    #[must_use]
    fn to_expr(&self) -> BlobExpr;

    /// The node count of [`Self::to_expr`] viewed as a TREE, never as a DAG.
    ///
    /// This is the crate's one resource measure, and the invariant every
    /// implementor keeps is
    ///
    /// ```text
    /// self.to_expr().size() <= self.size()
    /// ```
    ///
    /// — never an under-estimate, so a caller may treat it as the cost of ANY
    /// traversal of this value and as a bound on its depth. It is exact except
    /// in two directions that both err upwards: [`BlobExpr::slice`] normalises
    /// a whole-blob span away, which only makes the reified expression
    /// smaller, and the addition SATURATES, so [`u32::MAX`] means "at least
    /// this big". Neither loses the property the readers rely on, which is
    /// that a small answer is a true one.
    ///
    /// Every implementation answers in O(1), from a memo where the shape
    /// branches. The default is for shapes that do not: it reifies, and so
    /// costs a walk of the whole tree.
    ///
    /// Lean: no counterpart. A Lean `Nucleus.BlobExpr` is a finite tree with
    /// no sharing to expand, so nothing there needs bounding.
    #[must_use]
    fn size(&self) -> u32 {
        self.to_expr().size()
    }

    /// The length of the byte string this value denotes, when a `u64` answers.
    ///
    /// Compare two of these only through [`cmp_length`]; see its docs for why
    /// `==` is a soundness bug. See [`BlobExpr::len`] for what `Some` and
    /// `None` mean.
    ///
    /// Lean: `Nucleus.BlobExpr.length?`.
    #[must_use]
    fn len(&self) -> Option<u64> {
        self.to_expr().len()
    }

    /// The bytes this value denotes, when every model reads the same ones from
    /// it. See [`BlobExpr::eval`].
    ///
    /// Lean: `Nucleus.BlobExpr.eval?`.
    #[must_use]
    fn eval(&self) -> Option<Bytes> {
        self.to_expr().eval()
    }
}

/// An expression denoting a byte string.
///
/// Variants are named for the hash ALGORITHM, not for "the CAS": `Sha256` is a
/// planned sibling and nothing here assumes a unique digest variant. Each
/// digest arm is written out rather than caught by `_`, because
/// `#[non_exhaustive]` does not weaken exhaustiveness inside the defining
/// crate, so adding a variant breaks the build at every arm that must decide.
///
/// Lean: `Nucleus.BlobExpr`.
#[non_exhaustive]
#[derive(Clone, Debug, Eq)]
pub enum BlobExpr {
    /// The blob whose unkeyed BLAKE3 content address is this [`O256`] — not
    /// the 32 bytes of the digest, which are `BlobExpr::Bytes(h.as_bytes())`.
    ///
    /// The payload is [`O256`] rather than
    /// [`Blake3Hash`](covalence_lib_hash::blake3::Blake3Hash) because every
    /// consumer of this crate speaks `O256`, and because widening loses
    /// nothing: a keyed or context-derived `O256` simply is not a hash the CAS
    /// ever pins, so every model is free to give it any bytes at all. That is
    /// the ordinary unpinned case, which the calculus already handles without
    /// special-casing.
    ///
    /// Lean: `Nucleus.BlobExpr.blake3`.
    Blake3(O256),
    /// A sub-range of another expression. Out of range is undefined.
    ///
    /// Lean: `Nucleus.BlobExpr.slice`.
    Slice(BlobSlice<Arc<Self>, BlobSpan>),
    /// Two expressions concatenated.
    ///
    /// Lean: `Nucleus.BlobExpr.cat`.
    Cat(BlobCat<Arc<Self>, Arc<Self>>),
    /// Literal bytes.
    ///
    /// Lean: `Nucleus.BlobExpr.bytes`.
    Bytes(Bytes),
    /// A run of zero bytes.
    ///
    /// Lean: `Nucleus.BlobExpr.zero`.
    Zero(u64),
}

/// A sub-range of a blob, carrying its own tree size.
///
/// Fields are PRIVATE and [`Self::new`] is the only way in, because the memo
/// is an INVARIANT rather than a claim: it has to stay a function of `blob`,
/// and a struct literal could set it to anything. Nothing unsound follows from
/// a forged memo — its only readers decline on it, and declining is sound —
/// but a forged small one would put back the traversal the limit exists to
/// skip. Being a function of the other fields, it makes no difference to `==`.
///
/// Lean: erases into `Nucleus.BlobExpr.sliceOf`. The memo has NO Lean
/// counterpart.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BlobSlice<B, S> {
    blob: B,
    span: S,
    size: u32,
}

impl<B: BlobLike, S: BlobRange> BlobSlice<B, S> {
    /// Slices a value, computing the result's tree size once.
    ///
    /// TOTAL. A slice node is one node on top of its subject, and the addition
    /// SATURATES, so an absurd subject yields a memo pinned at [`u32::MAX`]
    /// rather than a refusal; see the module docs for why nothing here refuses.
    ///
    /// Lean: `Nucleus.BlobExpr.sliceOf`.
    #[must_use]
    pub fn new(blob: B, span: S) -> Self {
        let size = blob.size().saturating_add(1);
        Self { blob, span, size }
    }

    /// Borrows the expression being sliced.
    #[must_use]
    pub const fn blob(&self) -> &B {
        &self.blob
    }

    /// Borrows the range taken from it, in that expression's own coordinates.
    #[must_use]
    pub const fn span(&self) -> &S {
        &self.span
    }
}

/// A concatenation, carrying its own length and tree size.
///
/// Fields are PRIVATE and [`Self::new`] is the only constructor, because the
/// cached length is what the disequality rule reads: a forged cache makes
/// [`BlobLike::len`] lie. Both caches are functions of the other two fields.
///
/// Neither is an optimization. `Cat` is the only branching node and children
/// are [`Arc`]-shared, so a 64-level doubling DAG is 65 nodes but `2^64`
/// leaves; an unmemoized recursion over it does not terminate. Caching the
/// length is what lets it be answered — `checked_add`ed, so `None` rather than
/// wrapped — without walking those leaves, and caching the size is what lets
/// [`BlobExpr::len`] and its fellows DECLINE without walking them either.
///
/// Lean: erases into `Nucleus.BlobExpr.cat`. The caches have NO Lean
/// counterpart; `Nucleus.BlobExpr.length?` recomputes.
#[derive(Clone, Copy, Debug)]
pub struct BlobCat<L, R> {
    left: L,
    right: R,
    len: Option<u64>,
    size: u32,
}

impl<L: BlobLike, R: BlobLike> BlobCat<L, R> {
    /// Concatenates two values, computing the result's length and tree size
    /// once each.
    ///
    /// TOTAL. The length is `checked_add`ed and the size saturates, so an
    /// absurd pair yields `None` and [`u32::MAX`] rather than a refusal. The
    /// sizes are counted as TREES: concatenating an expression with ITSELF
    /// doubles the count, whatever the [`Arc`] sharing underneath.
    ///
    /// Lean: `Nucleus.BlobExpr.cat`.
    #[must_use]
    pub fn new(left: L, right: R) -> Self {
        // Byte strings are conceptually Nat-length; `u64` is the answerable
        // fragment. `checked_add` keeps a colossal expression from reporting a
        // small length and satisfying a precondition that is false.
        let len = match (left.len(), right.len()) {
            (Some(left), Some(right)) => left.checked_add(right),
            _ => None,
        };
        let size = left.size().saturating_add(right.size()).saturating_add(1);
        Self {
            left,
            right,
            len,
            size,
        }
    }

    /// Borrows the left operand.
    #[must_use]
    pub const fn left(&self) -> &L {
        &self.left
    }

    /// Borrows the right operand.
    #[must_use]
    pub const fn right(&self) -> &R {
        &self.right
    }
}

// The cached length is a function of the operands, so comparing it would
// change nothing. It is deliberately left out: an `Option<u64> == Option<u64>`
// next to `cmp_length` invites reuse of the pattern where it is not benign.
impl<L: PartialEq, R: PartialEq> PartialEq for BlobCat<L, R> {
    fn eq(&self, other: &Self) -> bool {
        self.left == other.left && self.right == other.right
    }
}

impl<L: Eq, R: Eq> Eq for BlobCat<L, R> {}

/// Compares two shared sub-expressions.
///
/// Same allocation implies same value, so the pointer test is sound. It is an
/// OPTIMIZATION AND NOTHING MORE, and it is worth saying which case it misses:
/// it can only fire between [`Arc`]s that are shared, which two independently
/// built expressions never are, however alike they look. Comparing two copies
/// of a doubling DAG therefore walks both trees in full, and NOTHING bounds
/// that: `==` is left exponential deliberately, since a limit inside it would
/// change what equality MEANS. What keeps the calculus clear of it is
/// [`BlobProp::decide`](crate::BlobProp::decide), which declines past
/// [`MAX_TREE_NODES`] before it ever compares anything.
fn shared_eq(left: &Arc<BlobExpr>, right: &Arc<BlobExpr>) -> bool {
    Arc::ptr_eq(left, right) || **left == **right
}

// Hand-written rather than derived, for the `Arc::ptr_eq` fast path. The outer
// match is over `self` alone so that adding a digest variant breaks the build
// here rather than falling into a catch-all that would silently answer `false`
// for two equal expressions.
impl PartialEq for BlobExpr {
    fn eq(&self, other: &Self) -> bool {
        match self {
            Self::Blake3(hash) => matches!(other, Self::Blake3(rhs) if hash == rhs),
            Self::Slice(slice) => matches!(
                other,
                Self::Slice(rhs) if slice.span == rhs.span && shared_eq(&slice.blob, &rhs.blob)
            ),
            Self::Cat(cat) => matches!(
                other,
                Self::Cat(rhs)
                    if shared_eq(&cat.left, &rhs.left) && shared_eq(&cat.right, &rhs.right)
            ),
            Self::Bytes(bytes) => matches!(other, Self::Bytes(rhs) if bytes == rhs),
            Self::Zero(count) => matches!(other, Self::Zero(rhs) if count == rhs),
        }
    }
}

#[allow(
    clippy::len_without_is_empty,
    reason = "emptiness is three-valued here: an expression's length may be \
              unknown, so a `bool` answer would have to guess"
)]
impl BlobExpr {
    /// Concatenates two expressions. TOTAL; see the module docs for why
    /// nothing here refuses to build.
    ///
    /// Lean: `Nucleus.BlobExpr.cat`.
    #[must_use]
    pub fn cat(left: Self, right: Self) -> Self {
        Self::Cat(BlobCat::new(Arc::new(left), Arc::new(right)))
    }

    /// Slices an expression, normalising the whole-blob span away. TOTAL.
    ///
    /// `slice(e, 0..) = e` is SOUND: every byte string is its own `0..`
    /// sub-range, so the two denote the same thing in every model, and are
    /// undefined in the same models. It earns its `if` because `O256` and
    /// `BlobSlice<O256, RangeFull>` would otherwise reify to different
    /// expressions for the same claim, and the transitivity rule matches
    /// middle terms syntactically.
    ///
    /// Lean: `Nucleus.BlobExpr.sliceOf`, with `@[simp] denotes_sliceOf`.
    #[allow(
        clippy::needless_pass_by_value,
        reason = "the range shapes are small `Copy` values, and by-value is the \
                  call shape `CasRangeFact::slice` already uses"
    )]
    #[must_use]
    pub fn slice(blob: Self, span: impl BlobRange) -> Self {
        let span = span.span();
        if span == BlobSpan::WHOLE {
            return blob;
        }
        Self::Slice(BlobSlice::new(Arc::new(blob), span))
    }

    /// The node count of this expression viewed as a TREE, never as a DAG.
    ///
    /// O(1) from the memo at each branching node, and EXACT until it saturates
    /// at [`u32::MAX`], where it reads as "at least this big". `Cat` counts
    /// both children in full, so an expression sharing one [`Arc`] between
    /// them counts it twice. That is the point — every traversal expands the
    /// sharing, so the tree is the true cost, and [`MAX_TREE_NODES`] is the
    /// size past which the observations below decline to pay it.
    ///
    /// Lean: no counterpart; see [`BlobLike::size`].
    ///
    /// ```
    /// use covalence_logic_cas::{BlobExpr, Bytes};
    ///
    /// let leaf = BlobExpr::Bytes(Bytes::from_static(b"x"));
    /// assert_eq!(leaf.size(), 1);
    ///
    /// // Sharing does not make the tree smaller: this is three nodes, not two.
    /// let doubled = BlobExpr::cat(leaf.clone(), leaf);
    /// assert_eq!(doubled.size(), 3);
    /// assert_eq!(BlobExpr::cat(doubled.clone(), doubled).size(), 7);
    /// ```
    #[must_use]
    pub const fn size(&self) -> u32 {
        match self {
            Self::Blake3(_) | Self::Bytes(_) | Self::Zero(_) => 1,
            Self::Slice(slice) => slice.size,
            Self::Cat(cat) => cat.size,
        }
    }

    /// The length of the byte string this expression denotes, when a `u64`
    /// answers.
    ///
    /// `Some(n)` is a DEFINEDNESS CERTIFICATE, and it quantifies over models:
    /// the expression is defined in EVERY model and is `n` bytes long in every
    /// one of them. That is what makes length-disagreement a sound disequality
    /// and what gives the deferred cancellation rule a computed precondition.
    /// It is why the `Slice` arm bounds-checks rather than reporting the span's
    /// width: two out-of-range slices of differing width are undefined in every
    /// model, so they are *equal*, and an unchecked width would refute that.
    ///
    /// `None` is neither an error nor zero. It means "no `u64` answer",
    /// whether because a digest hides the length, a slice is out of range, a
    /// `Cat` sum does not fit, or the expression passes [`MAX_TREE_NODES`] and
    /// this declines to walk it. All are uniformly conservative: by the `None`
    /// convention of [`cmp_length`] an unknown length agrees with nothing, so
    /// an over-long `Cat` never cancels and never settles a disequality. There
    /// is deliberately no error type distinguishing the cases.
    ///
    /// The size guard comes FIRST, and it is what makes the recursion below
    /// safe to enter: past it, the walk visits at most [`MAX_TREE_NODES`]
    /// nodes and nests at most that deep. A hyperblob gets `None`, which is
    /// exactly the answer a hyperblob deserves — never a wrapped small number
    /// that would satisfy a length-agreement precondition that is false.
    ///
    /// `Blake3(h)` is the interesting `None`. It is not undefined — every model
    /// reads *some* byte string at `h` — but `σ h` varies from model to model,
    /// so no single `n` answers, and a certificate quantified over models is
    /// exactly what this returns.
    ///
    /// Lean: `Nucleus.BlobExpr.length?`. ONE-DIRECTIONAL: Lean recurses in
    /// `Nat` and never overflows, so Rust answers `None` strictly more often;
    /// the obligation is `length?_agrees`, that when Rust answers it agrees.
    /// The definedness certificate itself is owed as `denote_isSome_of_length?`
    /// (`length? = some n` implies the expression is defined in every model)
    /// and `length?_sound` (it is `n` bytes long there).
    ///
    /// ```
    /// use covalence_logic_cas::{BlobExpr, Bytes, O256};
    ///
    /// assert_eq!(BlobExpr::Bytes(Bytes::from_static(b"abc")).len(), Some(3));
    /// assert_eq!(BlobExpr::Zero(9).len(), Some(9));
    /// // A digest is always defined, but its length varies by model.
    /// assert_eq!(BlobExpr::Blake3(O256::from_bytes(b"abc")).len(), None);
    /// ```
    #[must_use]
    pub fn len(&self) -> Option<u64> {
        if self.size() > MAX_TREE_NODES {
            return None;
        }
        match self {
            // Defined in every model, but `σ h` differs between them, so no
            // single `u64` is the length in all of them.
            Self::Blake3(_) => None,
            Self::Bytes(bytes) => u64::try_from(bytes.len()).ok(),
            Self::Zero(count) => Some(*count),
            // O(1): the sum was `checked_add`ed at construction.
            Self::Cat(cat) => cat.len,
            // The one place the slice length rule lives.
            Self::Slice(slice) => BlobLike::len(slice),
        }
    }

    /// RULE: EVALUATION. The bytes this expression denotes, when every model
    /// reads the same ones from it.
    ///
    /// `Some(v)` is a stronger certificate than [`Self::len`]'s: the
    /// expression is defined in every model and denotes exactly `v` there,
    /// so it settles an equality in both directions rather than only refuting.
    ///
    /// `None` for any `Blake3` node — `σ h` varies across models, and this
    /// crate cannot read a store to learn that `h` is pinned — for an
    /// out-of-range or backwards `Slice` (undefined in every model), when the
    /// length has no `u64` answer, past [`MAX_EVAL_BYTES`], and past
    /// [`MAX_TREE_NODES`].
    ///
    /// The two limits bound different things, and both are needed.
    /// [`MAX_EVAL_BYTES`] bounds the RESULT: it refuses `Zero(u64::MAX)`
    /// before a huge allocation aborts the process, and, being applied through
    /// [`Self::len`], it makes `eval e = Some v` imply `len e = Some(v.len())`
    /// with no loss. What it does NOT bound is the work — an `n`-level
    /// doubling DAG is `n + 1` nodes and `2^n` tree nodes, and this recurses
    /// into both children at every level, so with one-byte leaves a 30-level
    /// DAG sits inside the byte budget while doing sixty-four times the work
    /// of a 24-level one. [`MAX_TREE_NODES`] bounds that: past it this
    /// declines, and inside it the walk visits at most that many nodes, each
    /// copying at most [`MAX_EVAL_BYTES`].
    ///
    /// Lean: `Nucleus.BlobExpr.eval?`, owing `eval?_sound`: evaluating to `v`
    /// pins the denotation to the singleton `{v}`. ONE-DIRECTIONAL: neither
    /// limit has a Lean counterpart.
    ///
    /// ```
    /// use covalence_logic_cas::{BlobExpr, Bytes};
    ///
    /// let expr = BlobExpr::cat(
    ///     BlobExpr::Bytes(Bytes::from_static(b"ab")),
    ///     BlobExpr::Zero(2),
    /// );
    /// assert_eq!(expr.eval(), Some(Bytes::from_static(b"ab\0\0")));
    /// ```
    #[must_use]
    pub fn eval(&self) -> Option<Bytes> {
        // Stated here rather than inherited from `len`, so that this rule's
        // own contract does not rest on another one's guard.
        if self.size() > MAX_TREE_NODES || self.len()? > MAX_EVAL_BYTES {
            return None;
        }
        match self {
            // Unreachable through the guard above, since a digest has no known
            // length; written out so a new digest variant must decide.
            Self::Blake3(_) => None,
            Self::Bytes(bytes) => Some(bytes.clone()),
            Self::Zero(count) => {
                // The guard bounds `count` by `MAX_EVAL_BYTES`.
                let count = usize::try_from(*count).ok()?;
                Some(Bytes::from(vec![0; count]))
            }
            Self::Cat(cat) => {
                let left = cat.left.eval()?;
                let right = cat.right.eval()?;
                let mut joined = BytesMut::with_capacity(left.len() + right.len());
                joined.extend_from_slice(&left);
                joined.extend_from_slice(&right);
                Some(joined.freeze())
            }
            Self::Slice(slice) => BlobLike::eval(slice),
        }
    }
}

/// The largest expression [`BlobExpr::eval`] will materialise.
///
/// Completeness only: a smaller budget yields `None`, which means "unknown"
/// and is always sound. It bounds the ANSWER; [`MAX_TREE_NODES`] bounds the
/// work of getting there. Lean has no counterpart.
pub const MAX_EVAL_BYTES: u64 = 1 << 30;

/// The largest expression the observations here will WALK, counted as a tree.
///
/// ONE THOUSAND AND TWENTY-FOUR nodes. Nothing refuses to BUILD a bigger one;
/// [`BlobExpr::len`], [`BlobExpr::eval`] and
/// [`BlobProp::decide`](crate::BlobProp::decide) simply answer `None` past
/// this point instead of walking it.
///
/// Completeness only, like [`MAX_EVAL_BYTES`]. `None` is "the rules do not
/// settle it", which is a sound answer to every question this calculus asks,
/// so a limit set too low costs answers and never truth. That is the whole
/// justification, and it is why the number can be this small.
///
/// Why so small. Nothing here is MEANT to build a large expression: the bridge
/// from a range fact is two nodes, each congruence rule adds one, and the
/// widest thing anyone reassembles by hand is a concatenation of range facts
/// at two nodes each — so 1024 leaves room for some five hundred of them,
/// orders of magnitude past any use these expressions were designed for. What
/// it buys is that a declining traversal visits at most 1024 nodes and nests
/// at most 1024 deep, tens of kilobytes of stack. Raising it would only admit
/// inputs that are already past reasoning about.
///
/// Lean has no counterpart: its expressions are finite trees with no sharing.
pub const MAX_TREE_NODES: u32 = 1024;

/// Compares two values' lengths, or `None` when either is unknown.
///
/// This is the ONLY place in the crate where two lengths are compared, and the
/// only place the deferred cancellation rule would compute its precondition.
///
/// Writing `left.len() == right.len()` would be a SOUNDNESS BUG: `Option`'s
/// derived `PartialEq` makes `None == None` true, so two values of unknown
/// length would pass as having agreeing lengths. Unknown lengths compare like
/// SQL `NULL`: none equals anything, not even itself. The `?` makes that
/// unrepresentable here — the convention is structural, not a comment someone
/// can forget. Note that "known to differ" is
/// `matches!(.., Some(Less | Greater))`, which is NOT `!= Some(Equal)`.
///
/// Lean: `Nucleus.BlobExpr.cmpLength?`.
///
/// ```
/// use std::cmp::Ordering;
///
/// use covalence_logic_cas::{BlobExpr, O256, cmp_length};
///
/// let unknown = BlobExpr::Blake3(O256::from_bytes(b"blob"));
/// assert_eq!(cmp_length(&unknown, &unknown), None);
/// assert_eq!(
///     cmp_length(&BlobExpr::Zero(1), &BlobExpr::Zero(2)),
///     Some(Ordering::Less)
/// );
/// ```
#[must_use]
pub fn cmp_length(left: &impl BlobLike, right: &impl BlobLike) -> Option<Ordering> {
    Some(left.len()?.cmp(&right.len()?))
}

impl BlobLike for O256 {
    fn to_expr(&self) -> BlobExpr {
        BlobExpr::Blake3(*self)
    }

    /// A leaf, whatever the size of the blob it names.
    fn size(&self) -> u32 {
        1
    }

    /// A digest does not carry the length of what it names.
    fn len(&self) -> Option<u64> {
        None
    }

    /// This crate cannot read a store, so a digest never evaluates.
    fn eval(&self) -> Option<Bytes> {
        None
    }
}

impl BlobLike for Bytes {
    fn to_expr(&self) -> BlobExpr {
        BlobExpr::Bytes(self.clone())
    }

    /// A leaf, however many bytes it holds.
    fn size(&self) -> u32 {
        1
    }

    fn len(&self) -> Option<u64> {
        u64::try_from(Self::len(self)).ok()
    }

    fn eval(&self) -> Option<Bytes> {
        Some(self.clone())
    }
}

impl BlobLike for BlobExpr {
    fn to_expr(&self) -> Self {
        self.clone()
    }

    fn size(&self) -> u32 {
        Self::size(self)
    }

    fn len(&self) -> Option<u64> {
        Self::len(self)
    }

    fn eval(&self) -> Option<Bytes> {
        Self::eval(self)
    }
}

impl<B: BlobLike> BlobLike for Arc<B> {
    fn to_expr(&self) -> BlobExpr {
        (**self).to_expr()
    }

    /// Sharing costs a node NOTHING and saves it nothing: the tree counts what
    /// a traversal walks, and a traversal walks through the [`Arc`].
    fn size(&self) -> u32 {
        (**self).size()
    }

    fn len(&self) -> Option<u64> {
        (**self).len()
    }

    fn eval(&self) -> Option<Bytes> {
        (**self).eval()
    }
}

impl<B: BlobLike, S: BlobRange> BlobLike for BlobSlice<B, S> {
    /// Total, and it never grows the count: this value's memo already counts
    /// the slice node, and the whole-blob case normalises that node away.
    fn to_expr(&self) -> BlobExpr {
        let blob = self.blob.to_expr();
        let span = self.span.span();
        if span == BlobSpan::WHOLE {
            blob
        } else {
            BlobExpr::Slice(BlobSlice::new(Arc::new(blob), span))
        }
    }

    /// The memo, read in O(1). See [`Self::new`].
    fn size(&self) -> u32 {
        self.size
    }

    /// The ONE place the slice length rule lives; [`BlobExpr::len`] delegates.
    ///
    /// Deliberately stronger than "the span width": the bounds check against
    /// the subject's length is what makes `Some` certify that the slice is
    /// defined. The unchecked width is UNSOUND as a disequality source,
    /// because two out-of-range slices of differing width are undefined in
    /// every model and are therefore equal.
    ///
    /// The `start <= end` guard matters too:
    /// [`BlobRange::span`](crate::BlobRange::span) builds a
    /// [`BlobSpan`](crate::BlobSpan) by struct literal, bypassing
    /// `BlobSpan::new`'s guard, so a backwards `Range<u64>` reaches here. It
    /// denotes nothing, so `None` is both panic-free and correct.
    ///
    /// Cost: `Slice(Blake3(h), 0..32)` reports `None`, losing one disequality.
    /// Recovering it later is purely additive.
    fn len(&self) -> Option<u64> {
        let whole = self.blob.len()?;
        let start = self.span.start();
        let end = self.span.end().unwrap_or(whole);
        (start <= end && end <= whole).then(|| end - start)
    }

    fn eval(&self) -> Option<Bytes> {
        let whole = self.blob.eval()?;
        let len = u64::try_from(whole.len()).ok()?;
        let start = self.span.start();
        let end = self.span.end().unwrap_or(len);
        if start > end || end > len {
            return None;
        }
        // Both offsets are bounded by `len`, which is a `usize` already.
        let from = usize::try_from(start).ok()?;
        let to = usize::try_from(end).ok()?;
        Some(whole.slice(from..to))
    }
}

impl<L: BlobLike, R: BlobLike> BlobLike for BlobCat<L, R> {
    /// Total, and it never grows the count, for the reason given on
    /// [`BlobSlice::to_expr`]. It is NOT cheap: reifying walks both operands
    /// in full, so on a hyperblob carrier it is one of the traversals that may
    /// die rather than decline.
    fn to_expr(&self) -> BlobExpr {
        BlobExpr::Cat(BlobCat::new(
            Arc::new(self.left.to_expr()),
            Arc::new(self.right.to_expr()),
        ))
    }

    /// The memo, read in O(1). See [`Self::new`].
    fn size(&self) -> u32 {
        self.size
    }

    /// The memo, read in O(1). See [`Self::new`].
    ///
    /// Deliberately NOT guarded by [`MAX_TREE_NODES`], unlike
    /// [`BlobExpr::len`]: reading a memo walks nothing, so there is no work to
    /// decline, and the value is exact or `None` — `Self::new` summed it with
    /// `checked_add`. So this may answer where the reified expression, which
    /// would have to be walked, declines. Both answers are sound; one is
    /// merely less complete.
    fn len(&self) -> Option<u64> {
        self.len
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bytes(value: &'static [u8]) -> BlobExpr {
        BlobExpr::Bytes(Bytes::from_static(value))
    }

    /// An `Arc`-shared doubling DAG over `leaf`: `levels` new nodes, and a
    /// TREE of `2^(levels + 1) - 1`. Each level is ONE node and TWICE the
    /// tree, which is the shape every limit here exists for.
    fn doubling_dag(leaf: BlobExpr, levels: u32) -> BlobExpr {
        let mut expr = leaf;
        for _ in 0..levels {
            let node = Arc::new(expr);
            expr = BlobExpr::Cat(BlobCat::new(Arc::clone(&node), node));
        }
        expr
    }

    /// MANDATORY (R8). Sixty-four nested `Cat`s. The length is exact while the
    /// tree is small enough to walk, and `None` after — from the size limit
    /// first and from `checked_add` past `2^64` — but NEVER a small wrapped
    /// number, which is the one answer that would be a lie. It must not panic
    /// in a debug build either.
    #[test]
    fn nested_cat_length_never_wraps() {
        let mut expr = bytes(b"0123456789abcdef"); // 2^4 bytes
        for level in 0..64_u32 {
            let node = Arc::new(expr);
            expr = BlobExpr::Cat(BlobCat::new(Arc::clone(&node), node));
            if level < 9 {
                // 3, 7, ... 1023 nodes: small enough to walk, so exact.
                assert_eq!(expr.size(), 2_u32.pow(level + 2) - 1);
                assert_eq!(expr.len(), Some(1_u64 << (5 + level)));
            } else {
                // 2047 nodes and up. `len` declines rather than walking, and
                // it declines the same way once `2^64` bytes are passed.
                assert!(expr.size() > MAX_TREE_NODES);
                assert_eq!(expr.len(), None);
            }
        }
        // Sixty-four doublings is `2^70` tree nodes, so the memo has pinned at
        // its maximum: "at least this big", which is all the limit needs.
        assert_eq!(expr.size(), u32::MAX);
        assert_eq!(expr.len(), None);
        assert_eq!(expr.eval(), None);

        // A length past `u64` is also reachable without deep sharing, and is
        // `None` there too rather than a wrapped 0 — this one is `checked_add`
        // alone, the tree being three nodes.
        let huge = BlobExpr::cat(BlobExpr::Zero(u64::MAX), BlobExpr::Zero(u64::MAX));
        assert_eq!(huge.size(), 3);
        assert_eq!(huge.len(), None);
        // And evaluation must refuse it without allocating.
        assert_eq!(huge.eval(), None);
        assert_eq!(BlobExpr::cat(huge.clone(), bytes(b"a")).len(), None);
    }

    /// Deep nesting BUILDS, and is then DECLINED. Making the constructors
    /// fallible instead would poison every call site to solve a non-problem:
    /// a hyperblob is a degenerate input, and what must never happen to one is
    /// a WRONG ANSWER, not a refusal to exist.
    #[test]
    fn deep_nesting_is_built_and_then_declined() {
        // Slices: one node per level, so the limit is passed at the limit.
        let mut expr = bytes(b"0123456789");
        for _ in 0..MAX_TREE_NODES {
            expr = BlobExpr::slice(expr, 0..1);
        }
        assert_eq!(expr.size(), MAX_TREE_NODES + 1);
        assert_eq!(expr.len(), None);
        assert_eq!(expr.eval(), None);

        // One node fewer and the same shape answers, walking all 1024 of them.
        let mut inside = bytes(b"0123456789");
        for _ in 0..MAX_TREE_NODES - 1 {
            inside = BlobExpr::slice(inside, 0..1);
        }
        assert_eq!(inside.size(), MAX_TREE_NODES);
        assert_eq!(inside.len(), Some(1));
        assert_eq!(inside.eval(), Some(Bytes::from_static(b"0")));

        // `Cat`s, spine-shaped rather than doubling: also one node per level,
        // and the memo is `None` past the limit rather than a wrapped number.
        let mut spine = bytes(b"z");
        for _ in 0..MAX_TREE_NODES {
            spine = BlobExpr::cat(spine, bytes(b"z"));
        }
        assert_eq!(spine.size(), 2 * MAX_TREE_NODES + 1);
        assert_eq!(spine.len(), None);
    }

    /// Two INDEPENDENTLY built, structurally identical DAGs compare by walking
    /// both TREES in full: [`shared_eq`]'s pointer test cannot fire between
    /// them, nothing being shared across two separately built expressions.
    ///
    /// Nothing bounds that walk, and nothing should — a limit inside `==`
    /// would change what equality MEANS. Under [`MAX_TREE_NODES`] it is
    /// microseconds, and above it
    /// [`BlobProp::decide`](crate::BlobProp::decide) declines before it ever
    /// gets here; `eq.rs` pins that half.
    #[test]
    fn independent_dags_compare_by_walking_both_trees() {
        let left = doubling_dag(bytes(b"0123456789abcdef"), 9);
        let right = doubling_dag(bytes(b"0123456789abcdef"), 9);
        assert_eq!(left.size(), MAX_TREE_NODES - 1);
        assert_eq!(left, right);

        // The worst case, where they differ only at the leaves, so every one
        // of those nodes is visited before the answer comes back.
        assert_ne!(left, doubling_dag(bytes(b"fedcba9876543210"), 9));
    }

    /// Evaluating a shared doubling DAG expands the sharing, so the work is
    /// the TREE. [`MAX_EVAL_BYTES`] bounds the ANSWER and so never bounded
    /// this: a 30-level DAG of one-byte leaves sits inside the byte budget
    /// while doing sixty-four times the work of a 24-level one.
    /// [`MAX_TREE_NODES`] is what makes `eval` decline instead.
    #[test]
    fn eval_expands_the_sharing_and_declines_past_the_limit() {
        let inside = doubling_dag(bytes(b"x"), 9);
        assert_eq!(inside.size(), MAX_TREE_NODES - 1);
        // One byte per leaf and `2^9` leaves, so the ANSWER is tiny and the
        // byte budget was never going to be what stopped this.
        assert_eq!(inside.len(), Some(512));
        assert!(inside.len() < Some(MAX_EVAL_BYTES));
        assert_eq!(inside.eval(), Some(Bytes::from(vec![b'x'; 512])));

        // One level more is 2047 nodes, and `eval` declines rather than
        // walking them — though the answer would still be a kilobyte.
        let outside = doubling_dag(bytes(b"x"), 10);
        assert_eq!(outside.size(), 2 * MAX_TREE_NODES - 1);
        assert_eq!(outside.len(), None);
        assert_eq!(outside.eval(), None);
    }

    /// The limit is stated in TREE nodes, so sharing buys nothing: `Cat`
    /// counts a child twice when both sides are the same allocation.
    #[test]
    fn size_counts_the_tree_and_never_the_dag() {
        let leaf = bytes(b"x");
        assert_eq!(leaf.size(), 1);
        assert_eq!(BlobExpr::Zero(u64::MAX).size(), 1);
        assert_eq!(BlobExpr::Blake3(O256::from_bytes(b"blob")).size(), 1);

        let shared = Arc::new(leaf.clone());
        let doubled = BlobExpr::Cat(BlobCat::new(Arc::clone(&shared), shared));
        assert_eq!(doubled.size(), 3);
        assert_eq!(BlobExpr::slice(doubled.clone(), 0..1).size(), 4);
        // The whole-blob span normalises away, and takes its node with it.
        assert_eq!(BlobExpr::slice(doubled.clone(), ..).size(), 3);

        // Carriers count the same way, and reifying never grows the count.
        let carrier = BlobCat::new(O256::from_bytes(b"blob"), Bytes::from_static(b"a"));
        assert_eq!(BlobLike::size(&carrier), 3);
        assert_eq!(carrier.to_expr().size(), 3);
        let sliced = BlobSlice::new(O256::from_bytes(b"blob"), ..);
        assert_eq!(BlobLike::size(&sliced), 2);
        assert_eq!(sliced.to_expr().size(), 1); // `0..` normalises away
    }

    /// A `BlobCat` carrier answers its length from the memo without the size
    /// guard, so it may answer where the REIFIED expression declines. Both are
    /// sound: the memo is exact or `None`, never wrapped, and `None` is a
    /// refusal to answer rather than a claim.
    #[test]
    fn a_cat_memo_answers_where_the_reified_expression_declines() {
        let deep = doubling_dag(bytes(b"x"), 9); // 1023 nodes, 512 bytes
        let carrier = BlobCat::new(deep.clone(), deep);

        assert_eq!(BlobLike::size(&carrier), 2 * MAX_TREE_NODES - 1);
        assert_eq!(BlobLike::len(&carrier), Some(1024)); // O(1), and exact
        assert_eq!(carrier.to_expr().len(), None); // would have to be walked
    }

    /// MANDATORY (R7). `None` agrees with nothing, not even itself.
    #[test]
    fn unknown_lengths_never_agree_and_therefore_never_cancel() {
        let left = BlobExpr::Blake3(O256::from_bytes(b"left"));
        let right = BlobExpr::Blake3(O256::from_bytes(b"right"));

        assert_eq!((left.len(), right.len()), (None, None));
        assert_eq!(cmp_length(&left, &left), None); // NOT `Some(Equal)`
        assert_eq!(cmp_length(&left, &right), None);
        assert_eq!(cmp_length(&left, &BlobExpr::Zero(3)), None);
        assert_eq!(cmp_length(&BlobExpr::Zero(3), &left), None);
        // Writing `left.len() == right.len()` would be `true` here, and that
        // is exactly the bug `cmp_length` exists to make unwritable.
        assert_eq!(
            left.len(),
            right.len(),
            "unknown lengths look alike to `==`"
        );
    }

    #[test]
    fn lengths_follow_the_structure() {
        assert_eq!(bytes(b"abc").len(), Some(3));
        assert_eq!(BlobExpr::Zero(0).len(), Some(0));
        assert_eq!(BlobExpr::Zero(u64::MAX).len(), Some(u64::MAX));
        assert_eq!(
            BlobExpr::cat(bytes(b"abc"), BlobExpr::Zero(2)).len(),
            Some(5)
        );

        // A `Cat` is known only when both operands are.
        let digest = BlobExpr::Blake3(O256::from_bytes(b"blob"));
        assert_eq!(BlobExpr::cat(bytes(b"abc"), digest.clone()).len(), None);
        assert_eq!(BlobExpr::cat(digest.clone(), bytes(b"abc")).len(), None);

        // A closed slice is its width, an open one runs to the end.
        let ten = bytes(b"0123456789");
        assert_eq!(BlobExpr::slice(ten.clone(), 3..9).len(), Some(6));
        assert_eq!(BlobExpr::slice(ten.clone(), 3..).len(), Some(7));
        assert_eq!(BlobExpr::slice(ten.clone(), ..4).len(), Some(4));
        assert_eq!(BlobExpr::slice(ten, ..).len(), Some(10));

        // Slicing something of unknown length is unknown, even when closed:
        // the bounds check has nothing to check against.
        assert_eq!(BlobExpr::slice(digest, 0..32).len(), None);
    }

    /// Constraint 4: out of range denotes nothing, and is never clamped.
    #[test]
    fn out_of_range_slice_denotes_nothing() {
        let two = bytes(b"ab");

        // Not `Some(4)`, and not clamped to `Some(0)`.
        assert_eq!(BlobExpr::slice(two.clone(), 5..9).len(), None);
        assert_eq!(BlobExpr::slice(two.clone(), 5..9).eval(), None);
        // Not clamped to `"b"` either.
        assert_eq!(BlobExpr::slice(two.clone(), 1..4).len(), None);
        assert_eq!(BlobExpr::slice(two.clone(), 1..4).eval(), None);
        // An open end past the blob is out of range too.
        assert_eq!(BlobExpr::slice(two.clone(), 3..).len(), None);
        assert_eq!(BlobExpr::slice(two, 3..).eval(), None);
    }

    /// `BlobRange::span` bypasses `BlobSpan::new`, so a backwards range gets
    /// here. It denotes nothing; it must not panic.
    #[test]
    #[allow(clippy::reversed_empty_ranges, reason = "the rule must survive this")]
    fn backwards_span_is_none_not_a_panic() {
        let ten = bytes(b"0123456789");

        assert_eq!(BlobExpr::slice(ten.clone(), 7..3).len(), None);
        assert_eq!(BlobExpr::slice(ten, 7..3).eval(), None);
    }

    #[test]
    fn whole_span_normalises_away() {
        let ten = bytes(b"0123456789");
        assert_eq!(BlobExpr::slice(ten.clone(), ..), ten);
        assert_eq!(BlobExpr::slice(ten.clone(), 0..), ten);

        // So the two carriers for "the whole blob at `h`" reify alike.
        let hash = O256::from_bytes(b"blob");
        let sliced = BlobSlice::new(hash, ..);
        assert_eq!(sliced.to_expr(), BlobExpr::Blake3(hash));

        // A narrower span does not normalise away.
        assert_ne!(BlobExpr::slice(ten.clone(), 0..9), ten);
    }

    #[test]
    fn evaluation_materialises_what_it_can() {
        assert_eq!(bytes(b"abc").eval(), Some(Bytes::from_static(b"abc")));
        assert_eq!(
            BlobExpr::Zero(3).eval(),
            Some(Bytes::from_static(b"\0\0\0"))
        );
        assert_eq!(
            BlobExpr::cat(bytes(b"ab"), bytes(b"c")).eval(),
            Some(Bytes::from_static(b"abc"))
        );
        assert_eq!(
            BlobExpr::slice(bytes(b"0123456789"), 3..7).eval(),
            Some(Bytes::from_static(b"3456"))
        );
        assert_eq!(
            BlobExpr::slice(bytes(b"0123456789"), 7..).eval(),
            Some(Bytes::from_static(b"789"))
        );

        // A digest is not readable from here.
        assert_eq!(BlobExpr::Blake3(O256::from_bytes(b"abc")).eval(), None);
    }

    /// The budget refuses the work before it is done, so an absurd length is
    /// answered instantly rather than aborting the process.
    #[test]
    fn huge_zero_does_not_allocate() {
        assert_eq!(BlobExpr::Zero(u64::MAX).len(), Some(u64::MAX));
        assert_eq!(BlobExpr::Zero(u64::MAX).eval(), None);
        assert_eq!(BlobExpr::Zero(MAX_EVAL_BYTES + 1).eval(), None);
        // The length is still known, so a disequality is still decidable.
        assert_eq!(
            cmp_length(&BlobExpr::Zero(u64::MAX), &bytes(b"abc")),
            Some(Ordering::Greater)
        );
    }

    /// Constraint 5: `Blake3(h)` is the blob NAMED by `h`, not the digest.
    #[test]
    fn digest_bytes_are_not_the_named_blob() {
        let hash = O256::from_bytes(b"abc");
        let named = BlobExpr::Blake3(hash);
        let digest = BlobExpr::Bytes(Bytes::copy_from_slice(hash.as_bytes()));

        assert_ne!(named, digest);
        assert_eq!(named.len(), None);
        assert_eq!(digest.len(), Some(32));
        assert_eq!(named.eval(), None);
    }

    #[test]
    fn every_carrier_converts_into_the_same_expression() {
        let hash = O256::from_bytes(b"blob");
        assert_eq!(hash.to_expr(), BlobExpr::Blake3(hash));
        assert_eq!(hash.len(), None);
        assert_eq!(hash.eval(), None);

        let raw = Bytes::from_static(b"abc");
        assert_eq!(raw.to_expr(), bytes(b"abc"));
        assert_eq!(BlobLike::len(&raw), Some(3));
        assert_eq!(raw.eval(), Some(raw.clone()));

        let expr = bytes(b"abc");
        assert_eq!(expr.to_expr(), expr);

        let shared = Arc::new(raw.clone());
        assert_eq!(BlobLike::to_expr(&shared), bytes(b"abc"));
        assert_eq!(BlobLike::len(&shared), Some(3));
        assert_eq!(BlobLike::eval(&shared), Some(raw.clone()));

        let slice = BlobSlice::new(raw.clone(), 1..3);
        assert_eq!(slice.to_expr(), BlobExpr::slice(bytes(b"abc"), 1..3));
        assert_eq!(slice.len(), Some(2));
        assert_eq!(slice.eval(), Some(Bytes::from_static(b"bc")));

        let cat = BlobCat::new(hash, raw);
        assert_eq!(
            cat.to_expr(),
            BlobExpr::cat(BlobExpr::Blake3(hash), bytes(b"abc"))
        );
        assert_eq!(cat.len(), None);
        assert_eq!(cat.eval(), None);
        assert_eq!(cat.left(), &hash);
        assert_eq!(cat.right(), &Bytes::from_static(b"abc"));
    }

    /// Structural equality ignores the memo and takes the pointer fast path,
    /// but never confuses two different expressions.
    #[test]
    fn expressions_compare_structurally() {
        let shared = Arc::new(bytes(b"abc"));
        let left = BlobExpr::Cat(BlobCat::new(Arc::clone(&shared), Arc::clone(&shared)));
        let right = BlobExpr::cat(bytes(b"abc"), bytes(b"abc"));
        assert_eq!(left, right);

        assert_ne!(bytes(b"abc"), BlobExpr::Zero(3));
        assert_ne!(BlobExpr::Zero(3), BlobExpr::Zero(4));
        assert_ne!(
            BlobExpr::cat(bytes(b"ab"), bytes(b"c")),
            BlobExpr::cat(bytes(b"a"), bytes(b"bc"))
        );
        assert_ne!(
            BlobExpr::slice(bytes(b"abc"), 0..1),
            BlobExpr::slice(bytes(b"abc"), 0..2)
        );
    }
}
