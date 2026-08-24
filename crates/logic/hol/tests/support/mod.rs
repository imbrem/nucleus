//! Userspace fixtures for the out-of-kernel Ethane test suite.
//!
//! Everything here lives outside the trusted computing base: it drives
//! `covalence-logic-hol` through its public surface only, so a test can never
//! reach a kernel invariant that a real caller could not also reach. The proof
//! search in [`Prover`] is deliberately the sort of thing the kernel refuses to
//! own — it is the userspace side of the row-directed split.

#![allow(dead_code)]

use std::{collections::BTreeSet, convert::Infallible, fmt};

use covalence_lib_cbor::{Value, into_writer};
use covalence_logic_hol::{
    Arena, Kernel, KernelError, Link, Ref, Resolver, SynFact, SynFactId, SynRel, Table, Tag, TmTag,
    TyTag, wire,
};

/// A kernel preloaded with the two rows every other fixture needs.
pub struct Fix {
    pub kernel: Kernel,
    pub star: Ref,
    pub bool_ty: Ref,
}

impl Default for Fix {
    fn default() -> Self {
        Self::new()
    }
}

impl Fix {
    /// Builds `kind.star` and `ty.bool` in a fresh kernel.
    pub fn new() -> Self {
        let mut kernel = Kernel::new();
        let star = kernel.star().expect("star");
        let bool_ty = kernel.bool_ty(star).expect("bool type");
        Self {
            kernel,
            star,
            bool_ty,
        }
    }

    /// A Boolean term variable.
    pub fn var(&mut self, name: u64) -> Ref {
        let bool_ty = self.bool_ty;
        self.kernel.tm_fv(name, bool_ty).expect("term variable")
    }

    /// A Boolean literal.
    pub fn lit(&mut self, value: bool) -> Ref {
        let bool_ty = self.bool_ty;
        self.kernel.bool(bool_ty, value).expect("Boolean literal")
    }

    /// A type variable of kind `star`.
    pub fn ty_var(&mut self, name: u64) -> Ref {
        let star = self.star;
        self.kernel.ty_fv(name, star).expect("type variable")
    }

    /// `bool -> bool`.
    pub fn bool_arrow(&mut self) -> Ref {
        let bool_ty = self.bool_ty;
        self.kernel.ty_arr(bool_ty, bool_ty).expect("bool arrow")
    }

    /// Every currently occupied fact slot, indexed by one-based slot.
    pub fn slots(&self) -> Vec<Option<SynFact>> {
        slots(&self.kernel)
    }

    /// A prover bound to this fixture's `kind.star` row.
    pub fn prover(&self) -> Prover {
        Prover { star: self.star }
    }
}

impl std::ops::Deref for Fix {
    type Target = Kernel;

    fn deref(&self) -> &Self::Target {
        &self.kernel
    }
}

impl std::ops::DerefMut for Fix {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.kernel
    }
}

/// Every fact slot of a kernel, indexed by one-based slot, with removed slots
/// reported as `None`.
pub fn slots(kernel: &Kernel) -> Vec<Option<SynFact>> {
    (1..=kernel.syn_fact_len())
        .map(|position| {
            let id = fact_id(position);
            kernel.syn_fact(id).ok()
        })
        .collect()
}

/// One-based fact slot handle. Panics on zero, which no caller should produce.
pub fn fact_id(position: usize) -> SynFactId {
    SynFactId::new(u64::try_from(position).expect("slot fits in u64")).expect("slots are one-based")
}

/// One-based row handle. Panics on zero, which no caller should produce.
pub fn row_id(position: u64) -> Ref {
    Ref::new(position).expect("rows are one-based")
}

/// Userspace structural proof search over the row-directed kernel.
///
/// The kernel deliberately does not walk syntax trees, so a caller that wants
/// `left = right` for two structurally identical rows has to build the
/// congruence derivation itself. Duplicate rows are unavoidable in practice:
/// every `Kernel::lam` mints a fresh `ty.arr` row for the function type, so a
/// second identical lambda gets a second identical arrow.
#[derive(Clone, Copy)]
pub struct Prover {
    star: Ref,
}

impl Prover {
    pub const fn new(star: Ref) -> Self {
        Self { star }
    }

    /// Proves `left = right` in `rel` by structural congruence, returning the
    /// cached fact.
    ///
    /// Binders are handled without renaming, so this establishes literal
    /// syntactic agreement rather than alpha equivalence.
    pub fn syn_equal(
        self,
        kernel: &mut Kernel,
        rel: SynRel,
        left: Ref,
        right: Ref,
    ) -> Result<SynFactId, KernelError> {
        if left == right {
            return kernel.syn_refl(None, rel, left);
        }
        let tag = kernel
            .arena()
            .tag(left)
            .ok_or(KernelError::MissingDefinition { reference: left })?;
        match tag {
            Tag::Ty(TyTag::Lam) | Tag::Tm(TmTag::Lam) => self.binder(kernel, rel, left, right),
            Tag::Ty(TyTag::Model) | Tag::Tm(TmTag::TyExists) => {
                self.implicit_binder(kernel, rel, left, right)
            }
            _ => self.congruence(kernel, rel, left, right),
        }
    }

    /// Proves `left = right` and records it in the row union-find.
    pub fn union_equal(
        self,
        kernel: &mut Kernel,
        left: Ref,
        right: Ref,
    ) -> Result<(), KernelError> {
        let fact = self.syn_equal(kernel, SynRel::Syn, left, right)?;
        kernel.union_syn_fact(fact)
    }

    fn children(kernel: &Kernel, reference: Ref) -> Result<Vec<Ref>, KernelError> {
        Ok(kernel
            .arena()
            .children(reference)
            .ok_or(KernelError::MissingDefinition { reference })?
            .collect())
    }

    fn congruence(
        self,
        kernel: &mut Kernel,
        rel: SynRel,
        left: Ref,
        right: Ref,
    ) -> Result<SynFactId, KernelError> {
        let inputs = Self::children(kernel, left)?;
        let outputs = Self::children(kernel, right)?;
        if inputs.len() != outputs.len() {
            return Err(KernelError::MissingDefinition { reference: right });
        }
        // Variable rows compare their classifier child literally, never up to
        // conversion, so the child relation is always `syn` beneath one.
        let child_rel = if matches!(
            kernel.arena().tag(left),
            Some(Tag::Ty(TyTag::Fv) | Tag::Tm(TmTag::Fv))
        ) {
            SynRel::Syn
        } else {
            rel
        };
        let mut evidence = Vec::with_capacity(inputs.len());
        for (input, output) in inputs.into_iter().zip(outputs) {
            evidence.push(self.syn_equal(kernel, child_rel, input, output)?);
        }
        kernel.syn_congr(None, rel, None, None, left, right, &evidence)
    }

    fn binder(
        self,
        kernel: &mut Kernel,
        rel: SynRel,
        left: Ref,
        right: Ref,
    ) -> Result<SynFactId, KernelError> {
        let inputs = Self::children(kernel, left)?;
        let outputs = Self::children(kernel, right)?;
        let binder = self.syn_equal(kernel, rel, inputs[0], outputs[0])?;
        let body = self.syn_equal(kernel, rel, inputs[1], outputs[1])?;
        kernel.syn_binder_congr(None, rel, None, None, left, right, binder, body)
    }

    fn implicit_binder(
        self,
        kernel: &mut Kernel,
        rel: SynRel,
        left: Ref,
        right: Ref,
    ) -> Result<SynFactId, KernelError> {
        let name = kernel
            .arena()
            .name(left)
            .ok_or(KernelError::MissingDefinition { reference: left })?;
        let witness = kernel.ty_fv(name, self.star)?;
        let inputs = Self::children(kernel, left)?;
        let outputs = Self::children(kernel, right)?;
        let body = self.syn_equal(kernel, rel, inputs[0], outputs[0])?;
        kernel.syn_implicit_binder_congr(None, rel, None, None, left, right, witness, body)
    }
}

/// Hand-assembled arena CBOR, so a test can present bytes the encoder would
/// never emit.
pub struct ArenaCbor {
    imports: Vec<Value>,
    axs: Vec<Value>,
    defs: Vec<Value>,
    syn_facts: Option<Vec<Value>>,
    syn_free: Option<Value>,
    ctx: Vec<Value>,
    assume: Vec<Value>,
    assert: Vec<Value>,
    extra: Vec<(Value, Value)>,
}

impl Default for ArenaCbor {
    fn default() -> Self {
        Self::new()
    }
}

impl ArenaCbor {
    pub const fn new() -> Self {
        Self {
            imports: Vec::new(),
            axs: Vec::new(),
            defs: Vec::new(),
            syn_facts: None,
            syn_free: None,
            ctx: Vec::new(),
            assume: Vec::new(),
            assert: Vec::new(),
            extra: Vec::new(),
        }
    }

    #[must_use]
    pub fn defs(mut self, rows: Vec<Value>) -> Self {
        self.defs = rows;
        self
    }

    #[must_use]
    pub fn imports(mut self, imports: Vec<Value>) -> Self {
        self.imports = imports;
        self
    }

    #[must_use]
    pub fn axs(mut self, axs: Vec<Value>) -> Self {
        self.axs = axs;
        self
    }

    #[must_use]
    pub fn ctx(mut self, ctx: Vec<Value>) -> Self {
        self.ctx = ctx;
        self
    }

    #[must_use]
    pub fn slots(mut self, slots: Vec<Value>) -> Self {
        self.syn_facts = Some(slots);
        self
    }

    #[must_use]
    pub fn free(mut self, head: Value) -> Self {
        self.syn_free = Some(head);
        self
    }

    /// Adds a field the schema does not define.
    #[must_use]
    pub fn extra(mut self, key: &str, value: Value) -> Self {
        self.extra.push((text(key), value));
        self
    }

    #[must_use]
    pub fn bytes(self) -> Vec<u8> {
        let mut fields = vec![
            (text("tag"), text("arena")),
            (text("imports"), Value::Array(self.imports)),
            (text("axs"), Value::Array(self.axs)),
            (text("defs"), Value::Array(self.defs)),
        ];
        if let Some(slots) = self.syn_facts {
            fields.push((text("syn_facts"), Value::Array(slots)));
        }
        if let Some(free) = self.syn_free {
            fields.push((text("syn_free"), free));
        }
        fields.push((text("ctx"), Value::Array(self.ctx)));
        fields.push((text("assume"), Value::Array(self.assume)));
        fields.push((text("assert"), Value::Array(self.assert)));
        fields.extend(self.extra);
        let mut bytes = Vec::new();
        into_writer(&Value::Map(fields), &mut bytes).expect("hand-built CBOR encodes");
        bytes
    }

    pub fn decode(self) -> Result<Arena, wire::DecodeError> {
        wire::deserialize(self.bytes().as_slice())
    }
}

/// A CBOR text string.
pub fn text(name: &str) -> Value {
    Value::Text(name.into())
}

/// A CBOR unsigned integer.
pub fn int(value: u64) -> Value {
    Value::Integer(value.into())
}

/// A CBOR map.
pub fn map(fields: Vec<(&str, Value)>) -> Value {
    Value::Map(
        fields
            .into_iter()
            .map(|(key, value)| (text(key), value))
            .collect(),
    )
}

/// An occupied fact slot with explicit endpoints and no substitution.
pub fn direct_slot(rel: &str, input: u64, output: u64) -> Value {
    map(vec![
        ("rel", text(rel)),
        ("in", int(input)),
        ("out", int(output)),
    ])
}

/// A free slot pointing at `next`, or the end of the list.
pub fn free_slot(next: Option<u64>) -> Value {
    map(vec![("next", next.map_or(Value::Null, int))])
}

/// The canonical encoding of an arena.
pub fn encode(arena: &Arena) -> Vec<u8> {
    let mut bytes = Vec::new();
    wire::serialize(arena, &mut bytes).expect("arenas encode into memory");
    bytes
}

/// Asserts that an arena survives one encode/decode cycle unchanged.
pub fn assert_round_trips(arena: &Arena) {
    let bytes = encode(arena);
    let decoded = wire::deserialize(bytes.as_slice()).expect("canonical bytes decode");
    assert_eq!(&decoded, arena, "arena changed across a wire round trip");
    assert_eq!(
        encode(&decoded),
        bytes,
        "re-encoding a decoded arena changed its bytes"
    );
}

/// A resolver that always answers with the same table, whatever was asked for.
pub struct Always(pub Table);

impl Resolver for Always {
    type Error = Infallible;

    fn resolve(&mut self, _: &Link) -> Result<Table, Self::Error> {
        Ok(self.0.clone())
    }
}

/// A resolver that must never be consulted.
pub struct Never;

impl Resolver for Never {
    type Error = Infallible;

    fn resolve(&mut self, link: &Link) -> Result<Table, Self::Error> {
        unreachable!("resolver consulted for {link:?}")
    }
}

/// A resolver that counts how often it was asked.
pub struct Counting {
    pub table: Table,
    pub calls: usize,
}

impl Resolver for Counting {
    type Error = Infallible;

    fn resolve(&mut self, _: &Link) -> Result<Table, Self::Error> {
        self.calls += 1;
        Ok(self.table.clone())
    }
}

/// An I/O-style resolver failure.
#[derive(Debug)]
pub struct Unavailable;

impl fmt::Display for Unavailable {
    fn fmt(&self, output: &mut fmt::Formatter<'_>) -> fmt::Result {
        output.write_str("link is unavailable")
    }
}

impl std::error::Error for Unavailable {}

/// A resolver that never succeeds.
pub struct Offline;

impl Resolver for Offline {
    type Error = Unavailable;

    fn resolve(&mut self, _: &Link) -> Result<Table, Self::Error> {
        Err(Unavailable)
    }
}

/// A deterministic, dependency-free generator for randomized state machines.
pub struct Lcg(u64);

impl Lcg {
    pub const fn new(seed: u64) -> Self {
        Self(seed ^ 0x9e37_79b9_7f4a_7c15)
    }

    pub const fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 11
    }

    /// A value in `0..bound`. `bound` must be nonzero.
    pub fn below(&mut self, bound: usize) -> usize {
        let bound = u64::try_from(bound).expect("bounds fit in u64");
        usize::try_from(self.next() % bound).expect("a value below `bound` fits in usize")
    }
}

/// Whether a variable of the given name may occur anywhere beneath `root`,
/// recomputed from outside the kernel over the public row accessors.
///
/// Proxies are opaque, so an import counts as a possible occurrence — the same
/// conservative reading the kernel takes.
pub fn occurs(arena: &Arena, root: Ref, name: u64) -> bool {
    let mut visited = BTreeSet::new();
    let mut pending = vec![root];
    while let Some(reference) = pending.pop() {
        if !visited.insert(reference) {
            continue;
        }
        if arena.foreign(reference).is_some() {
            return true;
        }
        if matches!(
            arena.tag(reference),
            Some(Tag::Ty(TyTag::Fv) | Tag::Tm(TmTag::Fv))
        ) && arena.name(reference) == Some(name)
        {
            return true;
        }
        pending.extend(arena.children(reference).into_iter().flatten());
    }
    false
}

/// Every invariant the kernel promises about an occupied fact slot, checked
/// from outside the kernel.
///
/// A caller can only obtain a [`SynFact`] that some LCF rule minted, so these
/// have to hold for every slot of every kernel, whatever sequence of rules
/// produced it.
pub fn assert_cache_invariants(kernel: &Kernel) {
    for (position, slot) in slots(kernel).into_iter().enumerate() {
        let Some(fact) = slot else { continue };
        let id = fact_id(position + 1);
        assert!(
            fact.var().is_some() || fact.val().is_none(),
            "{id:?}: a replacement with no variable escaped a checked rule"
        );
        if let Some(var) = fact.var() {
            assert!(
                matches!(
                    kernel.arena().tag(var),
                    Some(Tag::Ty(TyTag::Fv) | Tag::Tm(TmTag::Fv))
                ),
                "{id:?}: substitution target {var:?} is not a free variable row"
            );
            if let Some(val) = fact.val() {
                assert_eq!(
                    kernel.category(var).expect("resident"),
                    kernel.category(val).expect("resident"),
                    "{id:?}: replacement changes syntactic category"
                );
            } else {
                // A universal fact quantifies over every compatible
                // replacement, so it can only be true of an input the variable
                // does not reach. Every rule that mints one preserves this, but
                // no single rule checks it, so it is worth pinning from here.
                let name = kernel
                    .arena()
                    .name(var)
                    .expect("a free-variable row carries a name");
                assert!(
                    !occurs(kernel.arena(), fact.input(), name),
                    "{id:?}: a universal fact mentions the variable it quantifies over"
                );
            }
        }
        let input = kernel.category(fact.input()).expect("resident input");
        let output = kernel.category(fact.output()).expect("resident output");
        assert_eq!(input, output, "{id:?}: endpoints span two categories");
        if input != covalence_logic_hol::Sort::Kind {
            let left = kernel.classifier(fact.input()).expect("classified input");
            let right = kernel.classifier(fact.output()).expect("classified output");
            assert!(
                kernel
                    .equivalent(left, right)
                    .expect("resident classifiers"),
                "{id:?}: endpoints carry unrelated classifiers"
            );
        }
    }
}
