//! Small checked rules for the arena's syntactic-fact cache.
//!
//! Lookup policy and proof search are intentionally absent. Userspace may
//! index these slots however it likes and may discard temporary suffixes.

use std::{
    collections::{BTreeMap, BTreeSet},
    convert::Infallible,
};

use crate::{EqColumn, Ref, Sort, SynFact, SynFactId, SynRel, init::Compiled, row::Expr as Node};

use super::{Kernel, KernelError};

impl Kernel {
    /// Records that a compact logical opcode is syntactically equal to its
    /// canonical opcode-free init expansion.
    ///
    /// `target` replaces that one-based slot when present; `None` allocates.
    /// The expansion is appended to this kernel using the named definition in
    /// `init`, exactly as in [`Kernel::lower_logical`].
    ///
    /// # Errors
    ///
    /// Returns an error if the source is not a logical opcode row, the init
    /// prefix is absent or mismatched, checked lowering fails, or the
    /// replacement slot is absent.
    pub fn logical_lower_fact(
        &mut self,
        target: Option<SynFactId>,
        init: &Compiled,
        source: Ref,
    ) -> Result<SynFactId, KernelError> {
        let expansion = self.lower_logical(init, source)?;
        self.require_compatible_endpoints::<Infallible>(source, expansion, false)?;
        self.put_fact(
            target,
            SynFact::new(SynRel::Syn, None, None, source, expansion),
        )
    }

    /// Number of allocated syntactic-fact slots, including removed slots.
    #[must_use]
    pub fn syn_fact_len(&self) -> usize {
        self.arena.syn_fact_slot_count()
    }

    /// Returns one checked syntactic fact.
    ///
    /// # Errors
    ///
    /// Returns an error if the one-based slot is absent or was removed.
    pub fn syn_fact(&self, id: SynFactId) -> Result<SynFact, KernelError> {
        self.fact::<Infallible>(id)
    }

    /// Removes one cached fact. Removing evidence cannot add a theorem.
    #[must_use]
    pub fn remove_syn_fact(&mut self, id: SynFactId) -> bool {
        self.arena.remove_syn_fact(id)
    }

    /// Retains the first `len` syntactic-fact slots and drops the rest.
    ///
    /// This supports temporary userspace proof searches without putting a
    /// cache or garbage collector in the trusted kernel.
    pub fn truncate_syn_facts(&mut self, len: usize) {
        self.arena.truncate_syn_facts(len);
    }

    /// Inserts reflexivity in any of the three nested relations.
    ///
    /// `target` replaces that one-based slot when present; `None` allocates.
    ///
    /// # Errors
    ///
    /// Returns an error if the expression or replacement slot is absent.
    pub fn syn_refl(
        &mut self,
        target: Option<SynFactId>,
        rel: SynRel,
        input: Ref,
    ) -> Result<SynFactId, KernelError> {
        self.row::<Infallible>(input)?;
        self.put_fact::<Infallible>(target, SynFact::new(rel, None, None, input, input))
    }

    /// Weakens a fact along `syn ≤ alpha ≤ conv`.
    ///
    /// # Errors
    ///
    /// Returns an error unless the source relation refines `rel`.
    pub fn syn_refine(
        &mut self,
        target: Option<SynFactId>,
        source: SynFactId,
        rel: SynRel,
    ) -> Result<SynFactId, KernelError> {
        let fact = self.fact::<Infallible>(source)?;
        if !fact.rel().refines(rel) {
            return Err(Self::invalid_fact("relation refinement"));
        }
        self.put_fact(
            target,
            SynFact::new(rel, fact.var(), fact.val(), fact.input(), fact.output()),
        )
    }

    /// Reverses a direct fact.
    ///
    /// # Errors
    ///
    /// Returns an error for an active substitution fact.
    pub fn syn_symm(
        &mut self,
        target: Option<SynFactId>,
        source: SynFactId,
    ) -> Result<SynFactId, KernelError> {
        let fact = self.direct_fact::<Infallible>(source, "symmetry")?;
        self.put_fact(
            target,
            SynFact::new(fact.rel(), None, None, fact.output(), fact.input()),
        )
    }

    /// Composes any checked left fact with a direct right fact, choosing the
    /// coarser input relation and preserving the left substitution endpoints.
    ///
    /// # Errors
    ///
    /// Returns an error unless the middle references agree exactly.
    pub fn syn_trans(
        &mut self,
        target: Option<SynFactId>,
        left: SynFactId,
        right: SynFactId,
    ) -> Result<SynFactId, KernelError> {
        let left = self.fact::<Infallible>(left)?;
        let right = self.direct_fact::<Infallible>(right, "transitivity")?;
        if left.output() != right.input() {
            return Err(Self::invalid_fact("transitivity"));
        }
        let rel = if left.rel().refines(right.rel()) {
            right.rel()
        } else if right.rel().refines(left.rel()) {
            left.rel()
        } else {
            return Err(Self::invalid_fact("transitivity"));
        };
        self.put_fact(
            target,
            SynFact::new(rel, left.var(), left.val(), left.input(), right.output()),
        )
    }

    /// Establishes the variable case `[val / var] var = val`.
    ///
    /// # Errors
    ///
    /// Returns an error unless `var` is a free variable and `val` has its
    /// syntactic category and a compatible classifier.
    pub fn syn_sub_var(
        &mut self,
        target: Option<SynFactId>,
        var: Ref,
        val: Ref,
    ) -> Result<SynFactId, KernelError> {
        self.require_substitution_pair::<Infallible>(var, val)?;
        self.put_fact(
            target,
            SynFact::new(SynRel::Syn, Some(var), Some(val), var, val),
        )
    }

    /// Establishes that substitution leaves one non-target leaf unchanged.
    ///
    /// # Errors
    ///
    /// Returns an error unless `input` is a literal leaf or a distinct free
    /// variable. An import proxy is opaque: callers must instead supply a
    /// checked universal fact obtained from theorem-import machinery.
    pub fn syn_sub_leaf(
        &mut self,
        target: Option<SynFactId>,
        var: Ref,
        val: Ref,
        input: Ref,
    ) -> Result<SynFactId, KernelError> {
        self.require_substitution_pair::<Infallible>(var, val)?;
        self.require_substitution_leaf::<Infallible>(var, input)?;
        self.put_fact(
            target,
            SynFact::new(SynRel::Syn, Some(var), Some(val), input, input),
        )
    }

    /// Returns whether raw named syntax proves `var` absent from `input`.
    ///
    /// This is deliberately conservative around import proxies: an opaque
    /// row may resolve to the variable, so it is never reported fresh. Local
    /// duplicate syntax is compared structurally rather than by row identity.
    ///
    /// # Errors
    ///
    /// Returns an error unless `var` is a local free variable and `input` is a
    /// resident local row.
    pub fn substitution_fresh(&self, var: Ref, input: Ref) -> Result<bool, KernelError> {
        self.require_substitution_variable::<Infallible>(var)?;
        self.row::<Infallible>(input)?;
        Ok(!self.may_contain_variable_as::<Infallible>(input, var)?)
    }

    /// Establishes that substitution leaves one fresh expression unchanged.
    ///
    /// Unlike [`syn_sub_leaf`](Self::syn_sub_leaf), this rule accepts an
    /// arbitrary compound expression after checking the substituted variable
    /// is absent from its complete raw named syntax. It is the executable
    /// counterpart of `NamedSubstitution.miss` in the Lean model.
    ///
    /// # Errors
    ///
    /// Returns an error unless `var` and `val` form a valid substitution pair
    /// and [`substitution_fresh`](Self::substitution_fresh) holds for `input`.
    pub fn syn_sub_fresh(
        &mut self,
        target: Option<SynFactId>,
        var: Ref,
        val: Ref,
        input: Ref,
    ) -> Result<SynFactId, KernelError> {
        self.require_substitution_pair::<Infallible>(var, val)?;
        if self.may_contain_variable_as::<Infallible>(input, var)? {
            return Err(Self::invalid_fact("fresh substitution"));
        }
        self.put_fact(
            target,
            SynFact::new(SynRel::Syn, Some(var), Some(val), input, input),
        )
    }

    /// Establishes that every compatible substitution leaves one
    /// non-target leaf unchanged.
    ///
    /// # Errors
    ///
    /// Returns an error unless `var` is a free variable and `input` is a
    /// literal leaf or a free variable with a distinct name.
    pub fn syn_sub_leaf_forall(
        &mut self,
        target: Option<SynFactId>,
        var: Ref,
        input: Ref,
    ) -> Result<SynFactId, KernelError> {
        self.require_substitution_variable::<Infallible>(var)?;
        self.require_substitution_leaf::<Infallible>(var, input)?;
        self.put_fact(
            target,
            SynFact::new(SynRel::Syn, Some(var), None, input, input),
        )
    }

    /// Uses a direct syntactic equality `var = val` to disable substitution.
    ///
    /// # Errors
    ///
    /// Returns an error unless `variable_equality` and `body_equality` are
    /// direct syntactic facts with the requested endpoints.
    #[allow(clippy::too_many_arguments)]
    pub fn syn_sub_identity(
        &mut self,
        target: Option<SynFactId>,
        var: Ref,
        val: Ref,
        input: Ref,
        output: Ref,
        variable_equality: SynFactId,
        body_equality: SynFactId,
    ) -> Result<SynFactId, KernelError> {
        self.require_substitution_pair::<Infallible>(var, val)?;
        self.require_direct::<Infallible>(
            variable_equality,
            SynRel::Syn,
            var,
            val,
            "identity substitution",
        )?;
        let body = self.direct_fact::<Infallible>(body_equality, "identity substitution")?;
        if body.input() != input || body.output() != output {
            return Err(Self::invalid_fact("identity substitution"));
        }
        self.put_fact(
            target,
            SynFact::new(body.rel(), Some(var), Some(val), input, output),
        )
    }

    /// Applies congruence to a non-binding constructor.
    ///
    /// Child facts must have the same substitution endpoints and relate the
    /// corresponding input and output children. Finer child relations may be
    /// used for a coarser parent relation.
    ///
    /// # Errors
    ///
    /// Returns an error for a binder, different constructor data, or
    /// mismatched child evidence.
    #[allow(clippy::too_many_arguments)]
    pub fn syn_congr(
        &mut self,
        target: Option<SynFactId>,
        rel: SynRel,
        var: Option<Ref>,
        val: Option<Ref>,
        input: Ref,
        output: Ref,
        children: &[SynFactId],
    ) -> Result<SynFactId, KernelError> {
        self.require_optional_substitution::<Infallible>(var, val)?;
        let input_node = *self.row::<Infallible>(input)?.expr();
        let output_node = *self.row::<Infallible>(output)?.expr();
        if Self::is_binder(input_node)
            || Self::is_binder(output_node)
            || !Self::same_head(input_node, output_node)
            || (var.is_some() && Self::is_proxy(input_node))
        {
            return Err(Self::invalid_fact("constructor congruence"));
        }
        if var.is_some_and(|var| {
            self.row::<Infallible>(var)
                .is_ok_and(|row| Self::same_variable_name(*row.expr(), input_node))
        }) {
            return Err(Self::invalid_fact("constructor congruence"));
        }
        let child_rel = if Self::is_variable(input_node) {
            SynRel::Syn
        } else {
            rel
        };
        self.require_children::<Infallible>(
            child_rel,
            var,
            val,
            &input_node.children(),
            &output_node.children(),
            children,
            "constructor congruence",
        )?;
        self.require_compatible_endpoints::<Infallible>(input, output, var.is_some())?;
        self.put_fact(target, SynFact::new(rel, var, val, input, output))
    }

    /// Applies congruence beneath an explicit binder without renaming it.
    ///
    /// The replacement must not mention a binder it crosses.
    ///
    /// # Errors
    ///
    /// Returns an error unless the binder and body facts match the local
    /// substitution rule exactly.
    #[allow(clippy::too_many_arguments)]
    pub fn syn_binder_congr(
        &mut self,
        target: Option<SynFactId>,
        rel: SynRel,
        var: Option<Ref>,
        val: Option<Ref>,
        input: Ref,
        output: Ref,
        binder: SynFactId,
        body: SynFactId,
    ) -> Result<SynFactId, KernelError> {
        self.require_optional_substitution::<Infallible>(var, val)?;
        let input_node = *self.row::<Infallible>(input)?.expr();
        let output_node = *self.row::<Infallible>(output)?.expr();
        let shape = Self::binder_shape::<Infallible>(input_node, output_node)?;
        let body_substitution =
            self.binder_substitution::<Infallible>(shape.input_binder, var, val)?;
        let substitution_through_term_binder = if let (Some(var), Node::Lam(..)) = (var, input_node)
        {
            let classifier = self.classifier_as::<Infallible>(shape.input_binder)?;
            self.may_contain_variable_as::<Infallible>(classifier, var)?
        } else {
            false
        };
        let binder_substitution = if substitution_through_term_binder {
            let binder_fact = self.fact::<Infallible>(binder)?;
            if binder_fact.var() != var || binder_fact.val() != val {
                return Err(Self::invalid_fact("binder classifier"));
            }
            if !Self::same_variable_name(
                *self.row::<Infallible>(shape.input_binder)?.expr(),
                *self.row::<Infallible>(shape.output_binder)?.expr(),
            ) {
                return Err(Self::invalid_fact("binder congruence"));
            }
            (var, val)
        } else {
            if !self.same_variable::<Infallible>(shape.input_binder, shape.output_binder)? {
                return Err(Self::invalid_fact("binder congruence"));
            }
            // The binder annotation is out of reach and is carried through
            // unchanged. A `ty.lam` binder carries a kind, which cannot
            // contain either kind of substituted variable.
            (None, None)
        };
        self.require_fact_match::<Infallible>(
            binder,
            rel,
            binder_substitution.0,
            binder_substitution.1,
            shape.input_binder,
            shape.output_binder,
            "binder congruence",
        )?;
        self.require_fact_match::<Infallible>(
            body,
            rel,
            body_substitution.0,
            body_substitution.1,
            shape.input_body,
            shape.output_body,
            "binder congruence",
        )?;
        self.require_compatible_endpoints::<Infallible>(input, output, var.is_some())?;
        self.put_fact(target, SynFact::new(rel, var, val, input, output))
    }

    /// Applies congruence beneath the implicit type binder of `Model` or
    /// `tyExists` without renaming it.
    ///
    /// `binder` is an explicit `ty.fv` witness for the stored binder name.
    /// Conversion congruence is deliberately unavailable under `Model`.
    ///
    /// # Errors
    ///
    /// Returns an error unless the witness and body fact match the local rule
    /// and the replacement is fresh for a binder it crosses.
    #[allow(clippy::too_many_arguments)]
    pub fn syn_implicit_binder_congr(
        &mut self,
        target: Option<SynFactId>,
        rel: SynRel,
        var: Option<Ref>,
        val: Option<Ref>,
        input: Ref,
        output: Ref,
        binder: Ref,
        body: SynFactId,
    ) -> Result<SynFactId, KernelError> {
        self.require_optional_substitution::<Infallible>(var, val)?;
        let input_node = *self.row::<Infallible>(input)?.expr();
        let output_node = *self.row::<Infallible>(output)?.expr();
        let (name, input_body, output_body, is_model) =
            Self::same_implicit_binder(input_node, output_node)
                .ok_or_else(|| Self::invalid_fact("implicit binder congruence"))?;
        if is_model && rel == SynRel::Conv {
            return Err(Self::invalid_fact("conversion under model"));
        }
        self.require_implicit_binder::<Infallible>(binder, name)?;
        let body_substitution = self.binder_substitution::<Infallible>(binder, var, val)?;
        self.require_fact_match::<Infallible>(
            body,
            rel,
            body_substitution.0,
            body_substitution.1,
            input_body,
            output_body,
            "implicit binder congruence",
        )?;
        self.require_compatible_endpoints::<Infallible>(input, output, var.is_some())?;
        self.put_fact(target, SynFact::new(rel, var, val, input, output))
    }

    /// Renames an explicit `ty.lam` or `tm.lam` binder using one substitution
    /// fact for the body.
    ///
    /// # Errors
    ///
    /// Returns an error unless the new binder is fresh in the old body and
    /// the supplied facts establish the classifier and body obligations.
    pub fn syn_alpha_binder(
        &mut self,
        target: Option<SynFactId>,
        input: Ref,
        output: Ref,
        binder_classifier: SynFactId,
        body_substitution: SynFactId,
    ) -> Result<SynFactId, KernelError> {
        let input_node = *self.row::<Infallible>(input)?.expr();
        let output_node = *self.row::<Infallible>(output)?.expr();
        let shape = Self::binder_shape::<Infallible>(input_node, output_node)?;
        let left_binder = shape.input_binder;
        let right_binder = shape.output_binder;
        let left_classifier = self.classifier_as::<Infallible>(left_binder)?;
        let right_classifier = self.classifier_as::<Infallible>(right_binder)?;
        self.require_direct::<Infallible>(
            binder_classifier,
            SynRel::Alpha,
            left_classifier,
            right_classifier,
            "explicit alpha binder",
        )?;
        self.require_fact_match::<Infallible>(
            body_substitution,
            SynRel::Alpha,
            Some(left_binder),
            Some(right_binder),
            shape.input_body,
            shape.output_body,
            "explicit alpha binder",
        )?;
        if !self.same_variable::<Infallible>(left_binder, right_binder)?
            && self.contains_variable::<Infallible>(shape.input_body, right_binder)?
        {
            return Err(Self::invalid_fact("explicit alpha binder freshness"));
        }
        self.require_compatible_endpoints::<Infallible>(input, output, false)?;
        self.put_fact(
            target,
            SynFact::new(SynRel::Alpha, None, None, input, output),
        )
    }

    /// Alpha-renames the implicit type binder of `Model` or `tyExists`.
    ///
    /// # Errors
    ///
    /// Returns an error unless the explicit binder witnesses match the stored
    /// names, the new binder is fresh, and the body substitution is proved.
    #[allow(clippy::too_many_arguments)]
    pub fn syn_alpha_implicit_binder(
        &mut self,
        target: Option<SynFactId>,
        input: Ref,
        output: Ref,
        input_binder: Ref,
        output_binder: Ref,
        body_substitution: SynFactId,
    ) -> Result<SynFactId, KernelError> {
        let input_node = *self.row::<Infallible>(input)?.expr();
        let output_node = *self.row::<Infallible>(output)?.expr();
        let (left_name, left_body, right_name, right_body) =
            Self::renamed_implicit_binder(input_node, output_node)
                .ok_or_else(|| Self::invalid_fact("implicit alpha binder"))?;
        self.require_implicit_binder::<Infallible>(input_binder, left_name)?;
        self.require_implicit_binder::<Infallible>(output_binder, right_name)?;
        self.require_fact_match::<Infallible>(
            body_substitution,
            SynRel::Alpha,
            Some(input_binder),
            Some(output_binder),
            left_body,
            right_body,
            "implicit alpha binder",
        )?;
        if !self.same_variable::<Infallible>(input_binder, output_binder)?
            && self.contains_variable::<Infallible>(left_body, output_binder)?
        {
            return Err(Self::invalid_fact("implicit alpha binder freshness"));
        }
        self.require_compatible_endpoints::<Infallible>(input, output, false)?;
        self.put_fact(
            target,
            SynFact::new(SynRel::Alpha, None, None, input, output),
        )
    }

    /// Introduces a root type-family beta conversion from a cached
    /// substitution fact.
    ///
    /// # Errors
    ///
    /// Returns an error unless `source` is `(ty.lam binder body) argument`
    /// and the evidence relates `[argument / binder] body` to its output.
    pub fn ty_beta_fact(
        &mut self,
        target: Option<SynFactId>,
        source: Ref,
        substitution: SynFactId,
    ) -> Result<SynFactId, KernelError> {
        self.require_category::<Infallible>(source, Sort::Ty)?;
        let Node::TyApp(function, argument) = *self.row::<Infallible>(source)?.expr() else {
            return Err(Self::invalid_fact("type beta"));
        };
        let Node::TyLam(binder, body) = *self.row::<Infallible>(function)?.expr() else {
            return Err(Self::invalid_fact("type beta"));
        };
        let fact = self.fact::<Infallible>(substitution)?;
        self.require_fact_match::<Infallible>(
            substitution,
            SynRel::Conv,
            Some(binder),
            Some(argument),
            body,
            fact.output(),
            "type beta",
        )?;
        self.require_compatible_endpoints::<Infallible>(source, fact.output(), false)?;
        self.put_fact(
            target,
            SynFact::new(SynRel::Conv, None, None, source, fact.output()),
        )
    }

    /// Introduces a root term beta conversion from a cached substitution fact.
    ///
    /// # Errors
    ///
    /// Returns an error unless `source` is `(lam binder body) argument` and
    /// the evidence relates `[argument / binder] body` to its output.
    pub fn tm_beta_fact(
        &mut self,
        target: Option<SynFactId>,
        source: Ref,
        substitution: SynFactId,
    ) -> Result<SynFactId, KernelError> {
        self.require_category::<Infallible>(source, Sort::Tm)?;
        let Node::App(function, argument) = *self.row::<Infallible>(source)?.expr() else {
            return Err(Self::invalid_fact("term beta"));
        };
        let Node::Lam(binder, body) = *self.row::<Infallible>(function)?.expr() else {
            return Err(Self::invalid_fact("term beta"));
        };
        let fact = self.fact::<Infallible>(substitution)?;
        self.require_fact_match::<Infallible>(
            substitution,
            SynRel::Conv,
            Some(binder),
            Some(argument),
            body,
            fact.output(),
            "term beta",
        )?;
        self.require_compatible_endpoints::<Infallible>(source, fact.output(), false)?;
        self.put_fact(
            target,
            SynFact::new(SynRel::Conv, None, None, source, fact.output()),
        )
    }

    /// Introduces the exact root eta conversion `lam x (f x) = f`.
    ///
    /// Alpha variants are obtained by composing cached facts in userspace.
    ///
    /// # Errors
    ///
    /// Returns an error unless the argument is the binder and the binder does
    /// not occur in `f`.
    pub fn tm_eta_fact(
        &mut self,
        target: Option<SynFactId>,
        source: Ref,
    ) -> Result<SynFactId, KernelError> {
        self.require_category::<Infallible>(source, Sort::Tm)?;
        let Node::Lam(binder, body) = *self.row::<Infallible>(source)?.expr() else {
            return Err(Self::invalid_fact("term eta"));
        };
        let Node::App(function, argument) = *self.row::<Infallible>(body)?.expr() else {
            return Err(Self::invalid_fact("term eta"));
        };
        if !self.same_variable::<Infallible>(binder, argument)?
            || self.contains_variable::<Infallible>(function, binder)?
        {
            return Err(Self::invalid_fact("term eta"));
        }
        self.require_compatible_endpoints::<Infallible>(source, function, false)?;
        self.put_fact(
            target,
            SynFact::new(SynRel::Conv, None, None, source, function),
        )
    }

    /// Records one direct syntactic fact in the row equality union-find.
    ///
    /// # Errors
    ///
    /// Returns an error for an active substitution fact.
    pub fn union_syn_fact(&mut self, fact: SynFactId) -> Result<(), KernelError> {
        let fact = self.direct_fact::<Infallible>(fact, "equality union")?;
        // Install the coarsest relation first.  Besides mirroring the
        // refinement chain `syn ⊆ conv ⊆ semantic`, this keeps every
        // observable error state sound: a later conversion or syntactic
        // union may fail without leaving a finer cache edge unsupported by
        // its coarser relation.
        self.union::<Infallible>(fact.input(), fact.output())?;
        self.union_in::<Infallible>(EqColumn::Conv, fact.input(), fact.output())?;
        if fact.rel() == SynRel::Syn {
            self.union_in::<Infallible>(EqColumn::Syn, fact.input(), fact.output())?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy)]
struct BinderShape {
    input_binder: Ref,
    output_binder: Ref,
    input_body: Ref,
    output_body: Ref,
}

impl Kernel {
    fn invalid_fact<E>(rule: &'static str) -> KernelError<E>
    where
        E: std::error::Error + 'static,
    {
        KernelError::InvalidSynFact { rule }
    }

    pub(super) fn fact<E>(&self, id: SynFactId) -> Result<SynFact, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let fact = self
            .arena
            .syn_fact(id)
            .ok_or(KernelError::MissingSynFact { id })?;
        if fact.var().is_none() && fact.val().is_some() {
            return Err(Self::invalid_fact("reserved substitution endpoints"));
        }
        Ok(fact)
    }

    fn direct_fact<E>(&self, id: SynFactId, rule: &'static str) -> Result<SynFact, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let fact = self.fact(id)?;
        if fact.var().is_some() || fact.val().is_some() {
            return Err(Self::invalid_fact(rule));
        }
        Ok(fact)
    }

    fn put_fact<E>(
        &mut self,
        target: Option<SynFactId>,
        fact: SynFact,
    ) -> Result<SynFactId, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        if let Some(target) = target {
            if self.arena.replace_syn_fact(target, fact) {
                return Ok(target);
            }
            return Err(KernelError::MissingSynFact { id: target });
        }
        self.arena
            .push_syn_fact(fact)
            .ok_or(KernelError::TooManySynFacts)
    }

    fn require_direct<E>(
        &self,
        evidence: SynFactId,
        rel: SynRel,
        input: Ref,
        output: Ref,
        rule: &'static str,
    ) -> Result<(), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let fact = self.direct_fact(evidence, rule)?;
        if !fact.rel().refines(rel) || fact.input() != input || fact.output() != output {
            return Err(Self::invalid_fact(rule));
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn require_fact_match<E>(
        &self,
        evidence: SynFactId,
        rel: SynRel,
        var: Option<Ref>,
        val: Option<Ref>,
        input: Ref,
        output: Ref,
        rule: &'static str,
    ) -> Result<(), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let fact = self.fact(evidence)?;
        if !fact.rel().refines(rel)
            || fact.var() != var
            || fact.val() != val
            || fact.input() != input
            || fact.output() != output
        {
            return Err(Self::invalid_fact(rule));
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn require_children<E>(
        &self,
        rel: SynRel,
        var: Option<Ref>,
        val: Option<Ref>,
        inputs: &[Ref],
        outputs: &[Ref],
        evidence: &[SynFactId],
        rule: &'static str,
    ) -> Result<(), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        if inputs.len() != outputs.len() || inputs.len() != evidence.len() {
            return Err(Self::invalid_fact(rule));
        }
        for ((input, output), fact) in inputs.iter().zip(outputs).zip(evidence) {
            self.require_fact_match(*fact, rel, var, val, *input, *output, rule)?;
        }
        Ok(())
    }

    fn require_optional_substitution<E>(
        &self,
        var: Option<Ref>,
        val: Option<Ref>,
    ) -> Result<(), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        match (var, val) {
            (Some(var), Some(val)) => self.require_substitution_pair(var, val)?,
            (Some(var), None) => {
                self.require_substitution_variable(var)?;
            }
            (None, None) => {}
            _ => return Err(Self::invalid_fact("partial substitution")),
        }
        Ok(())
    }

    fn require_substitution_variable<E>(&self, var: Ref) -> Result<Sort, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let var_node = *self.row::<E>(var)?.expr();
        if !Self::is_variable(var_node) {
            return Err(Self::invalid_fact("substitution variable"));
        }
        self.category_as::<E>(var)
    }

    fn require_substitution_pair<E>(&self, var: Ref, val: Ref) -> Result<(), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let category = self.require_substitution_variable::<E>(var)?;
        self.require_category::<E>(val, category)?;
        if category != Sort::Kind {
            let var_classifier = self.classifier_as::<E>(var)?;
            let replacement_classifier = self.classifier_as::<E>(val)?;
            if !self.equivalent_as::<E>(var_classifier, replacement_classifier)? {
                return Err(KernelError::ClassifierMismatch {
                    expected: var_classifier,
                    actual: replacement_classifier,
                });
            }
        }
        Ok(())
    }

    /// Whether `[… / var] input` leaves the leaf row `input` untouched.
    ///
    /// A different name is not enough on its own: a `tm.fv` row carries its
    /// type, and `ty.model` puts a term inside a type, so the classifier can
    /// mention the variable being replaced. A `ty.fv` row carries a kind, and
    /// kinds contain no named syntax at any depth, so nothing there can change.
    fn require_substitution_leaf<E>(&self, var: Ref, input: Ref) -> Result<(), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let node = *self.row::<E>(input)?.expr();
        if matches!(node, Node::KindStar | Node::BoolTy | Node::Bool(_)) {
            return Ok(());
        }
        let var_node = *self.row::<E>(var)?.expr();
        if !Self::is_variable(node) || Self::same_variable_name(var_node, node) {
            return Err(Self::invalid_fact("substitution leaf"));
        }
        if matches!(node, Node::TyFv { .. }) {
            return Ok(());
        }
        let classifier = self.classifier_as::<E>(input)?;
        if self.contains_variable::<E>(classifier, var)? {
            return Err(Self::invalid_fact("substitution leaf"));
        }
        Ok(())
    }

    /// Conservative raw-syntax occurrence check used by `syn_sub_fresh`.
    ///
    /// Two local rows may denote the same syntax without sharing a `Ref`, so
    /// variable classifiers are compared recursively. Any import proxy is
    /// treated as a possible match because this kernel does not own its bytes.
    fn may_contain_variable_as<E>(&self, input: Ref, var: Ref) -> Result<bool, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let needle = *self.row::<E>(var)?.expr();
        let mut pending = vec![input];
        let mut visited = BTreeSet::new();
        let mut syntax = BTreeMap::new();
        while let Some(reference) = pending.pop() {
            if !visited.insert(reference) {
                continue;
            }
            let node = *self.row::<E>(reference)?.expr();
            if Self::is_proxy(node) {
                return Ok(true);
            }
            let same_variable = match (needle, node) {
                (
                    Node::TyFv {
                        name: needle_name,
                        kind: needle_kind,
                    },
                    Node::TyFv { name, kind },
                ) if needle_name == name => {
                    self.may_same_syntax::<E>(needle_kind, kind, &mut syntax)?
                }
                (
                    Node::TmFv {
                        name: needle_name,
                        ty: needle_ty,
                    },
                    Node::TmFv { name, ty },
                ) if needle_name == name => {
                    self.may_same_syntax::<E>(needle_ty, ty, &mut syntax)?
                }
                _ => false,
            };
            if same_variable {
                return Ok(true);
            }
            pending.extend(node.children());
        }
        Ok(false)
    }

    /// Whether two local subtrees may resolve to identical raw syntax.
    ///
    /// `false` is a proof of constructor or child inequality. Proxies yield
    /// `true` unless their exact payloads match, conservatively preserving the
    /// soundness of the freshness result.
    fn may_same_syntax<E>(
        &self,
        left: Ref,
        right: Ref,
        memo: &mut BTreeMap<(Ref, Ref), bool>,
    ) -> Result<bool, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        if left == right {
            return Ok(true);
        }
        if let Some(&same) = memo.get(&(left, right)) {
            return Ok(same);
        }
        let left_node = *self.row::<E>(left)?.expr();
        let right_node = *self.row::<E>(right)?.expr();
        if Self::is_proxy(left_node) || Self::is_proxy(right_node) {
            memo.insert((left, right), true);
            return Ok(true);
        }
        let same_head = match (left_node, right_node) {
            (Node::KindStar, Node::KindStar)
            | (Node::BoolTy, Node::BoolTy)
            | (Node::KindArr(..), Node::KindArr(..))
            | (Node::TyArr(..), Node::TyArr(..))
            | (Node::TyApp(..), Node::TyApp(..))
            | (Node::TyLam(..), Node::TyLam(..))
            | (Node::App(..), Node::App(..))
            | (Node::Lam(..), Node::Lam(..))
            | (Node::Eq(..), Node::Eq(..))
            | (Node::Eps { .. }, Node::Eps { .. }) => true,
            (Node::TyFv { name: left, .. }, Node::TyFv { name: right, .. })
            | (Node::TmFv { name: left, .. }, Node::TmFv { name: right, .. })
            | (Node::TyExists { name: left, .. }, Node::TyExists { name: right, .. })
            | (Node::TyForall { name: left, .. }, Node::TyForall { name: right, .. })
            | (Node::Model { name: left, .. }, Node::Model { name: right, .. }) => left == right,
            (Node::Bool(left), Node::Bool(right)) => left == right,
            (Node::Op1(left, ..), Node::Op1(right, ..)) => left.code() == right.code(),
            (Node::Op2(left, ..), Node::Op2(right, ..)) => left.code() == right.code(),
            _ => false,
        };
        if !same_head {
            memo.insert((left, right), false);
            return Ok(false);
        }
        // Mark optimistically before recursion; local syntax is a backwards
        // DAG, but this also makes malformed private cycles terminate.
        memo.insert((left, right), true);
        let left_children = left_node.children();
        let right_children = right_node.children();
        if left_children.len() != right_children.len() {
            memo.insert((left, right), false);
            return Ok(false);
        }
        for (left_child, right_child) in left_children.into_iter().zip(right_children) {
            if !self.may_same_syntax::<E>(left_child, right_child, memo)? {
                memo.insert((left, right), false);
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn require_compatible_endpoints<E>(
        &self,
        input: Ref,
        output: Ref,
        substitution: bool,
    ) -> Result<(), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let category = self.category_as::<E>(input)?;
        self.require_category::<E>(output, category)?;
        // Direct syntactic relations preserve a row's classifier. An active
        // substitution is different: its recursively checked child facts may
        // rewrite the classifier itself, for example
        // `[bool / α] (x : α) = (x : bool)`. Requiring the endpoints to be in
        // one semantic type class here would make type substitution unable to
        // enter any term. The constructor and child checks above establish the
        // exact classifier transformation; this final check only needs to
        // preserve the syntactic category in that case.
        if category != Sort::Kind && !substitution {
            let input_classifier = self.classifier_as::<E>(input)?;
            let output_classifier = self.classifier_as::<E>(output)?;
            if !self.equivalent_as::<E>(input_classifier, output_classifier)? {
                return Err(KernelError::ClassifierMismatch {
                    expected: input_classifier,
                    actual: output_classifier,
                });
            }
        }
        Ok(())
    }

    const fn is_variable(node: Node) -> bool {
        matches!(node, Node::TyFv { .. } | Node::TmFv { .. })
    }

    const fn is_binder(node: Node) -> bool {
        matches!(
            node,
            Node::TyLam(..)
                | Node::Lam(..)
                | Node::TyExists { .. }
                | Node::TyForall { .. }
                | Node::Model { .. }
        )
    }

    const fn is_proxy(node: Node) -> bool {
        matches!(
            node,
            Node::TmRef { .. } | Node::TyRef { .. } | Node::KindRef { .. }
        )
    }

    const fn same_head(left: Node, right: Node) -> bool {
        match (left, right) {
            (Node::KindStar, Node::KindStar)
            | (Node::BoolTy, Node::BoolTy)
            | (Node::KindArr(..), Node::KindArr(..))
            | (Node::TyArr(..), Node::TyArr(..))
            | (Node::TyApp(..), Node::TyApp(..))
            | (Node::App(..), Node::App(..))
            | (Node::Eq(..), Node::Eq(..))
            | (Node::Eps { .. }, Node::Eps { .. }) => true,
            (Node::TyFv { name: left, .. }, Node::TyFv { name: right, .. })
            | (Node::TmFv { name: left, .. }, Node::TmFv { name: right, .. }) => left == right,
            (Node::Bool(left), Node::Bool(right)) => left == right,
            (Node::Op1(left, ..), Node::Op1(right, ..)) => left.code() == right.code(),
            (Node::Op2(left, ..), Node::Op2(right, ..)) => left.code() == right.code(),
            (
                Node::TmRef {
                    src: left_src,
                    ix: left_ix,
                },
                Node::TmRef {
                    src: right_src,
                    ix: right_ix,
                },
            )
            | (
                Node::TyRef {
                    src: left_src,
                    ix: left_ix,
                },
                Node::TyRef {
                    src: right_src,
                    ix: right_ix,
                },
            )
            | (
                Node::KindRef {
                    src: left_src,
                    ix: left_ix,
                },
                Node::KindRef {
                    src: right_src,
                    ix: right_ix,
                },
            ) => left_src.get() == right_src.get() && left_ix.get() == right_ix.get(),
            _ => false,
        }
    }

    fn same_variable<E>(&self, left: Ref, right: Ref) -> Result<bool, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        Ok(
            match (*self.row::<E>(left)?.expr(), *self.row::<E>(right)?.expr()) {
                (
                    Node::TyFv {
                        name: left_name,
                        kind: left_kind,
                    },
                    Node::TyFv {
                        name: right_name,
                        kind: right_kind,
                    },
                ) => left_name == right_name && left_kind == right_kind,
                (
                    Node::TmFv {
                        name: left_name,
                        ty: left_ty,
                    },
                    Node::TmFv {
                        name: right_name,
                        ty: right_ty,
                    },
                ) => left_name == right_name && left_ty == right_ty,
                _ => false,
            },
        )
    }

    fn binder_shape<E>(input: Node, output: Node) -> Result<BinderShape, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        match (input, output) {
            (Node::TyLam(left_binder, left_body), Node::TyLam(right_binder, right_body))
            | (Node::Lam(left_binder, left_body), Node::Lam(right_binder, right_body)) => {
                Ok(BinderShape {
                    input_binder: left_binder,
                    output_binder: right_binder,
                    input_body: left_body,
                    output_body: right_body,
                })
            }
            _ => Err(Self::invalid_fact("binder congruence")),
        }
    }

    fn binder_substitution<E>(
        &self,
        binder: Ref,
        var: Option<Ref>,
        val: Option<Ref>,
    ) -> Result<(Option<Ref>, Option<Ref>), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let Some(var) = var else {
            return if val.is_none() {
                Ok((None, None))
            } else {
                Err(Self::invalid_fact("partial substitution"))
            };
        };
        if self.same_variable::<E>(binder, var)? {
            return Ok((None, None));
        }
        if Self::same_variable_name(*self.row::<E>(binder)?.expr(), *self.row::<E>(var)?.expr()) {
            return Err(Self::invalid_fact("ambiguous binder identity"));
        }
        let Some(val) = val else {
            if self.category_as::<E>(binder)? == self.category_as::<E>(var)? {
                return Err(Self::invalid_fact("universal binder freshness"));
            }
            return Ok((Some(var), None));
        };
        if self.contains_variable::<E>(val, binder)? {
            return Err(Self::invalid_fact("binder freshness"));
        }
        Ok((Some(var), Some(val)))
    }

    const fn same_variable_name(left: Node, right: Node) -> bool {
        match (left, right) {
            (Node::TyFv { name: left, .. }, Node::TyFv { name: right, .. })
            | (Node::TmFv { name: left, .. }, Node::TmFv { name: right, .. }) => left == right,
            _ => false,
        }
    }

    const fn same_implicit_binder(left: Node, right: Node) -> Option<(u64, Ref, Ref, bool)> {
        match (left, right) {
            (
                Node::TyExists {
                    name: left_name,
                    predicate: left_body,
                },
                Node::TyExists {
                    name: right_name,
                    predicate: right_body,
                },
            ) if left_name == right_name => Some((left_name, left_body, right_body, false)),
            (
                Node::TyForall {
                    name: left_name,
                    predicate: left_body,
                },
                Node::TyForall {
                    name: right_name,
                    predicate: right_body,
                },
            ) if left_name == right_name => Some((left_name, left_body, right_body, false)),
            (
                Node::Model {
                    name: left_name,
                    predicate: left_body,
                },
                Node::Model {
                    name: right_name,
                    predicate: right_body,
                },
            ) if left_name == right_name => Some((left_name, left_body, right_body, true)),
            _ => None,
        }
    }

    const fn renamed_implicit_binder(left: Node, right: Node) -> Option<(u64, Ref, u64, Ref)> {
        match (left, right) {
            (
                Node::TyExists {
                    name: left_name,
                    predicate: left_body,
                },
                Node::TyExists {
                    name: right_name,
                    predicate: right_body,
                },
            )
            | (
                Node::TyForall {
                    name: left_name,
                    predicate: left_body,
                },
                Node::TyForall {
                    name: right_name,
                    predicate: right_body,
                },
            )
            | (
                Node::Model {
                    name: left_name,
                    predicate: left_body,
                },
                Node::Model {
                    name: right_name,
                    predicate: right_body,
                },
            ) => Some((left_name, left_body, right_name, right_body)),
            _ => None,
        }
    }

    fn require_implicit_binder<E>(&self, binder: Ref, name: u64) -> Result<(), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let Node::TyFv { name: actual, kind } = *self.row::<E>(binder)?.expr() else {
            return Err(Self::invalid_fact("implicit binder witness"));
        };
        if actual != name {
            return Err(Self::invalid_fact("implicit binder witness"));
        }
        self.require_star::<E>(kind)
    }

    /// Whether `variable` occurs free beneath `root`.
    ///
    /// Rows form a directed acyclic graph with sharing, so the walk needs a
    /// visited set: without one a term of `n` rows can present exponentially
    /// many paths. An unresolved proxy is conservatively reported as an
    /// occurrence, which is the rejecting answer for every caller.
    pub(super) fn contains_variable<E>(
        &self,
        root: Ref,
        variable: Ref,
    ) -> Result<bool, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let needle = *self.row::<E>(variable)?.expr();
        let mut visited = BTreeSet::new();
        let mut pending = vec![(root, false)];
        while let Some((reference, shadowed)) = pending.pop() {
            // A shared row can be reached both inside and outside a binder, so
            // the binding state is part of the visited key.
            if !visited.insert((reference, shadowed)) {
                continue;
            }
            let node = *self.row::<E>(reference)?.expr();
            if Self::is_proxy(node) {
                return Ok(true);
            }
            if Self::same_variable_name(node, needle) {
                if !shadowed {
                    return Ok(true);
                }
                continue;
            }
            match node {
                Node::TyLam(binder, body) | Node::Lam(binder, body) => {
                    let binder_node = *self.row::<E>(binder)?.expr();
                    // The declaration itself is not a variable occurrence, but
                    // a term binder's classifier remains outside its scope.
                    pending.extend(
                        binder_node
                            .children()
                            .into_iter()
                            .map(|child| (child, shadowed)),
                    );
                    pending.push((
                        body,
                        shadowed || Self::same_variable_name(binder_node, needle),
                    ));
                }
                Node::TyExists { name, predicate }
                | Node::TyForall { name, predicate }
                | Node::Model { name, predicate } => {
                    let binds_needle =
                        matches!(needle, Node::TyFv { name: needle, .. } if needle == name);
                    pending.push((predicate, shadowed || binds_needle));
                }
                _ => pending.extend(node.children().into_iter().map(|child| (child, shadowed))),
            }
        }
        Ok(false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Arena, Link, Resolver, Table, wire};

    struct NoResolver;

    impl Resolver for NoResolver {
        type Error = Infallible;

        fn resolve(&mut self, _link: &Link) -> Result<Table, Self::Error> {
            unreachable!("literal imports do not consult the resolver")
        }
    }

    fn bool_kernel() -> (Kernel, Ref, Ref) {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        (kernel, star, bool_ty)
    }

    #[test]
    fn facts_are_one_based_reusable_and_truncatable() {
        let (mut kernel, star, bool_ty) = bool_kernel();
        let first = kernel.syn_refl(None, SynRel::Syn, star).unwrap();
        let second = kernel.syn_refl(None, SynRel::Alpha, bool_ty).unwrap();
        assert_eq!(first.get(), 1);
        assert_eq!(second.get(), 2);

        assert!(kernel.remove_syn_fact(first));
        let reused = kernel.syn_refl(None, SynRel::Conv, bool_ty).unwrap();
        assert_eq!(reused, first);
        assert_eq!(kernel.syn_fact(reused).unwrap().rel(), SynRel::Conv);

        kernel.syn_refl(Some(second), SynRel::Syn, star).unwrap();
        assert_eq!(kernel.syn_fact(second).unwrap().input(), star);

        assert!(kernel.remove_syn_fact(first));
        kernel.truncate_syn_facts(1);
        assert_eq!(kernel.syn_fact_len(), 1);
        assert_eq!(kernel.syn_refl(None, SynRel::Syn, star).unwrap(), first);
        assert_eq!(kernel.syn_fact_len(), 1);
    }

    #[test]
    fn free_list_round_trips_with_the_arena() {
        let (mut kernel, star, bool_ty) = bool_kernel();
        let first = kernel.syn_refl(None, SynRel::Syn, star).unwrap();
        kernel.syn_refl(None, SynRel::Syn, bool_ty).unwrap();
        assert!(kernel.remove_syn_fact(first));

        let mut encoded = Vec::new();
        wire::serialize(kernel.arena(), &mut encoded).unwrap();
        let decoded: Arena = wire::deserialize(encoded.as_slice()).unwrap();
        assert_eq!(&decoded, kernel.arena());
        assert!(decoded.syn_fact(first).is_none());
    }

    #[test]
    fn alpha_and_beta_are_small_rules_over_cached_substitution() {
        let (mut kernel, _, bool_ty) = bool_kernel();
        let left_var = kernel.tm_fv(1, bool_ty).unwrap();
        let left = kernel.lam(left_var, left_var).unwrap();
        let right_var = kernel.tm_fv(2, bool_ty).unwrap();
        let right = kernel.lam(right_var, right_var).unwrap();

        let classifier = kernel.syn_refl(None, SynRel::Syn, bool_ty).unwrap();
        let left_ty = kernel.classifier(left).unwrap();
        let right_ty = kernel.classifier(right).unwrap();
        let function_type = kernel
            .syn_congr(
                None,
                SynRel::Syn,
                None,
                None,
                left_ty,
                right_ty,
                &[classifier, classifier],
            )
            .unwrap();
        kernel.union_syn_fact(function_type).unwrap();
        let renamed_body = kernel.syn_sub_var(None, left_var, right_var).unwrap();
        let alpha = kernel
            .syn_alpha_binder(None, left, right, classifier, renamed_body)
            .unwrap();
        kernel.union_syn_fact(alpha).unwrap();
        assert!(kernel.tm_eq(left, right).unwrap());

        let truth = kernel.bool(bool_ty, true).unwrap();
        let application = kernel.app(left, truth).unwrap();
        let substitution = kernel.syn_sub_var(None, left_var, truth).unwrap();
        let beta = kernel
            .tm_beta_fact(None, application, substitution)
            .unwrap();
        assert_eq!(kernel.syn_fact(beta).unwrap().output(), truth);
        kernel.union_syn_fact(beta).unwrap();
        assert!(kernel.tm_eq(application, truth).unwrap());
    }

    #[test]
    fn union_materializes_exactly_the_relation_refinement_chain() {
        let (mut kernel, _, bool_ty) = bool_kernel();
        let left = kernel.bool(bool_ty, true).unwrap();
        let right = kernel.bool(bool_ty, true).unwrap();
        let syntax = kernel
            .syn_congr(None, SynRel::Syn, None, None, left, right, &[])
            .unwrap();
        kernel.union_syn_fact(syntax).unwrap();

        assert_eq!(kernel.arena().syn_eq(right), Some(left));
        assert_eq!(kernel.arena().conv(right), Some(left));
        assert_eq!(kernel.arena().conv(left), Some(bool_ty));
        assert_eq!(kernel.arena().sort(right), Some(bool_ty));
        assert_eq!(kernel.arena().eq(right), Some(left));

        let third = kernel.bool(bool_ty, true).unwrap();
        let syntax = kernel
            .syn_congr(None, SynRel::Syn, None, None, left, third, &[])
            .unwrap();
        let conversion = kernel.syn_refine(None, syntax, SynRel::Conv).unwrap();
        kernel.union_syn_fact(conversion).unwrap();

        assert_eq!(kernel.arena().syn_eq(third), None);
        assert_eq!(kernel.arena().conv(third), Some(left));
        assert_eq!(kernel.arena().conv(left), Some(bool_ty));
        assert_eq!(kernel.arena().sort(third), Some(bool_ty));
        assert_eq!(kernel.arena().eq(third), Some(left));
    }

    #[test]
    fn union_failure_prefixes_are_coarse_to_fine_on_malformed_private_state() {
        fn syntax_fact(kernel: &mut Kernel, bool_ty: Ref) -> (Ref, Ref, SynFactId) {
            let left = kernel.bool(bool_ty, true).unwrap();
            let right = kernel.bool(bool_ty, true).unwrap();
            let fact = kernel
                .syn_congr(None, SynRel::Syn, None, None, left, right, &[])
                .unwrap();
            (left, right, fact)
        }

        // A malformed semantic path fails before any observable mutation.
        let (mut kernel, star, bool_ty) = bool_kernel();
        let (left, _right, fact) = syntax_fact(&mut kernel, bool_ty);
        assert!(
            kernel
                .arena
                .set_eq_column(EqColumn::Semantic, left, Some(star))
        );
        let before = kernel.arena.clone();
        assert!(kernel.union_syn_fact(fact).is_err());
        assert_eq!(kernel.arena, before);

        // If conversion is malformed, the already completed semantic union
        // remains, but no finer cache edge is installed.
        let (mut kernel, star, bool_ty) = bool_kernel();
        let (left, right, fact) = syntax_fact(&mut kernel, bool_ty);
        assert!(kernel.arena.set_eq_column(EqColumn::Conv, left, Some(star)));
        assert!(kernel.union_syn_fact(fact).is_err());
        assert_eq!(kernel.arena.eq(right), Some(left));
        assert_eq!(kernel.arena.syn_eq(right), None);

        // If only syntactic equality is malformed, both coarser unions have
        // completed before the final checked prefix fails.
        let (mut kernel, star, bool_ty) = bool_kernel();
        let (left, right, fact) = syntax_fact(&mut kernel, bool_ty);
        assert!(kernel.arena.set_eq_column(EqColumn::Syn, left, Some(star)));
        assert!(kernel.union_syn_fact(fact).is_err());
        assert_eq!(kernel.arena.eq(right), Some(left));
        assert_eq!(kernel.arena.conv(right), Some(left));
        assert_eq!(kernel.arena.syn_eq(right), None);
    }

    #[test]
    fn congruence_composes_substitution_without_tree_walks() {
        let (mut kernel, _, bool_ty) = bool_kernel();
        let bool_to_bool = kernel.ty_arr(bool_ty, bool_ty).unwrap();
        let function = kernel.tm_fv(3, bool_to_bool).unwrap();
        let variable = kernel.tm_fv(4, bool_ty).unwrap();
        let truth = kernel.bool(bool_ty, true).unwrap();
        let input = kernel.app(function, variable).unwrap();
        let output = kernel.app(function, truth).unwrap();

        let function_unchanged = kernel
            .syn_sub_leaf(None, variable, truth, function)
            .unwrap();
        let variable_replaced = kernel.syn_sub_var(None, variable, truth).unwrap();
        let fact = kernel
            .syn_congr(
                None,
                SynRel::Syn,
                Some(variable),
                Some(truth),
                input,
                output,
                &[function_unchanged, variable_replaced],
            )
            .unwrap();
        assert_eq!(kernel.syn_fact(fact).unwrap().output(), output);
    }

    #[test]
    fn logical_opcode_congruence_tracks_substitution_and_opcode_identity() {
        let (mut kernel, _, bool_ty) = bool_kernel();
        let variable = kernel.tm_fv(20, bool_ty).unwrap();
        let truth = kernel.bool(bool_ty, true).unwrap();
        let unary_input = kernel.op1(crate::builtin::Op1::Not, variable).unwrap();
        let unary_output = kernel.op1(crate::builtin::Op1::Not, truth).unwrap();
        let replaced = kernel.syn_sub_var(None, variable, truth).unwrap();
        kernel
            .syn_congr(
                None,
                SynRel::Syn,
                Some(variable),
                Some(truth),
                unary_input,
                unary_output,
                &[replaced],
            )
            .unwrap();

        for op in [
            crate::builtin::Op2::And,
            crate::builtin::Op2::Or,
            crate::builtin::Op2::Imp,
        ] {
            let left_unchanged = kernel.syn_sub_leaf(None, variable, truth, truth).unwrap();
            let binary_input = kernel.op2(op, truth, variable).unwrap();
            let binary_output = kernel.op2(op, truth, truth).unwrap();
            kernel
                .syn_congr(
                    None,
                    SynRel::Syn,
                    Some(variable),
                    Some(truth),
                    binary_input,
                    binary_output,
                    &[left_unchanged, replaced],
                )
                .unwrap();
            assert!(
                kernel
                    .contains_variable::<Infallible>(binary_input, variable)
                    .unwrap()
            );
            assert!(
                !kernel
                    .contains_variable::<Infallible>(binary_output, variable)
                    .unwrap()
            );
        }

        let binary_output = kernel.op2(crate::builtin::Op2::And, truth, truth).unwrap();
        let wrong_opcode = kernel.op2(crate::builtin::Op2::Or, truth, truth).unwrap();
        let left_refl = kernel.syn_refl(None, SynRel::Syn, truth).unwrap();
        let right_refl = kernel.syn_refl(None, SynRel::Syn, truth).unwrap();
        assert!(
            kernel
                .syn_congr(
                    None,
                    SynRel::Syn,
                    None,
                    None,
                    binary_output,
                    wrong_opcode,
                    &[left_refl, right_refl],
                )
                .is_err()
        );
    }

    #[test]
    fn transitivity_preserves_an_active_left_substitution() {
        let (mut kernel, _, bool_ty) = bool_kernel();
        let variable = kernel.tm_fv(4, bool_ty).unwrap();
        let first_truth = kernel.bool(bool_ty, true).unwrap();
        let second_truth = kernel.bool(bool_ty, true).unwrap();

        let substituted = kernel.syn_sub_var(None, variable, first_truth).unwrap();
        let equal_truths = kernel
            .syn_congr(
                None,
                SynRel::Syn,
                None,
                None,
                first_truth,
                second_truth,
                &[],
            )
            .unwrap();
        let composed = kernel.syn_trans(None, substituted, equal_truths).unwrap();
        let fact = kernel.syn_fact(composed).unwrap();

        assert_eq!(fact.rel(), SynRel::Syn);
        assert_eq!(fact.var(), Some(variable));
        assert_eq!(fact.val(), Some(first_truth));
        assert_eq!(fact.input(), variable);
        assert_eq!(fact.output(), second_truth);
    }

    #[test]
    fn transitivity_keeps_the_direct_form_and_chooses_the_coarser_relation() {
        let (mut kernel, _, bool_ty) = bool_kernel();
        let first = kernel.bool(bool_ty, true).unwrap();
        let middle = kernel.bool(bool_ty, true).unwrap();
        let last = kernel.bool(bool_ty, true).unwrap();
        let left = kernel
            .syn_congr(None, SynRel::Syn, None, None, first, middle, &[])
            .unwrap();
        let right = kernel
            .syn_congr(None, SynRel::Alpha, None, None, middle, last, &[])
            .unwrap();
        let composed = kernel.syn_trans(None, left, right).unwrap();
        let fact = kernel.syn_fact(composed).unwrap();

        assert_eq!(fact.rel(), SynRel::Alpha);
        assert_eq!(fact.var(), None);
        assert_eq!(fact.val(), None);
        assert_eq!(fact.input(), first);
        assert_eq!(fact.output(), last);
    }

    #[test]
    fn transitivity_still_requires_a_direct_right_fact() {
        let (mut kernel, _, bool_ty) = bool_kernel();
        let variable = kernel.tm_fv(4, bool_ty).unwrap();
        let truth = kernel.bool(bool_ty, true).unwrap();
        let active = kernel.syn_sub_var(None, variable, truth).unwrap();

        assert!(kernel.syn_trans(None, active, active).is_err());
    }

    #[test]
    fn universal_leaf_facts_compose_by_congruence_and_transitivity() {
        let (mut kernel, _, bool_ty) = bool_kernel();
        let function_ty = kernel.ty_arr(bool_ty, bool_ty).unwrap();
        let function = kernel.tm_fv(3, function_ty).unwrap();
        let variable = kernel.tm_fv(4, bool_ty).unwrap();
        let first_truth = kernel.bool(bool_ty, true).unwrap();
        let second_truth = kernel.bool(bool_ty, true).unwrap();
        let first_application = kernel.app(function, first_truth).unwrap();
        let second_application = kernel.app(function, second_truth).unwrap();

        let function_unchanged = kernel
            .syn_sub_leaf_forall(None, variable, function)
            .unwrap();
        let truth_unchanged = kernel
            .syn_sub_leaf_forall(None, variable, first_truth)
            .unwrap();
        let universal_application = kernel
            .syn_congr(
                None,
                SynRel::Syn,
                Some(variable),
                None,
                first_application,
                first_application,
                &[function_unchanged, truth_unchanged],
            )
            .unwrap();
        let function_refl = kernel.syn_refl(None, SynRel::Syn, function).unwrap();
        let equal_truths = kernel
            .syn_congr(
                None,
                SynRel::Syn,
                None,
                None,
                first_truth,
                second_truth,
                &[],
            )
            .unwrap();
        let equal_applications = kernel
            .syn_congr(
                None,
                SynRel::Syn,
                None,
                None,
                first_application,
                second_application,
                &[function_refl, equal_truths],
            )
            .unwrap();
        let composed = kernel
            .syn_trans(None, universal_application, equal_applications)
            .unwrap();
        let fact = kernel.syn_fact(composed).unwrap();

        assert_eq!(fact.var(), Some(variable));
        assert_eq!(fact.val(), None);
        assert_eq!(fact.input(), first_application);
        assert_eq!(fact.output(), second_application);
    }

    #[test]
    fn variable_congruence_rejects_duplicate_classifier_rows() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let first_bool = kernel.bool_ty(star).unwrap();
        let second_bool = kernel.bool_ty(star).unwrap();
        let variable = kernel.tm_fv(4, first_bool).unwrap();
        let duplicate = kernel.tm_fv(4, second_bool).unwrap();
        let truth = kernel.bool(first_bool, true).unwrap();
        let classifier = kernel
            .syn_sub_leaf(None, variable, truth, second_bool)
            .unwrap();

        assert!(
            kernel
                .syn_congr(
                    None,
                    SynRel::Syn,
                    Some(variable),
                    Some(truth),
                    duplicate,
                    duplicate,
                    &[classifier],
                )
                .is_err()
        );
    }

    #[test]
    fn fresh_substitution_uses_complete_structural_named_syntax() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let first_bool = kernel.bool_ty(star).unwrap();
        let duplicate_bool = kernel.bool_ty(star).unwrap();
        let function_ty = kernel.ty_arr(first_bool, first_bool).unwrap();
        let variable = kernel.tm_fv(4, first_bool).unwrap();
        let duplicate = kernel.tm_fv(4, duplicate_bool).unwrap();
        let distinct = kernel.tm_fv(4, function_ty).unwrap();
        let truth = kernel.bool(first_bool, true).unwrap();
        let falsity = kernel.bool(first_bool, false).unwrap();
        let compound = kernel.eq(first_bool, truth, falsity).unwrap();

        assert!(kernel.substitution_fresh(variable, compound).unwrap());
        let unchanged = kernel
            .syn_sub_fresh(None, variable, truth, compound)
            .unwrap();
        let fact = kernel.syn_fact(unchanged).unwrap();
        assert_eq!(fact.input(), compound);
        assert_eq!(fact.output(), compound);

        assert!(!kernel.substitution_fresh(variable, variable).unwrap());
        assert!(!kernel.substitution_fresh(variable, duplicate).unwrap());
        assert!(kernel.substitution_fresh(variable, distinct).unwrap());
        assert!(
            kernel
                .syn_sub_fresh(None, variable, truth, duplicate)
                .is_err()
        );
    }

    #[test]
    fn substitution_leaf_rejects_an_import_without_closedness_evidence() {
        let mut imported = Kernel::new();
        let imported_star = imported.star().unwrap();
        let imported_bool = imported.bool_ty(imported_star).unwrap();
        let imported_variable = imported.tm_fv(4, imported_bool).unwrap();

        let (mut kernel, _, bool_ty) = bool_kernel();
        let variable = kernel.tm_fv(4, bool_ty).unwrap();
        let truth = kernel.bool(bool_ty, true).unwrap();
        let source = kernel.import_literal(imported.into_arena()).unwrap();
        let proxy = kernel
            .tm_ref(&mut NoResolver, source, imported_variable, bool_ty)
            .unwrap();

        assert!(kernel.syn_sub_leaf(None, variable, truth, proxy).is_err());
        assert!(
            kernel
                .syn_congr(
                    None,
                    SynRel::Syn,
                    Some(variable),
                    Some(truth),
                    proxy,
                    proxy,
                    &[],
                )
                .is_err()
        );
        assert!(
            kernel
                .contains_variable::<Infallible>(proxy, variable)
                .unwrap()
        );
    }

    #[test]
    fn eta_uses_only_shape_and_freshness_then_can_be_discarded() {
        let (mut kernel, _, bool_ty) = bool_kernel();
        let function_ty = kernel.ty_arr(bool_ty, bool_ty).unwrap();
        let function = kernel.tm_fv(1, function_ty).unwrap();
        let variable = kernel.tm_fv(2, bool_ty).unwrap();
        let body = kernel.app(function, variable).unwrap();
        let source = kernel.lam(variable, body).unwrap();
        let bool_refl = kernel.syn_refl(None, SynRel::Syn, bool_ty).unwrap();
        let source_ty = kernel.classifier(source).unwrap();
        let function_type = kernel.classifier(function).unwrap();
        let type_equality = kernel
            .syn_congr(
                None,
                SynRel::Syn,
                None,
                None,
                source_ty,
                function_type,
                &[bool_refl, bool_refl],
            )
            .unwrap();
        kernel.union_syn_fact(type_equality).unwrap();
        let keep = kernel.syn_fact_len();

        let eta = kernel.tm_eta_fact(None, source).unwrap();
        assert_eq!(kernel.syn_fact(eta).unwrap().output(), function);
        kernel.union_syn_fact(eta).unwrap();
        kernel.truncate_syn_facts(keep);
        assert!(kernel.syn_fact(eta).is_err());
        assert!(kernel.tm_eq(source, function).unwrap());
    }

    #[test]
    fn conversion_congruence_does_not_enter_model() {
        let (mut kernel, star, bool_ty) = bool_kernel();
        let truth = kernel.bool(bool_ty, true).unwrap();
        let model = kernel.model(9, truth).unwrap();
        let binder = kernel.ty_fv(9, star).unwrap();
        let body = kernel.syn_refl(None, SynRel::Conv, truth).unwrap();

        assert!(
            kernel
                .syn_implicit_binder_congr(
                    None,
                    SynRel::Conv,
                    None,
                    None,
                    model,
                    model,
                    binder,
                    body,
                )
                .is_err()
        );
    }
}
