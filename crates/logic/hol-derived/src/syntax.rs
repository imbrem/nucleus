//! Userspace certificates for structurally identical checked syntax.

use std::collections::BTreeMap;

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref, Sort, SynFactId, SynRel, Tag, TmTag, TyTag};

use crate::substitute;

/// Failure to certify two checked rows as structurally identical.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum SyntaxError {
    /// A checked syntactic rule rejected the derived certificate.
    #[snafu(display("syntax certification was rejected: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// The two checked trees differ structurally.
    #[snafu(display("checked syntax is not structurally identical"))]
    Different,
}

impl From<KernelError> for SyntaxError {
    fn from(source: KernelError) -> Self {
        Self::Kernel { source }
    }
}

pub(crate) fn require_same_syntax(
    kernel: &Kernel,
    left: Ref,
    right: Ref,
) -> Result<(), SyntaxError> {
    fn visit(
        kernel: &Kernel,
        left: Ref,
        right: Ref,
        seen: &mut BTreeMap<(Ref, Ref), bool>,
    ) -> Result<(), SyntaxError> {
        if left == right || seen.insert((left, right), true).is_some() {
            return Ok(());
        }
        let tag = kernel.arena().tag(left);
        if tag.is_none()
            || tag != kernel.arena().tag(right)
            || kernel.arena().name(left) != kernel.arena().name(right)
            || kernel.arena().bool_value(left) != kernel.arena().bool_value(right)
            || kernel.arena().op1(left) != kernel.arena().op1(right)
            || kernel.arena().op2(left) != kernel.arena().op2(right)
        {
            return Err(SyntaxError::Different);
        }
        let left_children = kernel
            .arena()
            .children(left)
            .ok_or(SyntaxError::Different)?
            .collect::<Vec<_>>();
        let right_children = kernel
            .arena()
            .children(right)
            .ok_or(SyntaxError::Different)?
            .collect::<Vec<_>>();
        if left_children.len() != right_children.len() {
            return Err(SyntaxError::Different);
        }
        for (&left, &right) in left_children.iter().zip(&right_children) {
            visit(kernel, left, right, seen)?;
        }
        Ok(())
    }

    visit(kernel, left, right, &mut BTreeMap::new())
}

/// Certifies and joins two structurally identical checked syntax trees.
///
/// This is untrusted traversal: every congruence edge is checked by the
/// kernel, and a mismatch simply returns an error.
///
/// # Errors
///
/// Returns an error if either tree is absent, their syntax differs, or a
/// checked reflexivity, congruence, binder, or union operation rejects the
/// derived evidence.
pub fn join_same_syntax(
    kernel: &mut Kernel,
    left: Ref,
    right: Ref,
) -> Result<SynFactId, SyntaxError> {
    fn derive(
        kernel: &mut Kernel,
        left: Ref,
        right: Ref,
        memo: &mut BTreeMap<(Ref, Ref), SynFactId>,
    ) -> Result<SynFactId, SyntaxError> {
        if let Some(fact) = memo.get(&(left, right)) {
            return Ok(*fact);
        }
        if left == right {
            let fact = kernel.syn_refl(None, SynRel::Syn, left)?;
            memo.insert((left, right), fact);
            return Ok(fact);
        }
        if kernel.category(left)? != Sort::Kind {
            let classifiers = derive(
                kernel,
                kernel.classifier(left)?,
                kernel.classifier(right)?,
                memo,
            )?;
            kernel.union_syn_fact(classifiers)?;
        }
        let tag = kernel.arena().tag(left);
        if tag.is_none()
            || tag != kernel.arena().tag(right)
            || kernel.arena().name(left) != kernel.arena().name(right)
            || kernel.arena().bool_value(left) != kernel.arena().bool_value(right)
            || kernel.arena().op1(left) != kernel.arena().op1(right)
            || kernel.arena().op2(left) != kernel.arena().op2(right)
        {
            return Err(SyntaxError::Different);
        }
        let left_children = kernel
            .arena()
            .children(left)
            .ok_or(SyntaxError::Different)?
            .collect::<Vec<_>>();
        let right_children = kernel
            .arena()
            .children(right)
            .ok_or(SyntaxError::Different)?
            .collect::<Vec<_>>();
        if left_children.len() != right_children.len() {
            return Err(SyntaxError::Different);
        }
        let facts = left_children
            .iter()
            .zip(&right_children)
            .map(|(&left, &right)| derive(kernel, left, right, memo))
            .collect::<Result<Vec<_>, _>>()?;
        for &fact in &facts {
            kernel.union_syn_fact(fact)?;
        }
        let fact = match tag {
            Some(Tag::Tm(TmTag::Lam) | Tag::Ty(TyTag::Lam)) if facts.len() == 2 => kernel
                .syn_binder_congr(
                    None,
                    SynRel::Syn,
                    None,
                    None,
                    left,
                    right,
                    facts[0],
                    facts[1],
                ),
            Some(Tag::Ty(TyTag::Model) | Tag::Tm(TmTag::TyExists | TmTag::TyForall))
                if facts.len() == 1 =>
            {
                let name = kernel.arena().name(left).ok_or(SyntaxError::Different)?;
                let body = left_children[0];
                let star = kernel.classifier(kernel.classifier(body)?)?;
                let binder = kernel.ty_fv(name, star)?;
                kernel.syn_implicit_binder_congr(
                    None,
                    SynRel::Syn,
                    None,
                    None,
                    left,
                    right,
                    binder,
                    facts[0],
                )
            }
            _ => kernel.syn_congr(None, SynRel::Syn, None, None, left, right, &facts),
        }?;
        memo.insert((left, right), fact);
        Ok(fact)
    }

    let fact = derive(kernel, left, right, &mut BTreeMap::new())?;
    kernel.union_syn_fact(fact)?;
    Ok(fact)
}

/// Certifies and joins two alpha-equivalent checked syntax trees.
///
/// This userspace traversal renames binders by asking the ordinary checked
/// substitution API for the body certificate, then composes the kernel's
/// alpha and congruence rules. It is proof search, not an admission rule: a
/// wrong guess can only be rejected by `Kernel`.
///
/// # Errors
///
/// Returns an error if the search cannot establish alpha equivalence, it
/// encounters ambiguous bound-variable rows, or any checked certificate step
/// is rejected. The search is deliberately conservative and need not decide
/// every alpha-equivalent pair.
pub fn join_alpha_equivalent(
    kernel: &mut Kernel,
    left: Ref,
    right: Ref,
) -> Result<SynFactId, SyntaxError> {
    let fact = join_via_fresh_normal_form(kernel, left, right)?;
    kernel.union_syn_fact(fact)?;
    Ok(fact)
}

fn children(kernel: &Kernel, reference: Ref) -> Result<Vec<Ref>, SyntaxError> {
    Ok(kernel
        .arena()
        .children(reference)
        .ok_or(SyntaxError::Different)?
        .collect())
}

fn pair(kernel: &Kernel, reference: Ref) -> Result<[Ref; 2], SyntaxError> {
    children(kernel, reference)?
        .try_into()
        .map_err(|_| SyntaxError::Different)
}

fn only_child(kernel: &Kernel, reference: Ref) -> Result<Ref, SyntaxError> {
    let [child]: [Ref; 1] = children(kernel, reference)?
        .try_into()
        .map_err(|_| SyntaxError::Different)?;
    Ok(child)
}

fn bound_type(kernel: &Kernel, root: Ref, name: u64) -> Result<Option<Ref>, SyntaxError> {
    let mut stack = vec![root];
    let mut found = None;
    while let Some(reference) = stack.pop() {
        if kernel.arena().tag(reference) == Some(Tag::Ty(TyTag::Fv))
            && kernel.arena().name(reference) == Some(name)
        {
            if found.is_some_and(|other| other != reference) {
                return Err(SyntaxError::Different);
            }
            found = Some(reference);
        }
        stack.extend(children(kernel, reference)?);
    }
    Ok(found)
}

fn join_via_fresh_normal_form(
    kernel: &mut Kernel,
    left: Ref,
    right: Ref,
) -> Result<SynFactId, SyntaxError> {
    let base = kernel.fresh_name(&[left, right])?;
    let (left_normal, left_fact, binders) = {
        let mut freshen = Freshen::new(kernel, base);
        let (normal, fact) = freshen.derive(left)?;
        (normal, fact, freshen.binders)
    };
    let (right_normal, right_fact) = Freshen::reusing(kernel, base, binders).derive(right)?;
    let middle = join_same_syntax(kernel, left_normal, right_normal)?;
    let right_fact = kernel.syn_symm(None, right_fact)?;
    let left_middle = kernel.syn_trans(None, left_fact, middle)?;
    Ok(kernel.syn_trans(None, left_middle, right_fact)?)
}

struct Freshen<'a> {
    kernel: &'a mut Kernel,
    next_name: u64,
    binders: Vec<Ref>,
    binder_cursor: usize,
    reuse_binders: bool,
    named_binders: BTreeMap<(Sort, u64), Ref>,
    memo: BTreeMap<Ref, (Ref, SynFactId)>,
}

impl<'a> Freshen<'a> {
    const fn new(kernel: &'a mut Kernel, next_name: u64) -> Self {
        Self {
            kernel,
            next_name,
            binders: Vec::new(),
            binder_cursor: 0,
            reuse_binders: false,
            named_binders: BTreeMap::new(),
            memo: BTreeMap::new(),
        }
    }

    const fn reusing(kernel: &'a mut Kernel, next_name: u64, binders: Vec<Ref>) -> Self {
        Self {
            kernel,
            next_name,
            binders,
            binder_cursor: 0,
            reuse_binders: true,
            named_binders: BTreeMap::new(),
            memo: BTreeMap::new(),
        }
    }

    fn derive(&mut self, input: Ref) -> Result<(Ref, SynFactId), SyntaxError> {
        if let Some(&result) = self.memo.get(&input) {
            return Ok(result);
        }
        let tag = self
            .kernel
            .arena()
            .tag(input)
            .ok_or(SyntaxError::Different)?;
        let result = match tag {
            Tag::Tm(TmTag::Lam) | Tag::Ty(TyTag::Lam) => self.explicit(input, tag)?,
            Tag::Ty(TyTag::Model) | Tag::Tm(TmTag::TyExists | TmTag::TyForall) => {
                self.implicit(input, tag)?
            }
            _ => self.congruent(input, tag)?,
        };
        self.memo.insert(input, result);
        Ok(result)
    }

    fn take_name(&mut self) -> Result<u64, SyntaxError> {
        let name = self.next_name;
        self.next_name = name.checked_add(1).ok_or(SyntaxError::Different)?;
        Ok(name)
    }

    fn binder(
        &mut self,
        sort: Sort,
        source_name: u64,
        classifier: Ref,
    ) -> Result<Ref, SyntaxError> {
        if let Some(&binder) = self.named_binders.get(&(sort, source_name)) {
            let fact = join_same_syntax(self.kernel, self.kernel.classifier(binder)?, classifier)?;
            self.kernel.union_syn_fact(fact)?;
            return Ok(binder);
        }
        if self.reuse_binders {
            let binder = self
                .binders
                .get(self.binder_cursor)
                .copied()
                .ok_or(SyntaxError::Different)?;
            self.binder_cursor += 1;
            if self.kernel.category(binder)? != sort {
                return Err(SyntaxError::Different);
            }
            let fact = join_same_syntax(self.kernel, self.kernel.classifier(binder)?, classifier)?;
            self.kernel.union_syn_fact(fact)?;
            self.named_binders.insert((sort, source_name), binder);
            return Ok(binder);
        }
        let name = self.take_name()?;
        let binder = match sort {
            Sort::Tm => self.kernel.tm_fv(name, classifier)?,
            Sort::Ty => self.kernel.ty_fv(name, classifier)?,
            Sort::Kind => return Err(SyntaxError::Different),
        };
        self.binders.push(binder);
        self.binder_cursor += 1;
        self.named_binders.insert((sort, source_name), binder);
        Ok(binder)
    }

    fn explicit(&mut self, input: Ref, tag: Tag) -> Result<(Ref, SynFactId), SyntaxError> {
        let [old_binder, old_body] = pair(self.kernel, input)?;
        let classifier = self.kernel.classifier(old_binder)?;
        let old_name = self
            .kernel
            .arena()
            .name(old_binder)
            .ok_or(SyntaxError::Different)?;
        let new_binder = match tag {
            Tag::Tm(TmTag::Lam) => self.binder(Sort::Tm, old_name, classifier)?,
            Tag::Ty(TyTag::Lam) => self.binder(Sort::Ty, old_name, classifier)?,
            _ => return Err(SyntaxError::Different),
        };
        let binder_refl = self.kernel.syn_refl(None, SynRel::Syn, new_binder)?;
        self.memo.insert(new_binder, (new_binder, binder_refl));
        let substitution = substitute(self.kernel, old_binder, new_binder, old_body)
            .map_err(|_| SyntaxError::Different)?;
        let substitution_fact = self
            .kernel
            .syn_refine(None, substitution.fact, SynRel::Alpha)?;
        let intermediate = self.build_explicit(tag, input, new_binder, substitution.output)?;
        let classifier_fact =
            join_same_syntax(self.kernel, classifier, self.kernel.classifier(new_binder)?)?;
        let renamed = self.kernel.syn_alpha_binder(
            None,
            input,
            intermediate,
            classifier_fact,
            substitution_fact,
        )?;
        let (body, body_fact) = self.derive(substitution.output)?;
        self.kernel.union_syn_fact(body_fact)?;
        let output = self.build_explicit(tag, input, new_binder, body)?;
        let binder_fact = self.kernel.syn_refl(None, SynRel::Alpha, new_binder)?;
        let congruent = self.kernel.syn_binder_congr(
            None,
            SynRel::Alpha,
            None,
            None,
            intermediate,
            output,
            binder_fact,
            body_fact,
        )?;
        Ok((output, self.kernel.syn_trans(None, renamed, congruent)?))
    }

    fn build_explicit(
        &mut self,
        tag: Tag,
        source: Ref,
        binder: Ref,
        body: Ref,
    ) -> Result<Ref, SyntaxError> {
        Ok(match tag {
            Tag::Tm(TmTag::Lam) => {
                self.kernel
                    .lam_at(self.kernel.classifier(source)?, binder, body)?
            }
            Tag::Ty(TyTag::Lam) => self.kernel.ty_lam(binder, body)?,
            _ => return Err(SyntaxError::Different),
        })
    }

    fn implicit(&mut self, input: Ref, tag: Tag) -> Result<(Ref, SynFactId), SyntaxError> {
        let old_name = self
            .kernel
            .arena()
            .name(input)
            .ok_or(SyntaxError::Different)?;
        let old_body = only_child(self.kernel, input)?;
        let star = self.kernel.classifier(self.kernel.classifier(old_body)?)?;
        let old_binder = bound_type(self.kernel, old_body, old_name)?
            .unwrap_or(self.kernel.ty_fv(old_name, star)?);
        let new_binder = self.binder(Sort::Ty, old_name, star)?;
        let new_name = self
            .kernel
            .arena()
            .name(new_binder)
            .ok_or(SyntaxError::Different)?;
        let binder_refl = self.kernel.syn_refl(None, SynRel::Syn, new_binder)?;
        self.memo.insert(new_binder, (new_binder, binder_refl));
        let substitution = substitute(self.kernel, old_binder, new_binder, old_body)
            .map_err(|_| SyntaxError::Different)?;
        let substitution_fact = self
            .kernel
            .syn_refine(None, substitution.fact, SynRel::Alpha)?;
        let intermediate = self.build_implicit(tag, new_name, substitution.output)?;
        let renamed = self.kernel.syn_alpha_implicit_binder(
            None,
            input,
            intermediate,
            old_binder,
            new_binder,
            substitution_fact,
        )?;
        let (body, body_fact) = self.derive(substitution.output)?;
        self.kernel.union_syn_fact(body_fact)?;
        let output = self.build_implicit(tag, new_name, body)?;
        let congruent = self.kernel.syn_implicit_binder_congr(
            None,
            SynRel::Alpha,
            None,
            None,
            intermediate,
            output,
            new_binder,
            body_fact,
        )?;
        Ok((output, self.kernel.syn_trans(None, renamed, congruent)?))
    }

    fn build_implicit(&mut self, tag: Tag, name: u64, body: Ref) -> Result<Ref, SyntaxError> {
        Ok(match tag {
            Tag::Ty(TyTag::Model) => self.kernel.model(name, body)?,
            Tag::Tm(TmTag::TyExists) => self.kernel.ty_exists(name, body)?,
            Tag::Tm(TmTag::TyForall) => self.kernel.ty_forall(name, body)?,
            _ => return Err(SyntaxError::Different),
        })
    }

    fn congruent(&mut self, input: Ref, tag: Tag) -> Result<(Ref, SynFactId), SyntaxError> {
        let inputs = children(self.kernel, input)?;
        if inputs.is_empty() {
            return Ok((input, self.kernel.syn_refl(None, SynRel::Syn, input)?));
        }
        let derived = inputs
            .iter()
            .map(|&child| self.derive(child))
            .collect::<Result<Vec<_>, _>>()?;
        let outputs = derived
            .iter()
            .map(|&(output, _)| output)
            .collect::<Vec<_>>();
        let facts = derived.iter().map(|&(_, fact)| fact).collect::<Vec<_>>();
        for &fact in &facts {
            self.kernel.union_syn_fact(fact)?;
        }
        let output = self.rebuild(input, tag, &outputs)?;
        let fact = self
            .kernel
            .syn_congr(None, SynRel::Alpha, None, None, input, output, &facts)?;
        Ok((output, fact))
    }

    fn rebuild(&mut self, input: Ref, tag: Tag, c: &[Ref]) -> Result<Ref, SyntaxError> {
        let name = self.kernel.arena().name(input);
        Ok(match tag {
            Tag::Kind(covalence_logic_hol::KindTag::Arr) => self.kernel.kind_arr(c[0], c[1])?,
            Tag::Ty(TyTag::Arr) => self.kernel.ty_arr(c[0], c[1])?,
            Tag::Ty(TyTag::App) => self.kernel.ty_app(c[0], c[1])?,
            Tag::Ty(TyTag::Fv) => self
                .kernel
                .ty_fv(name.ok_or(SyntaxError::Different)?, c[0])?,
            Tag::Tm(TmTag::Fv) => self
                .kernel
                .tm_fv(name.ok_or(SyntaxError::Different)?, c[0])?,
            Tag::Tm(TmTag::App) => self.kernel.app(c[0], c[1])?,
            Tag::Tm(TmTag::Op1) => self.kernel.op1(
                self.kernel
                    .arena()
                    .op1(input)
                    .ok_or(SyntaxError::Different)?,
                c[0],
            )?,
            Tag::Tm(TmTag::Op2) => self.kernel.op2(
                self.kernel
                    .arena()
                    .op2(input)
                    .ok_or(SyntaxError::Different)?,
                c[0],
                c[1],
            )?,
            Tag::Tm(TmTag::Eq) => {
                self.kernel
                    .eq_at(self.kernel.classifier(input)?, c[0], c[1], c[2])?
            }
            Tag::Tm(TmTag::Eps) => self.kernel.eps(c[0], c[1])?,
            _ => return Err(SyntaxError::Different),
        })
    }
}
