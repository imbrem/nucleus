//! Chosen model types as an untrusted derived layer.
//!
//! The trusted kernel rule [`Kernel::model_spec`] checks one substitution
//! certificate and concludes its output. This module does the mechanical work
//! around that small rule: it reads the type existential from a theorem,
//! constructs its canonical `model` type, recursively builds the substituted
//! predicate and its certificate, and invokes the checked rule.
//!
//! None of the traversal is trusted. A bug can only make the kernel reject the
//! certificate or produce an unintended, still checked substitution.

use std::collections::BTreeMap;

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{
    Kernel, KernelError, KindTag, Ref, Sort, SynFactId, SynRel, Tag, ThmId, TmTag, TyTag,
};

/// A chosen type together with the checked theorem that specifies it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ChosenModel {
    /// The canonical `model name. predicate` type.
    pub ty: Ref,
    /// The quantified predicate before type substitution.
    pub predicate: Ref,
    /// The predicate after replacing its bound type variable with [`ty`](Self::ty).
    pub specification: Ref,
    /// The premise-free theorem concluding [`specification`](Self::specification).
    pub theorem: ThmId,
    /// The substitution certificate retained in the kernel's syntactic cache.
    pub substitution: SynFactId,
    /// The name bound by the source type existential.
    pub name: u64,
}

/// One checked capture-avoiding substitution and its syntactic certificate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Substitution {
    /// Rebuilt expression after substitution.
    pub output: Ref,
    /// Checked syntactic fact relating the input to [`output`](Self::output).
    pub fact: SynFactId,
}

/// A failure in the derived chosen-model construction.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ModelError {
    /// A checked kernel operation rejected the derived construction.
    #[snafu(display("chosen-model construction was rejected: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// The supplied theorem is not a premise-free positive type existential.
    #[snafu(display("theorem {theorem:?} does not conclude one positive type existential"))]
    WrongTheorem {
        /// Rejected theorem slot.
        theorem: ThmId,
    },
    /// The local substitution walker encountered opaque or future syntax.
    #[snafu(display("cannot derive substitution through {tag:?} at {reference:?}"))]
    UnsupportedSyntax {
        /// Row which could not be traversed.
        reference: Ref,
        /// Its stable syntax tag.
        tag: Tag,
    },
}

impl From<KernelError> for ModelError {
    fn from(source: KernelError) -> Self {
        Self::Kernel { source }
    }
}

/// Derived chosen-model operations over a checked Ethane kernel.
pub trait ModelExt {
    /// Opens one premise-free theorem `⊢ ∃type α. P α` at its chosen model.
    ///
    /// The result contains `model α. P α`, the substituted specification, and
    /// a theorem `⊢ P (model α. P α)`. All syntax construction and recursive
    /// substitution happen in this userspace crate; the kernel only checks the
    /// final local certificate through `model_spec`.
    ///
    /// # Errors
    ///
    /// Returns an error unless `theorem` has exactly the required shape, every
    /// reachable predicate row is local traversable syntax, and each checked
    /// constructor and substitution rule accepts the derived evidence.
    fn choose_model(&mut self, theorem: ThmId) -> Result<ChosenModel, ModelError>;
}

impl ModelExt for Kernel {
    fn choose_model(&mut self, theorem: ThmId) -> Result<ChosenModel, ModelError> {
        let conclusion = sole_positive_conclusion(self, theorem)?;
        let tag = self
            .arena()
            .tag(conclusion)
            .ok_or(KernelError::MissingDefinition {
                reference: conclusion,
            })?;
        if tag != Tag::Tm(TmTag::TyExists) {
            return Err(ModelError::WrongTheorem { theorem });
        }
        let name = self
            .arena()
            .name(conclusion)
            .ok_or(ModelError::WrongTheorem { theorem })?;
        let predicate = only_child(self, conclusion)?;
        let ty = self.model(name, predicate)?;
        let star = self.classifier(ty)?;
        // Reuse the predicate's actual free-variable row when it has one.
        // Syntactic substitution deliberately distinguishes duplicate rows
        // with one name, so manufacturing a parallel witness would make every
        // real occurrence look ambiguous. A vacuous existential has no such
        // row and may use a fresh witness safely.
        let variable = match find_free_type_variable(self, predicate, name)? {
            Some(variable) => variable,
            None => self.ty_fv(name, star)?,
        };

        let substitution = substitute(self, variable, ty, predicate)?;
        let specification = substitution.output;
        let fact = substitution.fact;
        let specification_theorem = self.model_spec(theorem, fact)?;

        Ok(ChosenModel {
            ty,
            predicate,
            specification,
            theorem: specification_theorem,
            substitution: fact,
            name,
        })
    }
}

/// Rebuilds `input[var := val]` and constructs the checked syntactic fact.
///
/// This traversal carries no authority: every rebuilt row and every step of
/// its substitution certificate is checked by [`Kernel`]. It is shared by
/// chosen-model opening, beta reduction, and derived packages.
///
/// # Errors
///
/// Returns an error if any reachable row is opaque or unsupported, or if the
/// checked kernel rejects a reconstructed row or certificate step.
pub fn substitute(
    kernel: &mut Kernel,
    variable: Ref,
    replacement: Ref,
    input: Ref,
) -> Result<Substitution, ModelError> {
    let (output, fact) = TypeSubstitution {
        kernel,
        variable,
        replacement,
        memo: BTreeMap::new(),
    }
    .derive(input)?;
    Ok(Substitution { output, fact })
}

/// Eta-expands a function with an exact requested arrow classifier.
///
/// Checked substitution commonly rebuilds a type into fresh but syntactically
/// identical rows. The kernel intentionally does not infer equality merely
/// from that physical shape. This helper constructs `λx. function x` at
/// `function_ty`; ordinary checked application verifies the domain, and
/// [`Kernel::lam_at`] verifies the requested classifier.
///
/// This carries no theorem authority. Callers needing to rewrite a theorem
/// between `function` and the returned eta expansion must separately obtain
/// checked conversion evidence.
///
/// # Errors
///
/// Returns an error unless `function_ty` is an arrow type compatible with
/// `function`, or if no fresh binder name remains.
pub fn eta_expand_at(
    kernel: &mut Kernel,
    function_ty: Ref,
    function: Ref,
) -> Result<Ref, KernelError> {
    let actual = kernel
        .arena()
        .tag(function_ty)
        .ok_or(KernelError::MissingDefinition {
            reference: function_ty,
        })?;
    let mut parts = kernel
        .arena()
        .children(function_ty)
        .ok_or(KernelError::WrongForm {
            reference: function_ty,
            expected: "an arrow type",
            actual,
        })?;
    let domain = parts.next().ok_or(KernelError::WrongForm {
        reference: function_ty,
        expected: "an arrow type",
        actual,
    })?;
    drop(parts);
    let argument = kernel.tm_fv(kernel.fresh_name(&[function_ty, function])?, domain)?;
    let body = kernel.app(function, argument)?;
    kernel.lam_at(function_ty, argument, body)
}

fn find_free_type_variable(
    kernel: &Kernel,
    root: Ref,
    name: u64,
) -> Result<Option<Ref>, ModelError> {
    fn visit(
        kernel: &Kernel,
        input: Ref,
        name: u64,
        seen: &mut BTreeMap<Ref, bool>,
    ) -> Result<Option<Ref>, ModelError> {
        if seen.insert(input, true).is_some() {
            return Ok(None);
        }
        let tag = kernel
            .arena()
            .tag(input)
            .ok_or(KernelError::MissingDefinition { reference: input })?;
        if tag == Tag::Ty(TyTag::Fv) && kernel.arena().name(input) == Some(name) {
            return Ok(Some(input));
        }
        let children: Vec<_> = kernel
            .arena()
            .children(input)
            .ok_or(KernelError::MissingDefinition { reference: input })?
            .collect();

        // The first child of an explicit lambda is its binder. If that binder
        // shadows the selected type name, neither it nor the body is free.
        if matches!(tag, Tag::Ty(TyTag::Lam))
            && children
                .first()
                .is_some_and(|binder| kernel.arena().name(*binder) == Some(name))
        {
            return Ok(None);
        }
        // `model` and the type quantifiers store their binder name directly.
        if matches!(
            tag,
            Tag::Ty(TyTag::Model) | Tag::Tm(TmTag::TyExists | TmTag::TyForall)
        ) && kernel.arena().name(input) == Some(name)
        {
            return Ok(None);
        }
        for child in children {
            if let Some(variable) = visit(kernel, child, name, seen)? {
                return Ok(Some(variable));
            }
        }
        Ok(None)
    }

    visit(kernel, root, name, &mut BTreeMap::new())
}

fn sole_positive_conclusion(kernel: &Kernel, theorem: ThmId) -> Result<Ref, ModelError> {
    let sequent = kernel
        .thm()
        .get(theorem)
        .ok_or(KernelError::MissingTheorem { id: theorem })?;
    if sequent.lhs.rows().next().is_some() {
        return Err(ModelError::WrongTheorem { theorem });
    }
    let mut rows = sequent.rhs.rows();
    let row = rows.next().ok_or(ModelError::WrongTheorem { theorem })?;
    if rows.next().is_some() || row.len() != 1 || !row[0].is_positive() {
        return Err(ModelError::WrongTheorem { theorem });
    }
    let index =
        i32::try_from(row[0].magnitude()).map_err(|_| ModelError::WrongTheorem { theorem })?;
    Ref::new(index).ok_or(ModelError::WrongTheorem { theorem })
}

fn only_child(kernel: &Kernel, input: Ref) -> Result<Ref, ModelError> {
    let mut children = kernel
        .arena()
        .children(input)
        .ok_or(KernelError::MissingDefinition { reference: input })?;
    let child = children.next().ok_or(ModelError::UnsupportedSyntax {
        reference: input,
        tag: kernel
            .arena()
            .tag(input)
            .ok_or(KernelError::MissingDefinition { reference: input })?,
    })?;
    if children.next().is_some() {
        return Err(ModelError::UnsupportedSyntax {
            reference: input,
            tag: kernel
                .arena()
                .tag(input)
                .ok_or(KernelError::MissingDefinition { reference: input })?,
        });
    }
    Ok(child)
}

struct TypeSubstitution<'a> {
    kernel: &'a mut Kernel,
    variable: Ref,
    replacement: Ref,
    memo: BTreeMap<Ref, (Ref, SynFactId)>,
}

impl TypeSubstitution<'_> {
    fn derive(&mut self, input: Ref) -> Result<(Ref, SynFactId), ModelError> {
        if let Some(&result) = self.memo.get(&input) {
            return Ok(result);
        }
        let result = if input == self.variable {
            let fact = self
                .kernel
                .syn_sub_var(None, self.variable, self.replacement)?;
            (self.replacement, fact)
        } else if self.kernel.substitution_fresh(self.variable, input)? {
            let fact = self
                .kernel
                .syn_sub_fresh(None, self.variable, self.replacement, input)?;
            (input, fact)
        } else {
            self.derive_node(input)?
        };
        self.memo.insert(input, result);
        Ok(result)
    }

    fn derive_node(&mut self, input: Ref) -> Result<(Ref, SynFactId), ModelError> {
        let tag = self
            .kernel
            .arena()
            .tag(input)
            .ok_or(KernelError::MissingDefinition { reference: input })?;
        let children: Vec<Ref> = self
            .kernel
            .arena()
            .children(input)
            .ok_or(KernelError::MissingDefinition { reference: input })?
            .collect();

        match tag {
            Tag::Kind(KindTag::Star) | Tag::Ty(TyTag::Bool) | Tag::Tm(TmTag::Bool) => {
                self.unchanged_leaf(input)
            }
            Tag::Ty(TyTag::Fv) => self.unchanged_leaf(input),
            Tag::Kind(KindTag::Arr) => self.binary(input, &children, |kernel, left, right| {
                kernel.kind_arr(left, right)
            }),
            Tag::Ty(TyTag::Arr) => self.binary(input, &children, Kernel::ty_arr),
            Tag::Ty(TyTag::App) => self.binary(input, &children, Kernel::ty_app),
            Tag::Tm(TmTag::App) => self.binary(input, &children, Kernel::app),
            Tag::Tm(TmTag::Op2) => {
                let op = self
                    .kernel
                    .arena()
                    .op2(input)
                    .ok_or(ModelError::UnsupportedSyntax {
                        reference: input,
                        tag,
                    })?;
                self.binary(input, &children, |kernel, left, right| {
                    kernel.op2(op, left, right)
                })
            }
            Tag::Tm(TmTag::Op1) => {
                let op = self
                    .kernel
                    .arena()
                    .op1(input)
                    .ok_or(ModelError::UnsupportedSyntax {
                        reference: input,
                        tag,
                    })?;
                self.unary(input, &children, |kernel, child| kernel.op1(op, child))
            }
            Tag::Tm(TmTag::Fv) => {
                let name = self.name(input, tag)?;
                self.unary(input, &children, |kernel, ty| kernel.tm_fv(name, ty))
            }
            Tag::Tm(TmTag::Eq) => {
                if children.len() != 3 {
                    return Err(ModelError::UnsupportedSyntax {
                        reference: input,
                        tag,
                    });
                }
                let (ty, ty_fact) = self.derive(children[0])?;
                let (left, left_fact) = self.derive(children[1])?;
                let (right, right_fact) = self.derive(children[2])?;
                let bool_ty = self.kernel.classifier(input)?;
                let output = self.kernel.eq(bool_ty, left, right)?;
                let fact = self.kernel.syn_congr(
                    None,
                    SynRel::Syn,
                    Some(self.variable),
                    Some(self.replacement),
                    input,
                    output,
                    &[ty_fact, left_fact, right_fact],
                )?;
                let _ = ty;
                Ok((output, fact))
            }
            Tag::Tm(TmTag::Eps) => self.binary(input, &children, Kernel::eps),
            Tag::Ty(TyTag::Lam) | Tag::Tm(TmTag::Lam) => {
                self.explicit_binder(input, tag, &children)
            }
            Tag::Ty(TyTag::Model) | Tag::Tm(TmTag::TyExists | TmTag::TyForall) => {
                self.implicit_binder(input, tag, &children)
            }
            Tag::Kind(KindTag::Ref) | Tag::Ty(TyTag::Ref) | Tag::Tm(TmTag::Ref) => {
                Err(ModelError::UnsupportedSyntax {
                    reference: input,
                    tag,
                })
            }
            _ => Err(ModelError::UnsupportedSyntax {
                reference: input,
                tag,
            }),
        }
    }

    fn unchanged_leaf(&mut self, input: Ref) -> Result<(Ref, SynFactId), ModelError> {
        let fact = self
            .kernel
            .syn_sub_leaf(None, self.variable, self.replacement, input)?;
        Ok((input, fact))
    }

    fn unary(
        &mut self,
        input: Ref,
        children: &[Ref],
        build: impl FnOnce(&mut Kernel, Ref) -> Result<Ref, KernelError>,
    ) -> Result<(Ref, SynFactId), ModelError> {
        let &[child] = children else {
            return Err(ModelError::UnsupportedSyntax {
                reference: input,
                tag: self
                    .kernel
                    .arena()
                    .tag(input)
                    .ok_or(KernelError::MissingDefinition { reference: input })?,
            });
        };
        let (child, child_fact) = self.derive(child)?;
        let output = build(self.kernel, child)?;
        let fact = self.congr(input, output, &[child_fact])?;
        Ok((output, fact))
    }

    fn binary(
        &mut self,
        input: Ref,
        children: &[Ref],
        build: impl FnOnce(&mut Kernel, Ref, Ref) -> Result<Ref, KernelError>,
    ) -> Result<(Ref, SynFactId), ModelError> {
        let &[left, right] = children else {
            return Err(ModelError::UnsupportedSyntax {
                reference: input,
                tag: self
                    .kernel
                    .arena()
                    .tag(input)
                    .ok_or(KernelError::MissingDefinition { reference: input })?,
            });
        };
        let (left, left_fact) = self.derive(left)?;
        let (right, right_fact) = self.derive(right)?;
        let output = build(self.kernel, left, right)?;
        let fact = self.congr(input, output, &[left_fact, right_fact])?;
        Ok((output, fact))
    }

    fn congr(
        &mut self,
        input: Ref,
        output: Ref,
        children: &[SynFactId],
    ) -> Result<SynFactId, ModelError> {
        Ok(self.kernel.syn_congr(
            None,
            SynRel::Syn,
            Some(self.variable),
            Some(self.replacement),
            input,
            output,
            children,
        )?)
    }

    fn explicit_binder(
        &mut self,
        input: Ref,
        tag: Tag,
        children: &[Ref],
    ) -> Result<(Ref, SynFactId), ModelError> {
        let &[binder, body] = children else {
            return Err(ModelError::UnsupportedSyntax {
                reference: input,
                tag,
            });
        };
        let shadowed = binder == self.variable;
        let substitutes_binder_classifier =
            tag == Tag::Tm(TmTag::Lam) && self.kernel.category(self.variable)? == Sort::Ty;
        let (output_binder, binder_fact) = if shadowed || !substitutes_binder_classifier {
            (binder, self.kernel.syn_refl(None, SynRel::Syn, binder)?)
        } else {
            self.derive(binder)?
        };
        let (output_body, body_fact) = if shadowed {
            (body, self.kernel.syn_refl(None, SynRel::Syn, body)?)
        } else {
            self.derive(body)?
        };
        let output = match tag {
            Tag::Ty(TyTag::Lam) => self.kernel.ty_lam(output_binder, output_body)?,
            Tag::Tm(TmTag::Lam) => {
                // Reuse the recursively substituted classifier rather than
                // letting `lam` append a parallel arrow row. Applications of
                // this lambda refer to the former, and Ethane intentionally
                // does not identify structurally duplicate type rows.
                let input_classifier = self.kernel.classifier(input)?;
                let (output_classifier, _) = self.derive(input_classifier)?;
                self.kernel
                    .lam_at(output_classifier, output_binder, output_body)?
            }
            _ => unreachable!("caller matched explicit binder tags"),
        };
        let fact = self.kernel.syn_binder_congr(
            None,
            SynRel::Syn,
            Some(self.variable),
            Some(self.replacement),
            input,
            output,
            binder_fact,
            body_fact,
        )?;
        Ok((output, fact))
    }

    fn implicit_binder(
        &mut self,
        input: Ref,
        tag: Tag,
        children: &[Ref],
    ) -> Result<(Ref, SynFactId), ModelError> {
        let &[body] = children else {
            return Err(ModelError::UnsupportedSyntax {
                reference: input,
                tag,
            });
        };
        let name = self.name(input, tag)?;
        let variable_tag =
            self.kernel
                .arena()
                .tag(self.variable)
                .ok_or(KernelError::MissingDefinition {
                    reference: self.variable,
                })?;
        let shadowed = variable_tag == Tag::Ty(TyTag::Fv)
            && self.kernel.arena().name(self.variable) == Some(name);
        let witness = if shadowed {
            self.variable
        } else {
            let classifier = self.kernel.classifier(input)?;
            let star = match tag {
                Tag::Ty(TyTag::Model) => classifier,
                Tag::Tm(TmTag::TyExists | TmTag::TyForall) => self.kernel.classifier(classifier)?,
                _ => unreachable!("caller matched implicit binder tags"),
            };
            self.kernel.ty_fv(name, star)?
        };
        let (output_body, body_fact) = if shadowed {
            (body, self.kernel.syn_refl(None, SynRel::Syn, body)?)
        } else {
            self.derive(body)?
        };
        let output = match tag {
            Tag::Ty(TyTag::Model) => self.kernel.model(name, output_body)?,
            Tag::Tm(TmTag::TyExists) => self.kernel.ty_exists(name, output_body)?,
            Tag::Tm(TmTag::TyForall) => self.kernel.ty_forall(name, output_body)?,
            _ => unreachable!("caller matched implicit binder tags"),
        };
        let fact = self.kernel.syn_implicit_binder_congr(
            None,
            SynRel::Syn,
            Some(self.variable),
            Some(self.replacement),
            input,
            output,
            witness,
            body_fact,
        )?;
        Ok((output, fact))
    }

    fn name(&self, input: Ref, tag: Tag) -> Result<u64, ModelError> {
        self.kernel
            .arena()
            .name(input)
            .ok_or(ModelError::UnsupportedSyntax {
                reference: input,
                tag,
            })
    }
}
