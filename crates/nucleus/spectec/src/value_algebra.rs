//! Generic checked propositions for faithful structural-value interpretations.
//!
//! `SpecTec` lowering may initially interpret every structural value in one
//! erased HOL carrier. This module states the constructor injectivity and
//! disjointness obligations needed to make such an interpretation faithful.
//! It constructs syntax only: callers must supply checked proofs or retain the
//! propositions as explicit semantic premises.

use std::sync::Arc;

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{
    Kernel, KernelError, Lit, Ref, SynRel, ThmId,
    builtin::{Op1, Op2},
};
use covalence_logic_hol_derived::{
    EqualityError, ExistsError, ForallError, ModelError, SyntaxError, equality_symmetry,
    forall_elim, introduce_exists, join_alpha_equivalent, join_same_syntax, substitute,
};

use crate::Evidence;

/// One validated constructor in an erased structural-value algebra.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StructuralConstructor {
    operation: Ref,
    arity: usize,
}

impl StructuralConstructor {
    /// Returns the checked curried constructor operation.
    #[must_use]
    pub const fn operation(self) -> Ref {
        self.operation
    }

    /// Returns the number of structural children.
    #[must_use]
    pub const fn arity(self) -> usize {
        self.arity
    }
}

/// Classifiers shared by a single-carrier structural-value interpretation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StructuralValueAlgebra {
    /// Classifier of erased structural values.
    pub value_ty: Ref,
    /// HOL Boolean classifier.
    pub bool_ty: Ref,
}

/// Immutable checked shape of one structural field-pattern graph.
///
/// The descriptor retains the exact binders used by its predicate so later
/// proof construction does not need to reconstruct alpha-equivalent syntax.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StructuralFieldPattern {
    values: StructuralValueAlgebra,
    record_constructor: StructuralConstructor,
    selected: usize,
    pattern_constructor: StructuralConstructor,
    fields: Arc<[Ref]>,
    predicate: Ref,
}

/// A structural field pattern paired with its checked premise-free evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProvedStructuralFieldPattern {
    pattern: StructuralFieldPattern,
    evidence: Evidence,
}

impl ProvedStructuralFieldPattern {
    /// Returns the exact immutable pattern proved by the evidence.
    #[must_use]
    pub const fn pattern(&self) -> &StructuralFieldPattern {
        &self.pattern
    }

    /// Returns the checked application of the pattern to its concrete values.
    #[must_use]
    pub const fn evidence(&self) -> Evidence {
        self.evidence
    }
}

impl StructuralFieldPattern {
    /// Returns the structural value algebra used by this graph.
    #[must_use]
    pub const fn algebra(&self) -> StructuralValueAlgebra {
        self.values
    }

    /// Returns the checked binary graph predicate.
    #[must_use]
    pub const fn predicate(&self) -> Ref {
        self.predicate
    }

    /// Returns the record-like constructor matched by this graph.
    #[must_use]
    pub const fn record_constructor(&self) -> StructuralConstructor {
        self.record_constructor
    }

    /// Returns the selected record-field index.
    #[must_use]
    pub const fn selected(&self) -> usize {
        self.selected
    }

    /// Returns the unary constructor required at the selected field.
    #[must_use]
    pub const fn pattern_constructor(&self) -> StructuralConstructor {
        self.pattern_constructor
    }

    /// Returns the exact existential field binders retained by the predicate.
    #[must_use]
    pub fn field_binders(&self) -> &[Ref] {
        &self.fields
    }
}

/// Immutable obligations for one finite structural-constructor vocabulary.
///
/// The propositions contain every constructor's injectivity law followed by
/// disjointness for every unordered pair, in input order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StructuralConstructorLaws {
    constructors: Arc<[StructuralConstructor]>,
    propositions: Arc<[Ref]>,
}

/// One finite structural sequence and its exact membership-law proposition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FiniteSequenceLaw {
    list: Ref,
    elements: Arc<[Ref]>,
    binder: Ref,
    proposition: Ref,
}

impl FiniteSequenceLaw {
    /// Returns the structural list term.
    #[must_use]
    pub const fn list(&self) -> Ref {
        self.list
    }

    /// Returns the elements in semantic order.
    #[must_use]
    pub fn elements(&self) -> &[Ref] {
        &self.elements
    }

    /// Returns `forall x. member x list = (x=e0 or ...)`.
    #[must_use]
    pub const fn proposition(&self) -> Ref {
        self.proposition
    }
}

/// A checked membership operation over one structural-value carrier.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StructuralSequenceAlgebra {
    values: StructuralValueAlgebra,
    member: Ref,
}

impl StructuralSequenceAlgebra {
    /// Validates `member : value -> value -> bool`.
    ///
    /// # Errors
    ///
    /// Returns an error unless `member` has the exact required classifier.
    /// `kernel` is unchanged on failure.
    pub fn new(
        kernel: &mut Kernel,
        values: StructuralValueAlgebra,
        member: Ref,
    ) -> Result<Self, KernelError> {
        let mut staged = kernel.fork();
        let tail = staged.ty_arr(values.value_ty, values.bool_ty)?;
        let expected = staged.ty_arr(values.value_ty, tail)?;
        let actual = staged.classifier(member)?;
        join_same_syntax(&mut staged, actual, expected)
            .map_err(|_| KernelError::ClassifierMismatch { expected, actual })?;
        *kernel = staged;
        Ok(Self { values, member })
    }

    /// Returns the checked membership predicate.
    #[must_use]
    pub const fn member(self) -> Ref {
        self.member
    }

    /// Constructs exact finite membership semantics for one list constructor.
    ///
    /// For elements `[e0, ...]`, the proposition is
    /// `forall x. member x (list e0 ...) = (x=e0 or ...)`. The empty
    /// disjunction is false. This creates no theorem fact.
    ///
    /// # Errors
    ///
    /// Returns an error unless `list_constructor` belongs to this value
    /// algebra with arity equal to `elements.len()`, every element has the
    /// value classifier, and checked construction succeeds. `kernel` is
    /// unchanged on failure.
    pub fn membership_law(
        self,
        kernel: &mut Kernel,
        list_constructor: StructuralConstructor,
        elements: &[Ref],
    ) -> Result<FiniteSequenceLaw, KernelError> {
        let mut staged = kernel.fork();
        self.values
            .require_constructor(&mut staged, list_constructor)?;
        if list_constructor.arity != elements.len() {
            return Err(KernelError::InvalidTheoremRule {
                rule: "finite sequence constructor arity",
            });
        }
        for &element in elements {
            let actual = staged.classifier(element)?;
            join_same_syntax(&mut staged, actual, self.values.value_ty).map_err(|_| {
                KernelError::ClassifierMismatch {
                    expected: self.values.value_ty,
                    actual,
                }
            })?;
        }
        let list = apply(&mut staged, list_constructor.operation, elements)?;
        let mut roots = vec![
            self.values.value_ty,
            self.values.bool_ty,
            self.member,
            list_constructor.operation,
            list,
        ];
        roots.extend_from_slice(elements);
        let candidate = staged.tm_fv(staged.fresh_name(&roots)?, self.values.value_ty)?;
        let contains = apply(&mut staged, self.member, &[candidate, list])?;
        let mut enumerated = staged.bool(self.values.bool_ty, false)?;
        for &element in elements.iter().rev() {
            let equal = staged.eq(self.values.bool_ty, candidate, element)?;
            enumerated = staged.op2(Op2::Or, equal, enumerated)?;
        }
        let exact = staged.eq(self.values.bool_ty, contains, enumerated)?;
        let proposition = staged.forall_tm(self.values.bool_ty, candidate, exact)?;
        let law = FiniteSequenceLaw {
            list,
            elements: Arc::from(elements),
            binder: candidate,
            proposition,
        };
        *kernel = staged;
        Ok(law)
    }

    /// Constructs `forall x. not (member x list)`.
    ///
    /// # Errors
    ///
    /// Returns an error unless `list` has the value classifier or checked
    /// construction fails. `kernel` is unchanged on failure.
    pub fn no_members(self, kernel: &mut Kernel, list: Ref) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let actual = staged.classifier(list)?;
        join_same_syntax(&mut staged, actual, self.values.value_ty).map_err(|_| {
            KernelError::ClassifierMismatch {
                expected: self.values.value_ty,
                actual,
            }
        })?;
        let candidate = staged.tm_fv(
            staged.fresh_name(&[self.values.value_ty, self.values.bool_ty, self.member, list])?,
            self.values.value_ty,
        )?;
        let contains = apply(&mut staged, self.member, &[candidate, list])?;
        let absent = staged.op1(Op1::Not, contains)?;
        let proposition = staged.forall_tm(self.values.bool_ty, candidate, absent)?;
        *kernel = staged;
        Ok(proposition)
    }

    /// Derives absence of members from checked exact membership semantics for
    /// an empty finite sequence.
    ///
    /// Every premise of `membership_fact` remains visible. No property of the
    /// membership operation is assumed beyond the supplied checked theorem.
    ///
    /// # Errors
    ///
    /// Returns an error unless `law` has no elements and `membership_fact`
    /// positively proves its exact proposition, or a checked specialization,
    /// equality, contradiction, universal, or alignment step fails. `kernel`
    /// is unchanged on failure.
    pub fn prove_empty_has_no_members(
        self,
        kernel: &mut Kernel,
        law: &FiniteSequenceLaw,
        membership_fact: ThmId,
    ) -> Result<Evidence, StructuralValueProofError> {
        if !law.elements.is_empty() {
            return Err(StructuralValueProofError::NonemptySequence);
        }
        let mut staged = kernel.fork();
        let source = positive_conclusion(&staged, membership_fact)?;
        let membership_fact = staged.copy_theorem(membership_fact)?;
        if source != law.proposition {
            join_alpha_equivalent(&mut staged, source, law.proposition)?;
            staged.convert_conclusions(membership_fact, source, law.proposition)?;
        }
        let candidate = staged.tm_fv(
            staged.fresh_name(&[
                self.values.value_ty,
                self.values.bool_ty,
                self.member,
                law.list,
                law.binder,
                law.proposition,
            ])?,
            self.values.value_ty,
        )?;
        let specialized = forall_elim(&mut staged, membership_fact, candidate)?;
        let contains = apply(&mut staged, self.member, &[candidate, law.list])?;
        let falsehood = staged.bool(self.values.bool_ty, false)?;
        let equality = staged.eq(self.values.bool_ty, contains, falsehood)?;
        join_alpha_equivalent(&mut staged, specialized.proposition, equality)?;
        staged.convert_conclusions(specialized.theorem, specialized.proposition, equality)?;
        let assumed = staged.identity(positive(contains))?;
        let impossible = staged.eq_mp(specialized.theorem, assumed)?;
        let false_left = staged.false_left(positive(falsehood))?;
        let contradiction = staged.cut(impossible, false_left, positive(falsehood))?;
        staged.not_right(contradiction, positive(contains))?;
        let absent = staged.op1(Op1::Not, contains)?;
        let flattened = staged.flatten_conclusion(contradiction, positive(contains).negated())?;
        let absent_fact = staged.fold_conclusion(flattened, positive(absent))?;
        let direct = staged.forall_tm(self.values.bool_ty, candidate, absent)?;
        let theorem = staged.forall_intro_at(absent_fact, candidate, direct)?;
        let canonical = self.no_members(&mut staged, law.list)?;
        join_alpha_equivalent(&mut staged, direct, canonical)?;
        staged.convert_conclusions(theorem, direct, canonical)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: canonical,
            theorem,
            holds: true,
        })
    }

    /// Derives membership of the element at `index` from checked exact finite
    /// membership semantics.
    ///
    /// Every premise of `membership_fact` remains visible. Element equality is
    /// discharged by checked reflexivity, then introduced into the finite
    /// disjunction and transported through the membership equation.
    ///
    /// # Errors
    ///
    /// Returns an error if `index` is out of bounds, `membership_fact` does not
    /// positively prove `law`, or checked specialization, equality,
    /// disjunction, or alignment fails. `kernel` is unchanged on failure.
    pub fn prove_member_at(
        self,
        kernel: &mut Kernel,
        law: &FiniteSequenceLaw,
        membership_fact: ThmId,
        index: usize,
    ) -> Result<Evidence, StructuralValueProofError> {
        let Some(&element) = law.elements.get(index) else {
            return Err(StructuralValueProofError::Index {
                index,
                len: law.elements.len(),
            });
        };
        let mut staged = kernel.fork();
        let source = positive_conclusion(&staged, membership_fact)?;
        let membership_fact = staged.copy_theorem(membership_fact)?;
        if source != law.proposition {
            join_alpha_equivalent(&mut staged, source, law.proposition)?;
            staged.convert_conclusions(membership_fact, source, law.proposition)?;
        }
        let specialized = forall_elim(&mut staged, membership_fact, element)?;
        let contains = apply(&mut staged, self.member, &[element, law.list])?;
        let mut suffixes = vec![staged.bool(self.values.bool_ty, false)?];
        let mut equalities = Vec::with_capacity(law.elements.len());
        for &candidate in law.elements.iter().rev() {
            let equal = staged.eq(self.values.bool_ty, element, candidate)?;
            equalities.push(equal);
            let tail = *suffixes.last().ok_or(KernelError::InvalidTheoremRule {
                rule: "finite sequence membership suffix",
            })?;
            suffixes.push(staged.op2(Op2::Or, equal, tail)?);
        }
        suffixes.reverse();
        equalities.reverse();
        let enumerated = suffixes[0];
        let equality = staged.eq(self.values.bool_ty, contains, enumerated)?;
        join_alpha_equivalent(&mut staged, specialized.proposition, equality)?;
        staged.convert_conclusions(specialized.theorem, specialized.proposition, equality)?;

        let reflexive = staged.refl(self.values.bool_ty, element)?;
        join_alpha_equivalent(&mut staged, reflexive.equality, equalities[index])?;
        staged.convert_conclusions(reflexive.theorem, reflexive.equality, equalities[index])?;
        let mut disjunction = staged.copy_theorem(reflexive.theorem)?;
        staged.weaken(disjunction, &[], &[positive(suffixes[index + 1])])?;
        disjunction = staged.or_right(disjunction, positive(suffixes[index]))?;
        for outer in (0..index).rev() {
            staged.weaken(disjunction, &[], &[positive(equalities[outer])])?;
            disjunction = staged.or_right(disjunction, positive(suffixes[outer]))?;
        }
        let reversed = equality_symmetry(&mut staged, self.values.bool_ty, specialized.theorem)?;
        let theorem = staged.eq_mp(reversed.theorem, disjunction)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: contains,
            theorem,
            holds: true,
        })
    }
}

/// Failure to derive a checked structural-value algebra law.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum StructuralValueProofError {
    /// Empty-sequence elimination was requested for a nonempty law.
    #[snafu(display("expected an empty finite-sequence law"))]
    NonemptySequence,
    /// The selected finite-sequence element does not exist.
    #[snafu(display("sequence index {index} is out of bounds for length {len}"))]
    Index {
        /// Requested element index.
        index: usize,
        /// Actual sequence length.
        len: usize,
    },
    /// A checked kernel operation failed.
    #[snafu(transparent)]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// Universal specialization failed.
    #[snafu(transparent)]
    Forall {
        /// Underlying derived universal-elimination failure.
        source: ForallError,
    },
    /// Checked equality symmetry failed.
    #[snafu(transparent)]
    Equality {
        /// Underlying derived equality failure.
        source: EqualityError,
    },
    /// Existential introduction failed.
    #[snafu(transparent)]
    Exists {
        /// Underlying derived existential failure.
        source: ExistsError,
    },
    /// Capture-avoiding substitution failed.
    #[snafu(transparent)]
    Model {
        /// Underlying derived model operation failure.
        source: ModelError,
    },
    /// Checked formulas could not be aligned.
    #[snafu(transparent)]
    Syntax {
        /// Underlying alpha-equivalence failure.
        source: SyntaxError,
    },
}

fn positive(proposition: Ref) -> Lit {
    Lit::positive(proposition.get())
}

fn positive_conclusion(kernel: &Kernel, theorem: ThmId) -> Result<Ref, KernelError> {
    let theorem = kernel
        .thm()
        .get(theorem)
        .ok_or(KernelError::MissingTheorem { id: theorem })?;
    let mut conclusions = theorem.rhs.rows();
    let Some([literal]) = conclusions.next() else {
        return Err(KernelError::InvalidTheoremRule {
            rule: "structural value proof unit conclusion",
        });
    };
    if conclusions.next().is_some() || !literal.is_positive() {
        return Err(KernelError::InvalidTheoremRule {
            rule: "structural value proof positive conclusion",
        });
    }
    Ref::new(literal.magnitude().cast_signed()).ok_or(KernelError::InvalidTheoremRule {
        rule: "structural value proof conclusion reference",
    })
}

impl StructuralConstructorLaws {
    /// Returns the exact constructor vocabulary covered by these laws.
    #[must_use]
    pub fn constructors(&self) -> &[StructuralConstructor] {
        &self.constructors
    }

    /// Returns the injectivity and pairwise-disjointness propositions.
    #[must_use]
    pub fn propositions(&self) -> &[Ref] {
        &self.propositions
    }
}

impl StructuralValueAlgebra {
    /// Constructs and retains the exact shape of a structural field pattern.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as
    /// [`Self::field_pattern_graph`]. `kernel` is unchanged on failure.
    pub fn field_pattern(
        self,
        kernel: &mut Kernel,
        record_constructor: StructuralConstructor,
        selected: usize,
        pattern_constructor: StructuralConstructor,
    ) -> Result<StructuralFieldPattern, KernelError> {
        self.field_pattern_avoiding(
            kernel,
            record_constructor,
            selected,
            pattern_constructor,
            &[],
        )
    }

    /// Constructs a binary graph matching one constructor field against a
    /// unary structural pattern.
    ///
    /// For a record-like constructor `R` and unary pattern constructor `P`,
    /// the result is
    /// `lambda record output. exists fields. record = R(fields) and
    /// fields[selected] = P(output)`. Constructor meaning remains explicit;
    /// this method creates syntax and no theorem fact.
    ///
    /// # Errors
    ///
    /// Returns an error unless both constructors belong to this algebra, the
    /// pattern is unary, `selected` names a record field, and checked HOL
    /// construction succeeds. `kernel` is unchanged on failure.
    pub fn field_pattern_graph(
        self,
        kernel: &mut Kernel,
        record_constructor: StructuralConstructor,
        selected: usize,
        pattern_constructor: StructuralConstructor,
    ) -> Result<Ref, KernelError> {
        self.field_pattern(kernel, record_constructor, selected, pattern_constructor)
            .map(|pattern| pattern.predicate)
    }

    fn field_pattern_avoiding(
        self,
        kernel: &mut Kernel,
        record_constructor: StructuralConstructor,
        selected: usize,
        pattern_constructor: StructuralConstructor,
        avoid: &[Ref],
    ) -> Result<StructuralFieldPattern, KernelError> {
        let mut staged = kernel.fork();
        self.require_constructor(&mut staged, record_constructor)?;
        self.require_constructor(&mut staged, pattern_constructor)?;
        if selected >= record_constructor.arity {
            return Err(KernelError::InvalidTheoremRule {
                rule: "structural field pattern index",
            });
        }
        if pattern_constructor.arity != 1 {
            return Err(KernelError::InvalidTheoremRule {
                rule: "structural field pattern arity",
            });
        }
        let roots = [
            self.value_ty,
            self.bool_ty,
            record_constructor.operation,
            pattern_constructor.operation,
        ]
        .into_iter()
        .chain(avoid.iter().copied())
        .collect::<Vec<_>>();
        let first = staged.fresh_name(&roots)?;
        let record = staged.tm_fv(first, self.value_ty)?;
        let output = staged.tm_fv(
            first.checked_add(1).ok_or(KernelError::TooManyNames)?,
            self.value_ty,
        )?;
        let mut fields = Vec::with_capacity(record_constructor.arity);
        for offset in 0..record_constructor.arity {
            let offset = u64::try_from(offset).map_err(|_| KernelError::TooManyNames)?;
            fields.push(
                staged.tm_fv(
                    first
                        .checked_add(2)
                        .and_then(|name| name.checked_add(offset))
                        .ok_or(KernelError::TooManyNames)?,
                    self.value_ty,
                )?,
            );
        }
        let constructed = apply(&mut staged, record_constructor.operation, &fields)?;
        let record_equality = staged.eq(self.bool_ty, record, constructed)?;
        let pattern = apply(&mut staged, pattern_constructor.operation, &[output])?;
        let field_equality = staged.eq(self.bool_ty, fields[selected], pattern)?;
        let mut body = staged.op2(Op2::And, record_equality, field_equality)?;
        for &field in fields.iter().rev() {
            body = staged.exists_tm(field, body)?;
        }
        let output_predicate_ty = staged.ty_arr(self.value_ty, self.bool_ty)?;
        let by_output = staged.lam_at(output_predicate_ty, output, body)?;
        let graph_ty = staged.ty_arr(self.value_ty, output_predicate_ty)?;
        let graph = staged.lam_at(graph_ty, record, by_output)?;
        let pattern = StructuralFieldPattern {
            values: self,
            record_constructor,
            selected,
            pattern_constructor,
            fields: Arc::from(fields),
            predicate: graph,
        };
        *kernel = staged;
        Ok(pattern)
    }

    /// Proves an exact constructed value satisfies a structural field pattern.
    ///
    /// The returned descriptor is allocated fresh for `fields` and `output`.
    /// Its evidence proves the descriptor's binary predicate applied to the
    /// constructed record and `output`, with no premises.
    ///
    /// # Errors
    ///
    /// Returns an error unless `fields` exactly fill `record_constructor`, the
    /// selected field is the unary `pattern_constructor` applied to `output`,
    /// and every checked proof step succeeds. `kernel` is unchanged on failure.
    #[allow(clippy::too_many_lines)]
    pub fn prove_field_pattern(
        self,
        kernel: &mut Kernel,
        record_constructor: StructuralConstructor,
        fields: &[Ref],
        selected: usize,
        pattern_constructor: StructuralConstructor,
        output: Ref,
    ) -> Result<ProvedStructuralFieldPattern, StructuralValueProofError> {
        let mut staged = kernel.fork();
        self.require_constructor(&mut staged, record_constructor)?;
        self.require_constructor(&mut staged, pattern_constructor)?;
        if fields.len() != record_constructor.arity || selected >= fields.len() {
            return Err(KernelError::InvalidTheoremRule {
                rule: "structural field pattern proof shape",
            }
            .into());
        }
        if pattern_constructor.arity != 1 {
            return Err(KernelError::InvalidTheoremRule {
                rule: "structural field pattern proof arity",
            }
            .into());
        }
        let record = apply(&mut staged, record_constructor.operation, fields)?;
        let pattern_value = apply(&mut staged, pattern_constructor.operation, &[output])?;
        join_same_syntax(&mut staged, fields[selected], pattern_value)?;
        let mut avoid = vec![record, output, pattern_value];
        avoid.extend_from_slice(fields);
        let pattern = self.field_pattern_avoiding(
            &mut staged,
            record_constructor,
            selected,
            pattern_constructor,
            &avoid,
        )?;

        let rebuilt_record = apply(&mut staged, record_constructor.operation, fields)?;
        let record_equality = staged.eq(self.bool_ty, record, rebuilt_record)?;
        let record_reflexive = staged.refl(self.bool_ty, record)?;
        join_same_syntax(&mut staged, record_reflexive.equality, record_equality)?;
        staged.convert_conclusions(
            record_reflexive.theorem,
            record_reflexive.equality,
            record_equality,
        )?;
        let rebuilt_pattern = apply(&mut staged, pattern_constructor.operation, &[output])?;
        let field_equality = staged.eq(self.bool_ty, fields[selected], rebuilt_pattern)?;
        let field_reflexive = staged.refl(self.bool_ty, fields[selected])?;
        join_same_syntax(&mut staged, field_reflexive.equality, field_equality)?;
        staged.convert_conclusions(
            field_reflexive.theorem,
            field_reflexive.equality,
            field_equality,
        )?;
        let concrete = staged.op2(Op2::And, record_equality, field_equality)?;
        let mut theorem = staged.and_right(
            record_reflexive.theorem,
            field_reflexive.theorem,
            positive(concrete),
        )?;
        let mut proposition = concrete;
        for index in (0..fields.len()).rev() {
            let arguments = fields[..index]
                .iter()
                .copied()
                .chain(pattern.fields[index..].iter().copied())
                .collect::<Vec<_>>();
            let constructed = apply(&mut staged, record_constructor.operation, &arguments)?;
            let record_equality = staged.eq(self.bool_ty, record, constructed)?;
            let selected_pattern = apply(&mut staged, pattern_constructor.operation, &[output])?;
            let field_equality = staged.eq(self.bool_ty, arguments[selected], selected_pattern)?;
            let mut body = staged.op2(Op2::And, record_equality, field_equality)?;
            for &later in pattern.fields[index + 1..].iter().rev() {
                body = staged.exists_tm(later, body)?;
            }
            let introduced = introduce_exists(
                &mut staged,
                theorem,
                pattern.fields[index],
                body,
                fields[index],
            )?;
            theorem = introduced.theorem;
            proposition = introduced.proposition;
        }
        let (application, reduced) =
            reduce_binary_application(&mut staged, pattern.predicate, record, output)?;
        join_alpha_equivalent(&mut staged, proposition, reduced)?;
        staged.convert_conclusions(theorem, proposition, reduced)?;
        staged.convert_conclusions(theorem, reduced, application)?;
        let proved = ProvedStructuralFieldPattern {
            pattern,
            evidence: Evidence {
                proposition: application,
                theorem,
                holds: true,
            },
        };
        *kernel = staged;
        Ok(proved)
    }

    /// Constructs the complete constructor-separation obligations for a finite
    /// vocabulary.
    ///
    /// The result contains one injectivity proposition per constructor and one
    /// disjointness proposition per unordered constructor pair. It does not
    /// claim exhaustiveness, sequence-operation laws, or that any proposition
    /// has been proved.
    ///
    /// # Errors
    ///
    /// Returns an error if a constructor is duplicated or invalid for this
    /// algebra, or any checked proposition construction fails. `kernel` is
    /// unchanged on failure.
    pub fn constructor_laws(
        self,
        kernel: &mut Kernel,
        constructors: &[StructuralConstructor],
    ) -> Result<StructuralConstructorLaws, KernelError> {
        let mut staged = kernel.fork();
        for (index, &constructor) in constructors.iter().enumerate() {
            self.require_constructor(&mut staged, constructor)?;
            if constructors[..index].contains(&constructor) {
                return Err(KernelError::InvalidTheoremRule {
                    rule: "duplicate structural constructor law",
                });
            }
        }
        let pair_count = constructors
            .len()
            .checked_mul(constructors.len().saturating_sub(1))
            .and_then(|count| count.checked_div(2))
            .ok_or(KernelError::TooManyNames)?;
        let mut propositions = Vec::with_capacity(
            constructors
                .len()
                .checked_add(pair_count)
                .ok_or(KernelError::TooManyNames)?,
        );
        for (index, &constructor) in constructors.iter().enumerate() {
            propositions.push(self.injective(&mut staged, constructor)?);
            for &other in &constructors[index + 1..] {
                propositions.push(self.disjoint(&mut staged, constructor, other)?);
            }
        }
        let laws = StructuralConstructorLaws {
            constructors: Arc::from(constructors),
            propositions: Arc::from(propositions),
        };
        *kernel = staged;
        Ok(laws)
    }

    /// Validates a curried `value^arity -> value` constructor.
    ///
    /// # Errors
    ///
    /// Returns an error unless `operation` has the exact classifier induced by
    /// `arity`. `kernel` is unchanged on failure.
    pub fn constructor(
        self,
        kernel: &mut Kernel,
        operation: Ref,
        arity: usize,
    ) -> Result<StructuralConstructor, KernelError> {
        let mut staged = kernel.fork();
        let mut expected = self.value_ty;
        for _ in 0..arity {
            expected = staged.ty_arr(self.value_ty, expected)?;
        }
        let actual = staged.classifier(operation)?;
        join_same_syntax(&mut staged, actual, expected)
            .map_err(|_| KernelError::ClassifierMismatch { expected, actual })?;
        *kernel = staged;
        Ok(StructuralConstructor { operation, arity })
    }

    /// Constructs the injectivity proposition for one constructor.
    ///
    /// For arity `n`, the result is
    /// `forall xs ys. constructor(xs) = constructor(ys) -> and_i xs[i] = ys[i]`.
    /// Nullary constructor injectivity reduces to an implication with `true`
    /// consequent.
    ///
    /// # Errors
    ///
    /// Returns an error if `constructor` is not valid for this algebra, fresh
    /// variables cannot be allocated, or a checked HOL constructor fails.
    /// `kernel` is unchanged on failure.
    pub fn injective(
        self,
        kernel: &mut Kernel,
        constructor: StructuralConstructor,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        self.require_constructor(&mut staged, constructor)?;
        let (left, right) = self.arguments(&mut staged, constructor, constructor)?;
        let left_value = apply(&mut staged, constructor.operation, &left)?;
        let right_value = apply(&mut staged, constructor.operation, &right)?;
        let equal_values = staged.eq(self.bool_ty, left_value, right_value)?;
        let mut equal_fields = staged.bool(self.bool_ty, true)?;
        for (&left, &right) in left.iter().zip(&right).rev() {
            let equal = staged.eq(self.bool_ty, left, right)?;
            equal_fields = staged.op2(Op2::And, equal, equal_fields)?;
        }
        let body = staged.op2(Op2::Imp, equal_values, equal_fields)?;
        let proposition = quantify(&mut staged, self.bool_ty, &left, &right, body)?;
        *kernel = staged;
        Ok(proposition)
    }

    /// Constructs disjointness of two structural constructors.
    ///
    /// The result is `forall xs ys. not (left(xs) = right(ys))` and supports
    /// independently chosen arities.
    ///
    /// # Errors
    ///
    /// Returns an error if either constructor belongs to another algebra,
    /// fresh variables cannot be allocated, or checked construction fails.
    /// `kernel` is unchanged on failure.
    pub fn disjoint(
        self,
        kernel: &mut Kernel,
        left_constructor: StructuralConstructor,
        right_constructor: StructuralConstructor,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        self.require_constructor(&mut staged, left_constructor)?;
        self.require_constructor(&mut staged, right_constructor)?;
        let (left, right) = self.arguments(&mut staged, left_constructor, right_constructor)?;
        let left_value = apply(&mut staged, left_constructor.operation, &left)?;
        let right_value = apply(&mut staged, right_constructor.operation, &right)?;
        let equality = staged.eq(self.bool_ty, left_value, right_value)?;
        let body = staged.op1(Op1::Not, equality)?;
        let proposition = quantify(&mut staged, self.bool_ty, &left, &right, body)?;
        *kernel = staged;
        Ok(proposition)
    }

    fn require_constructor(
        self,
        kernel: &mut Kernel,
        constructor: StructuralConstructor,
    ) -> Result<(), KernelError> {
        self.constructor(kernel, constructor.operation, constructor.arity)?;
        Ok(())
    }

    fn arguments(
        self,
        kernel: &mut Kernel,
        left: StructuralConstructor,
        right: StructuralConstructor,
    ) -> Result<(Vec<Ref>, Vec<Ref>), KernelError> {
        let first =
            kernel.fresh_name(&[self.value_ty, self.bool_ty, left.operation, right.operation])?;
        let count = left
            .arity
            .checked_add(right.arity)
            .ok_or(KernelError::TooManyNames)?;
        let mut variables = Vec::with_capacity(count);
        for offset in 0..count {
            let offset = u64::try_from(offset).map_err(|_| KernelError::TooManyNames)?;
            variables.push(kernel.tm_fv(
                first.checked_add(offset).ok_or(KernelError::TooManyNames)?,
                self.value_ty,
            )?);
        }
        let right = variables.split_off(left.arity);
        Ok((variables, right))
    }
}

fn apply(kernel: &mut Kernel, function: Ref, arguments: &[Ref]) -> Result<Ref, KernelError> {
    arguments.iter().try_fold(function, |function, &argument| {
        kernel.app(function, argument)
    })
}

fn reduce_binary_application(
    kernel: &mut Kernel,
    predicate: Ref,
    left: Ref,
    right: Ref,
) -> Result<(Ref, Ref), StructuralValueProofError> {
    let mut outer = kernel
        .arena()
        .children(predicate)
        .ok_or(KernelError::InvalidTheoremRule {
            rule: "structural field pattern outer lambda",
        })?;
    let left_binder = outer.next().ok_or(KernelError::InvalidTheoremRule {
        rule: "structural field pattern left binder",
    })?;
    let outer_body = outer.next().ok_or(KernelError::InvalidTheoremRule {
        rule: "structural field pattern outer body",
    })?;
    drop(outer);
    let outer_application = kernel.app(predicate, left)?;
    let outer_reduced = substitute(kernel, left_binder, left, outer_body)?;
    let outer_beta = kernel.tm_beta_fact(None, outer_application, outer_reduced.fact)?;
    kernel.union_syn_fact(outer_beta)?;
    let application = kernel.app(outer_application, right)?;
    let intermediate = kernel.app(outer_reduced.output, right)?;
    let right_reflexive = kernel.syn_refl(None, SynRel::Syn, right)?;
    let congruence = kernel.syn_congr(
        None,
        SynRel::Conv,
        None,
        None,
        application,
        intermediate,
        &[outer_beta, right_reflexive],
    )?;
    kernel.union_syn_fact(congruence)?;
    let mut inner =
        kernel
            .arena()
            .children(outer_reduced.output)
            .ok_or(KernelError::InvalidTheoremRule {
                rule: "structural field pattern inner lambda",
            })?;
    let right_binder = inner.next().ok_or(KernelError::InvalidTheoremRule {
        rule: "structural field pattern right binder",
    })?;
    let inner_body = inner.next().ok_or(KernelError::InvalidTheoremRule {
        rule: "structural field pattern inner body",
    })?;
    drop(inner);
    let reduced = substitute(kernel, right_binder, right, inner_body)?;
    let inner_beta = kernel.tm_beta_fact(None, intermediate, reduced.fact)?;
    kernel.union_syn_fact(inner_beta)?;
    let conversion = kernel.syn_trans(None, congruence, inner_beta)?;
    kernel.union_syn_fact(conversion)?;
    Ok((application, reduced.output))
}

fn quantify(
    kernel: &mut Kernel,
    bool_ty: Ref,
    left: &[Ref],
    right: &[Ref],
    mut body: Ref,
) -> Result<Ref, KernelError> {
    for &variable in right.iter().rev().chain(left.iter().rev()) {
        body = kernel.forall_tm(bool_ty, variable, body)?;
    }
    Ok(body)
}

#[cfg(test)]
mod tests {
    use super::{StructuralSequenceAlgebra, StructuralValueAlgebra, apply};
    use crate::EvidenceScope;
    use covalence_logic_hol::Kernel;

    #[test]
    fn structural_faithfulness_laws_are_generic_checked_and_transactional() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let value_ty = kernel.ty_fv(1, star).unwrap();
        let unary_ty = kernel.ty_arr(value_ty, value_ty).unwrap();
        let binary_tail = kernel.ty_arr(value_ty, value_ty).unwrap();
        let binary_ty = kernel.ty_arr(value_ty, binary_tail).unwrap();
        let member_tail = kernel.ty_arr(value_ty, bool_ty).unwrap();
        let member_ty = kernel.ty_arr(value_ty, member_tail).unwrap();
        let empty = kernel.tm_fv(9, value_ty).unwrap();
        let unary = kernel.tm_fv(10, unary_ty).unwrap();
        let binary = kernel.tm_fv(11, binary_ty).unwrap();
        let member = kernel.tm_fv(13, member_ty).unwrap();
        let algebra = StructuralValueAlgebra { value_ty, bool_ty };
        let empty = algebra.constructor(&mut kernel, empty, 0).unwrap();
        let unary = algebra.constructor(&mut kernel, unary, 1).unwrap();
        let binary = algebra.constructor(&mut kernel, binary, 2).unwrap();
        let injective = algebra.injective(&mut kernel, binary).unwrap();
        let disjoint = algebra.disjoint(&mut kernel, unary, binary).unwrap();
        assert_eq!(kernel.classifier(injective).unwrap(), bool_ty);
        assert_eq!(kernel.classifier(disjoint).unwrap(), bool_ty);

        let sequences = StructuralSequenceAlgebra::new(&mut kernel, algebra, member).unwrap();
        let empty_law = sequences.membership_law(&mut kernel, empty, &[]).unwrap();
        let element = kernel.tm_fv(12, value_ty).unwrap();
        let singleton_law = sequences
            .membership_law(&mut kernel, unary, &[element])
            .unwrap();
        let other_element = kernel.tm_fv(14, value_ty).unwrap();
        let pair_law = sequences
            .membership_law(&mut kernel, binary, &[element, other_element])
            .unwrap();
        assert!(empty_law.elements().is_empty());
        assert_eq!(singleton_law.elements(), &[element]);
        assert_eq!(kernel.classifier(empty_law.proposition()).unwrap(), bool_ty);
        assert_eq!(
            kernel.classifier(singleton_law.proposition()).unwrap(),
            bool_ty
        );
        let empty_fact = kernel
            .identity(super::positive(empty_law.proposition()))
            .unwrap();
        let no_members = sequences
            .prove_empty_has_no_members(&mut kernel, &empty_law, empty_fact)
            .unwrap();
        EvidenceScope::positive(&[empty_law.proposition()])
            .check(&kernel, no_members)
            .unwrap();
        let pair_fact = kernel
            .identity(super::positive(pair_law.proposition()))
            .unwrap();
        let contains_second = sequences
            .prove_member_at(&mut kernel, &pair_law, pair_fact, 1)
            .unwrap();
        EvidenceScope::positive(&[pair_law.proposition()])
            .check(&kernel, contains_second)
            .unwrap();

        let laws = algebra
            .constructor_laws(&mut kernel, &[unary, binary])
            .unwrap();
        assert_eq!(laws.constructors(), &[unary, binary]);
        assert_eq!(laws.propositions().len(), 3);
        assert!(
            laws.propositions()
                .iter()
                .all(|&law| kernel.classifier(law).unwrap() == bool_ty)
        );

        let applied = apply(&mut kernel, unary.operation(), &[element]).unwrap();
        assert_eq!(kernel.classifier(applied).unwrap(), value_ty);
        let before = kernel.arena().clone();
        assert!(
            algebra
                .constructor(&mut kernel, unary.operation(), 2)
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
        assert!(
            sequences
                .prove_member_at(&mut kernel, &pair_law, pair_fact, 2)
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
        assert!(
            sequences
                .prove_empty_has_no_members(&mut kernel, &singleton_law, empty_fact)
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
        assert!(sequences.membership_law(&mut kernel, unary, &[]).is_err());
        assert_eq!(kernel.arena(), &before);
        assert!(
            algebra
                .constructor_laws(&mut kernel, &[unary, unary])
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
    }

    #[test]
    fn structural_field_patterns_are_generic_and_transactional() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let value_ty = kernel.ty_fv(1, star).unwrap();
        let unary_ty = kernel.ty_arr(value_ty, value_ty).unwrap();
        let binary_tail = kernel.ty_arr(value_ty, value_ty).unwrap();
        let binary_ty = kernel.ty_arr(value_ty, binary_tail).unwrap();
        let graph_tail = kernel.ty_arr(value_ty, bool_ty).unwrap();
        let graph_ty = kernel.ty_arr(value_ty, graph_tail).unwrap();
        let unary = kernel.tm_fv(10, unary_ty).unwrap();
        let binary = kernel.tm_fv(11, binary_ty).unwrap();
        let algebra = StructuralValueAlgebra { value_ty, bool_ty };
        let unary = algebra.constructor(&mut kernel, unary, 1).unwrap();
        let binary = algebra.constructor(&mut kernel, binary, 2).unwrap();

        let pattern = algebra
            .field_pattern(&mut kernel, binary, 1, unary)
            .unwrap();
        assert_eq!(pattern.algebra(), algebra);
        assert_eq!(pattern.record_constructor(), binary);
        assert_eq!(pattern.selected(), 1);
        assert_eq!(pattern.pattern_constructor(), unary);
        assert_eq!(pattern.field_binders().len(), 2);
        let graph = pattern.predicate();
        let actual = kernel.classifier(graph).unwrap();
        covalence_logic_hol_derived::join_same_syntax(&mut kernel, actual, graph_ty).unwrap();
        let output = kernel.tm_fv(12, value_ty).unwrap();
        let other = kernel.tm_fv(13, value_ty).unwrap();
        let patterned = apply(&mut kernel, unary.operation(), &[output]).unwrap();
        let proved = algebra
            .prove_field_pattern(&mut kernel, binary, &[other, patterned], 1, unary, output)
            .unwrap();
        assert_eq!(proved.pattern().selected(), 1);
        EvidenceScope::positive(&[])
            .check(&kernel, proved.evidence())
            .unwrap();

        let before = kernel.arena().clone();
        assert!(
            algebra
                .field_pattern_graph(&mut kernel, binary, 2, unary)
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
        assert!(
            algebra
                .prove_field_pattern(&mut kernel, binary, &[other, other], 1, unary, output)
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
        assert!(
            algebra
                .field_pattern_graph(&mut kernel, binary, 1, binary)
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
    }
}
