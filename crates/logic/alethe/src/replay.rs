//! Proof-producing QF_UF replay through checked HOL operations.

use std::collections::{BTreeSet, HashMap};

use covalence_data_sexpr::{Atom, Expr, ExprKind, Repr, SpannedRepr};
use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{
    Kernel, KernelError, Lit, Ref, SynRel, Tag, ThmId, TmTag,
    builtin::{Op1, Op2},
    init,
};
use covalence_logic_hol_derived::{
    EqualityError, SyntaxError, equality_symmetry, equality_transitivity, join_same_syntax,
};

use crate::{AletheCommand, AletheProof, SmtCommand, SmtProblem};

/// A checked refutation bound to one exact normalized SMT assertion set.
#[derive(Debug)]
pub struct Refutation {
    kernel: Kernel,
    theorem: ThmId,
    assertions: Vec<Lit>,
}

impl Refutation {
    /// Returns the checked kernel containing the refutation theorem.
    #[must_use]
    pub const fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// Returns the theorem whose premises are exactly the normalized problem
    /// assertions and whose conclusion is empty.
    #[must_use]
    pub const fn theorem(&self) -> ThmId {
        self.theorem
    }

    /// Returns the translated assertions in source order.
    #[must_use]
    pub fn assertions(&self) -> &[Lit] {
        &self.assertions
    }

    /// Consumes the result and returns its checked kernel.
    #[must_use]
    pub fn into_kernel(self) -> Kernel {
        self.kernel
    }
}

/// Why a QF_UF problem or Alethe derivation was rejected.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum Error {
    /// The embedded checked Boolean init manifest was invalid JSON.
    #[snafu(display("could not decode the checked Boolean init manifest: {source}"))]
    InitJson {
        source: covalence_lib_json::serde_json::Error,
    },
    /// The embedded checked Boolean init manifest was rejected.
    #[snafu(display("could not compile the checked Boolean init manifest: {source}"))]
    Init { source: init::CompileError },
    /// A checked HOL operation rejected the derivation.
    #[snafu(transparent)]
    Kernel { source: KernelError },
    /// A userspace-derived equality rule was rejected.
    #[snafu(transparent)]
    Equality { source: EqualityError },
    /// A structural syntax certificate was rejected.
    #[snafu(transparent)]
    Syntax { source: SyntaxError },
    /// Input uses a command, rule, sort, or term outside QF_UF.
    #[snafu(display("unsupported QF_UF input: {message}"))]
    Unsupported { message: String },
    /// Input is structurally inconsistent or names absent data.
    #[snafu(display("malformed QF_UF input: {message}"))]
    Malformed { message: String },
    /// A proof assumption is not one of the requested problem assertions.
    #[snafu(display("Alethe assumption is not asserted by the requested problem"))]
    UnassertedAssumption,
    /// A checked rule derived a clause other than the one stated by Alethe.
    #[snafu(display("Alethe step {step:?} derived clause {actual:?}, expected {expected:?}"))]
    ClauseMismatch {
        step: String,
        actual: Vec<Lit>,
        expected: Vec<Lit>,
    },
    /// The proof ended without an empty clause.
    #[snafu(display("Alethe proof does not derive the empty clause"))]
    NoRefutation,
}

#[derive(Clone, Copy, Debug)]
struct Term {
    reference: Ref,
    literal: Lit,
}

impl Term {
    fn positive(reference: Ref) -> Self {
        Self {
            reference,
            literal: Lit::positive(reference.get()),
        }
    }

    fn literal(self) -> Lit {
        self.literal
    }
}

struct Replayer {
    kernel: Kernel,
    init: init::Compiled,
    star: Ref,
    bool_ty: Ref,
    next_name: u64,
    sorts: HashMap<String, Ref>,
    functions: HashMap<String, Term>,
    named: HashMap<String, Term>,
    assertions: Vec<Lit>,
    assertion_terms: Vec<Term>,
    assertion_transports: Vec<(Ref, Ref)>,
    steps: HashMap<String, ThmId>,
}

impl Replayer {
    fn new() -> Result<Self, Error> {
        const MANIFEST: &str = include_str!("../../../../theories/init-boolean.checked.json");
        let manifest = covalence_lib_json::serde_json::from_str(MANIFEST)
            .map_err(|source| Error::InitJson { source })?;
        let init = init::compile(&manifest).map_err(|source| Error::Init { source })?;
        let kernel = Kernel::with_init(&init);
        let star = init.get("star").ok_or_else(|| Error::Malformed {
            message: "Boolean init has no star definition".to_owned(),
        })?;
        let bool_ty = init.get("bool").ok_or_else(|| Error::Malformed {
            message: "Boolean init has no bool definition".to_owned(),
        })?;
        Ok(Self {
            kernel,
            init,
            star,
            bool_ty,
            next_name: 0,
            sorts: HashMap::new(),
            functions: HashMap::new(),
            named: HashMap::new(),
            assertions: Vec::new(),
            assertion_terms: Vec::new(),
            assertion_transports: Vec::new(),
            steps: HashMap::new(),
        })
    }

    fn name(&mut self) -> Result<u64, Error> {
        let name = self.next_name;
        self.next_name = self
            .next_name
            .checked_add(1)
            .ok_or_else(|| Error::Malformed {
                message: "symbol name space is exhausted".to_owned(),
            })?;
        Ok(name)
    }

    fn ingest_problem(&mut self, problem: &SmtProblem) -> Result<(), Error> {
        let mut logic = None;
        for command in problem.commands() {
            match command {
                SmtCommand::SetLogic(value) => {
                    if logic.replace(value.as_str()).is_some() || value != "QF_UF" {
                        return Err(Error::Unsupported {
                            message: format!("logic {value:?}"),
                        });
                    }
                }
                SmtCommand::DeclareSort { name, arity: 0 } => {
                    if self.sorts.contains_key(name) {
                        return Err(Error::Malformed {
                            message: format!("duplicate sort {name:?}"),
                        });
                    }
                    let symbol = self.name()?;
                    let ty = self.kernel.ty_fv(symbol, self.star)?;
                    self.sorts.insert(name.clone(), ty);
                }
                SmtCommand::DeclareSort { name, arity } => {
                    return Err(Error::Unsupported {
                        message: format!("parametric sort {name:?}/{arity}"),
                    });
                }
                SmtCommand::DeclareFun {
                    name,
                    parameters,
                    result,
                } => self.declare_function(name, parameters, result)?,
                SmtCommand::Assert(expression) => {
                    let term = self.term(expression)?;
                    self.assertions.push(Lit::positive(term.reference.get()));
                    self.assertion_terms.push(term);
                }
            }
        }
        if logic != Some("QF_UF") {
            return Err(Error::Unsupported {
                message: "problem must declare QF_UF".to_owned(),
            });
        }
        Ok(())
    }

    fn declare_function(
        &mut self,
        name: &str,
        parameters: &[Expr],
        result: &Expr,
    ) -> Result<(), Error> {
        if self.functions.contains_key(name) {
            return Err(Error::Malformed {
                message: format!("duplicate function {name:?}"),
            });
        }
        let mut ty = self.sort(result)?;
        for parameter in parameters.iter().rev() {
            let domain = self.sort(parameter)?;
            ty = self.kernel.ty_arr(domain, ty)?;
        }
        let symbol = self.name()?;
        let term = self.kernel.tm_fv(symbol, ty)?;
        self.functions.insert(name.to_owned(), Term::positive(term));
        Ok(())
    }

    fn sort(&self, expression: &Expr) -> Result<Ref, Error> {
        let name = symbol(expression)?;
        if name == "Bool" {
            return Ok(self.bool_ty);
        }
        self.sorts
            .get(name)
            .copied()
            .ok_or_else(|| Error::Unsupported {
                message: format!("sort {name:?}"),
            })
    }

    fn term(&mut self, expression: &Expr) -> Result<Term, Error> {
        match expression.node() {
            ExprKind::Atom(node) => match SpannedRepr::atom(node) {
                Atom::Symbol(value) if value == "true" => {
                    Ok(Term::positive(self.kernel.bool(self.bool_ty, true)?))
                }
                Atom::Symbol(value) if value == "false" => {
                    Ok(Term::positive(self.kernel.bool(self.bool_ty, false)?))
                }
                Atom::Symbol(value) if value.starts_with('@') => self
                    .named
                    .get(value.as_str())
                    .copied()
                    .map(|term| Term::positive(term.reference))
                    .ok_or_else(|| Error::Malformed {
                        message: format!("unknown named term {value:?}"),
                    }),
                Atom::Symbol(value) => {
                    self.functions
                        .get(value.as_str())
                        .copied()
                        .ok_or_else(|| Error::Malformed {
                            message: format!("unknown function {value:?}"),
                        })
                }
                other => Err(Error::Unsupported {
                    message: format!("term atom {other:?}"),
                }),
            },
            ExprKind::List(node) => {
                let items = SpannedRepr::list_items(node);
                let head = items.first().ok_or_else(|| Error::Malformed {
                    message: "empty term".to_owned(),
                })?;
                match symbol(head)? {
                    "!" => self.annotation(items),
                    "not" if items.len() == 2 => {
                        let inner = self.term(&items[1])?;
                        let reference = self.kernel.op1(Op1::Not, inner.reference)?;
                        Ok(Term {
                            reference,
                            literal: inner.literal.negated(),
                        })
                    }
                    "=" if items.len() == 3 => {
                        let left = self.term(&items[1])?.reference;
                        let right = self.term(&items[2])?.reference;
                        Ok(Term::positive(self.kernel.eq(self.bool_ty, left, right)?))
                    }
                    "and" | "or" | "=>" => self.fold_boolean(symbol(head)?, &items[1..]),
                    _ => {
                        let mut function = self.term(head)?.reference;
                        for argument in &items[1..] {
                            let argument = self.term(argument)?.reference;
                            function = self.kernel.app(function, argument)?;
                        }
                        Ok(Term::positive(function))
                    }
                }
            }
        }
    }

    fn annotation(&mut self, items: &[Expr]) -> Result<Term, Error> {
        if items.len() < 4 || !items.len().is_multiple_of(2) {
            return Err(Error::Malformed {
                message: "annotation requires attribute-value pairs".to_owned(),
            });
        }
        let value = self.term(&items[1])?;
        for pair in items[2..].chunks_exact(2) {
            if keyword(&pair[0])? != "named" {
                return Err(Error::Unsupported {
                    message: format!("term attribute :{}", keyword(&pair[0])?),
                });
            }
            let name = symbol(&pair[1])?;
            if !name.starts_with('@') || self.named.insert(name.to_owned(), value).is_some() {
                return Err(Error::Malformed {
                    message: format!("invalid or duplicate named term {name:?}"),
                });
            }
        }
        Ok(value)
    }

    fn fold_boolean(&mut self, operator: &str, arguments: &[Expr]) -> Result<Term, Error> {
        let (first, rest) = arguments.split_first().ok_or_else(|| Error::Malformed {
            message: format!("nullary {operator}"),
        })?;
        let mut result = self.term(first)?.reference;
        for argument in rest {
            let right = self.term(argument)?.reference;
            result = match operator {
                "and" => self.kernel.op2(Op2::And, result, right)?,
                "or" => self.kernel.op2(Op2::Or, result, right)?,
                "=>" => self.kernel.op2(Op2::Imp, result, right)?,
                _ => unreachable!("caller limits Boolean operators"),
            };
        }
        Ok(Term::positive(result))
    }

    fn ingest_proof(mut self, proof: &AletheProof) -> Result<Refutation, Error> {
        let mut refutation = None;
        for command in proof.commands() {
            match command {
                AletheCommand::Assume { id, term } => {
                    let term = self.term(term)?;
                    let formula = Lit::positive(term.reference.get());
                    self.match_assertion(formula)?;
                    let theorem = self.kernel.identity(formula)?;
                    self.insert_step(id, theorem)?;
                }
                AletheCommand::Step {
                    id,
                    clause,
                    rule,
                    premises,
                    args,
                    discharge,
                } => {
                    if !discharge.is_empty()
                        || (!args.is_empty() && !matches!(rule.as_str(), "rare_rewrite" | "and"))
                    {
                        return Err(Error::Unsupported {
                            message: format!("{rule} attributes"),
                        });
                    }
                    let clause = clause
                        .iter()
                        .map(|term| self.term(term).map(Term::literal))
                        .collect::<Result<Vec<_>, _>>()?;
                    let premises = premises
                        .iter()
                        .map(|name| {
                            self.steps
                                .get(name)
                                .copied()
                                .ok_or_else(|| Error::Malformed {
                                    message: format!("unknown premise {name:?}"),
                                })
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let theorem = self.apply_rule(rule, &clause, &premises, args)?;
                    let theorem = self.check_clause(id, theorem, &clause)?;
                    self.insert_step(id, theorem)?;
                    if clause.is_empty() {
                        refutation = Some(theorem);
                    }
                }
                AletheCommand::Anchor { .. } => {
                    return Err(Error::Unsupported {
                        message: "anchor".to_owned(),
                    });
                }
                AletheCommand::DefineFun { .. } => {
                    return Err(Error::Unsupported {
                        message: "define-fun".to_owned(),
                    });
                }
            }
        }
        let theorem = refutation.ok_or(Error::NoRefutation)?;
        for &(source, target) in &self.assertion_transports {
            self.kernel.convert_theorem(theorem, source, target)?;
        }
        self.kernel.weaken(theorem, &self.assertions, &[])?;
        self.kernel.contract_theorem(theorem)?;
        self.check_exact_goal(theorem)?;
        Ok(Refutation {
            kernel: self.kernel,
            theorem,
            assertions: self.assertions,
        })
    }

    fn insert_step(&mut self, id: &str, theorem: ThmId) -> Result<(), Error> {
        if self.steps.insert(id.to_owned(), theorem).is_some() {
            return Err(Error::Malformed {
                message: format!("duplicate step {id:?}"),
            });
        }
        Ok(())
    }

    fn match_assertion(&mut self, literal: Lit) -> Result<(), Error> {
        let candidate = reference(literal.magnitude())?;
        let assertions = self.assertion_terms.clone();
        for assertion in assertions {
            let target = assertion.reference;
            if join_same_syntax(&mut self.kernel, candidate, target).is_ok() {
                self.assertion_transports.push((candidate, target));
                return Ok(());
            }
        }
        Err(Error::UnassertedAssumption)
    }

    fn apply_rule(
        &mut self,
        rule: &str,
        clause: &[Lit],
        premises: &[ThmId],
        args: &[Expr],
    ) -> Result<ThmId, Error> {
        match rule {
            "resolution" | "th_resolution" => self.resolution(premises),
            "refl" => self.reflexivity(clause),
            "symm" => self.symmetry(clause, premises),
            "trans" => self.transitivity(clause, premises),
            "cong" => self.congruence(clause, premises),
            "equiv_pos2" => self.equiv_pos2(clause),
            "implies" => self.flatten_single_premise("implies", premises),
            "or_pos" => self.or_pos(clause),
            "and" => self.and_elimination(clause, premises, args),
            "rare_rewrite" => self.rare_rewrite(clause, args),
            "evaluate" => self.evaluate(clause),
            "false" => self.false_rule(clause),
            other => Err(Error::Unsupported {
                message: format!("rule {other:?}"),
            }),
        }
    }

    fn or_pos(&mut self, clause: &[Lit]) -> Result<ThmId, Error> {
        let Some(negated_disjunction) = clause.first().copied() else {
            return Err(Error::Malformed {
                message: "or_pos requires a clause".to_owned(),
            });
        };
        if negated_disjunction.is_positive() {
            return Err(Error::Malformed {
                message: "or_pos requires a negative disjunction".to_owned(),
            });
        }
        let disjunction = reference(negated_disjunction.magnitude())?;
        let theorem = self.kernel.identity(Lit::positive(disjunction.get()))?;
        let theorem =
            self.kernel
                .expand_conclusion(theorem, Lit::positive(disjunction.get()), None)?;
        self.kernel
            .not_right(theorem, Lit::positive(disjunction.get()))?;
        self.kernel.contract_theorem(theorem)?;
        Ok(theorem)
    }

    fn and_elimination(
        &mut self,
        clause: &[Lit],
        premises: &[ThmId],
        args: &[Expr],
    ) -> Result<ThmId, Error> {
        let [premise] = premises else {
            return Err(Error::Malformed {
                message: "and requires one premise".to_owned(),
            });
        };
        let [argument] = args else {
            return Err(Error::Malformed {
                message: "and requires one index".to_owned(),
            });
        };
        let index = number_value(argument)?
            .parse::<usize>()
            .map_err(|_| Error::Malformed {
                message: "and index is not a natural number".to_owned(),
            })?;
        let conclusions = conclusion_literals(&self.kernel, *premise)?;
        let [source] = conclusions.as_slice() else {
            return Err(Error::Malformed {
                message: "and premise must have one conclusion".to_owned(),
            });
        };
        if !source.is_positive() {
            return Err(Error::Malformed {
                message: "and premise must conclude a conjunction".to_owned(),
            });
        }
        let conjunction = reference(source.magnitude())?;
        let children = self
            .kernel
            .arena()
            .children(conjunction)
            .ok_or_else(|| Error::Malformed {
                message: "and premise has no children".to_owned(),
            })?
            .collect::<Vec<_>>();
        let [left, right] = children.as_slice() else {
            return Err(Error::Malformed {
                message: "and premise is not binary".to_owned(),
            });
        };
        let selected = match index {
            0 => *left,
            1 => *right,
            _ => {
                return Err(Error::Malformed {
                    message: "and index is outside the binary conjunction".to_owned(),
                });
            }
        };
        let other = if index == 0 { *right } else { *left };
        let theorem = self.kernel.identity(Lit::positive(selected.get()))?;
        self.kernel
            .weaken(theorem, &[Lit::positive(other.get())], &[])?;
        let theorem = self
            .kernel
            .fold_premise(theorem, Lit::positive(conjunction.get()))?;
        self.convert_equality(theorem, selected, positive_unit(clause, "and")?)
    }

    fn flatten_single_premise(&mut self, rule: &str, premises: &[ThmId]) -> Result<ThmId, Error> {
        let [premise] = premises else {
            return Err(Error::Malformed {
                message: format!("{rule} requires one premise"),
            });
        };
        self.flatten_clause(*premise)
    }

    fn rare_rewrite(&mut self, clause: &[Lit], args: &[Expr]) -> Result<ThmId, Error> {
        let Some(name) = args.first().and_then(string_value) else {
            return Err(Error::Malformed {
                message: "rare_rewrite requires a string rule name".to_owned(),
            });
        };
        match name {
            "eq-refl" => {
                let target = positive_unit(clause, "rare_rewrite eq-refl")?;
                let [_bool_ty, proposition, truth] = equality_children(&self.kernel, target)?;
                if self.kernel.arena().bool_value(truth) != Some(true) {
                    return Err(Error::Malformed {
                        message: "eq-refl must rewrite to true".to_owned(),
                    });
                }
                let [_domain, left, right] = equality_children(&self.kernel, proposition)?;
                join_same_syntax(&mut self.kernel, left, right)?;
                let proved = self.kernel.refl(self.bool_ty, left)?;
                let theorem =
                    self.convert_equality(proved.theorem, proved.equality, proposition)?;
                self.equality_to_true(proposition, truth, theorem, target)
            }
            other => Err(Error::Unsupported {
                message: format!("rare_rewrite {other:?}"),
            }),
        }
    }

    fn evaluate(&mut self, clause: &[Lit]) -> Result<ThmId, Error> {
        let target = positive_unit(clause, "evaluate")?;
        let [_bool_ty, proposition, constant] = equality_children(&self.kernel, target)?;
        if self.kernel.arena().bool_value(constant) != Some(false) {
            return Err(Error::Unsupported {
                message: "evaluate result other than false".to_owned(),
            });
        }
        let left = self.kernel.identity(Lit::positive(proposition.get()))?;
        let left = self
            .kernel
            .flatten_conclusion(left, Lit::positive(proposition.get()))?;
        if conclusion_literals(&self.kernel, left)?.is_empty() {
            self.kernel
                .weaken(left, &[], &[Lit::positive(constant.get())])?;
        } else {
            return Err(Error::Unsupported {
                message: "evaluate expression does not reduce to false".to_owned(),
            });
        }
        let right = self.kernel.false_left(Lit::positive(constant.get()))?;
        self.kernel
            .weaken(right, &[], &[Lit::positive(proposition.get())])?;
        let result =
            self.kernel
                .deduct_antisym(self.bool_ty, proposition, constant, left, right)?;
        self.convert_equality(result.theorem, result.equality, target)
    }

    fn equality_to_true(
        &mut self,
        proposition: Ref,
        truth: Ref,
        proposition_theorem: ThmId,
        target: Ref,
    ) -> Result<ThmId, Error> {
        let truth_theorem = self.kernel.true_right(Lit::positive(truth.get()))?;
        let result = self.kernel.deduct_antisym(
            self.bool_ty,
            proposition,
            truth,
            truth_theorem,
            proposition_theorem,
        )?;
        self.convert_equality(result.theorem, result.equality, target)
    }

    fn false_rule(&mut self, clause: &[Lit]) -> Result<ThmId, Error> {
        let [literal] = clause else {
            return Err(Error::Malformed {
                message: "false requires one literal".to_owned(),
            });
        };
        if literal.is_positive() {
            return Err(Error::Malformed {
                message: "false requires a negative literal".to_owned(),
            });
        }
        let falsehood =
            Lit::positive(
                i32::try_from(literal.magnitude()).map_err(|_| Error::Malformed {
                    message: "false literal exceeds the checked arena".to_owned(),
                })?,
            );
        let theorem = self.kernel.false_left(falsehood)?;
        self.kernel.not_right(theorem, falsehood)?;
        Ok(theorem)
    }

    fn resolution(&mut self, premises: &[ThmId]) -> Result<ThmId, Error> {
        let (first, rest) = premises.split_first().ok_or_else(|| Error::Malformed {
            message: "resolution has no premises".to_owned(),
        })?;
        let mut result = *first;
        for &next in rest {
            let mut next = next;
            let left = conclusion_literals(&self.kernel, result)?;
            let right = conclusion_literals(&self.kernel, next)?;
            let mut pivot = left
                .iter()
                .find(|literal| right.contains(&literal.negated()))
                .copied();
            if pivot.is_none() {
                'candidate: for &left_literal in &left {
                    for &right_literal in &right {
                        if left_literal.is_positive() == right_literal.is_positive() {
                            continue;
                        }
                        let left_reference = reference(left_literal.magnitude())?;
                        let right_reference = reference(right_literal.magnitude())?;
                        if join_same_syntax(&mut self.kernel, left_reference, right_reference)
                            .is_ok()
                        {
                            self.kernel.convert_conclusions(
                                next,
                                right_reference,
                                left_reference,
                            )?;
                            pivot = Some(left_literal);
                            break 'candidate;
                        }
                    }
                }
            }
            // CVC5 sometimes resolves a singleton `(not p)` assumption as
            // the negative literal `p`, but in other proofs resolves the
            // exact named negation as an atom. Prefer exact atoms above and
            // only expose the logical clause view when that cannot resolve.
            if pivot.is_none()
                && right.len() == 1
                && right[0].is_positive()
                && self.kernel.arena().op1(reference(right[0].magnitude())?) == Some(Op1::Not)
            {
                next = self.kernel.expand_conclusion(next, right[0], None)?;
                let flattened = conclusion_literals(&self.kernel, next)?;
                pivot = left
                    .iter()
                    .find(|literal| flattened.contains(&literal.negated()))
                    .copied();
            }
            if pivot.is_none() {
                for &literal in &left {
                    if !literal.is_positive() {
                        continue;
                    }
                    let formula = reference(literal.magnitude())?;
                    if self.kernel.arena().op1(formula) != Some(Op1::Not) {
                        continue;
                    }
                    let Some(child) = self
                        .kernel
                        .arena()
                        .children(formula)
                        .and_then(|mut children| children.next())
                    else {
                        continue;
                    };
                    if right.contains(&Lit::positive(child.get())) {
                        result = self.kernel.flatten_conclusion(result, literal)?;
                        pivot = Some(Lit::positive(child.get()).negated());
                        break;
                    }
                }
            }
            let pivot = pivot.ok_or_else(|| Error::Malformed {
                message: "resolution premises have no complementary pivot".to_owned(),
            })?;
            result = self.kernel.resolve(result, next, pivot)?;
        }
        self.kernel.contract_theorem(result)?;
        Ok(result)
    }

    fn reflexivity(&mut self, clause: &[Lit]) -> Result<ThmId, Error> {
        let target = positive_unit(clause, "refl")?;
        let [_domain, left, right] = equality_children(&self.kernel, target)?;
        join_same_syntax(&mut self.kernel, left, right)?;
        let result = self.kernel.refl(self.bool_ty, left)?;
        self.convert_equality(result.theorem, result.equality, target)
    }

    fn symmetry(&mut self, clause: &[Lit], premises: &[ThmId]) -> Result<ThmId, Error> {
        let [premise] = premises else {
            return Err(Error::Malformed {
                message: "symm requires one premise".to_owned(),
            });
        };
        let target = positive_unit(clause, "symm")?;
        let result = equality_symmetry(&mut self.kernel, self.bool_ty, *premise)?;
        self.convert_equality(result.theorem, result.equality, target)
    }

    fn transitivity(&mut self, clause: &[Lit], premises: &[ThmId]) -> Result<ThmId, Error> {
        let (first, rest) = premises.split_first().ok_or_else(|| Error::Malformed {
            message: "trans requires premises".to_owned(),
        })?;
        let mut theorem = *first;
        let mut equality = positive_theorem_equality(&self.kernel, theorem)?;
        for &next in rest {
            let result = equality_transitivity(&mut self.kernel, self.bool_ty, theorem, next)?;
            theorem = result.theorem;
            equality = result.equality;
        }
        self.convert_equality(theorem, equality, positive_unit(clause, "trans")?)
    }

    fn congruence(&mut self, clause: &[Lit], premises: &[ThmId]) -> Result<ThmId, Error> {
        let target = positive_unit(clause, "cong")?;
        let [_domain, compact_left, compact_right] = equality_children(&self.kernel, target)?;
        let left_expansion = self.kernel.lower_logical_tree(&self.init, compact_left)?;
        let right_expansion = self.kernel.lower_logical_tree(&self.init, compact_right)?;
        let left = left_expansion.raw;
        let right = right_expansion.raw;
        let (left_head, left_args) = application_spine(&self.kernel, left)?;
        let (right_head, right_args) = application_spine(&self.kernel, right)?;
        if left_args.is_empty() && right_args.is_empty() && premises.len() == 2 {
            let left_proved = positive_theorem_equality(&self.kernel, premises[0])?;
            let right_proved = positive_theorem_equality(&self.kernel, premises[1])?;
            if join_same_syntax(&mut self.kernel, left_proved, compact_left).is_ok()
                && join_same_syntax(&mut self.kernel, right_proved, compact_right).is_ok()
            {
                self.kernel
                    .convert_conclusions(premises[0], left_proved, compact_left)?;
                self.kernel
                    .convert_conclusions(premises[1], right_proved, compact_right)?;
                let truth = self.kernel.bool(self.bool_ty, true)?;
                let left_target = self.kernel.eq(self.bool_ty, compact_left, truth)?;
                let left_true =
                    self.equality_to_true(compact_left, truth, premises[0], left_target)?;
                let right_target = self.kernel.eq(self.bool_ty, compact_right, truth)?;
                let right_true =
                    self.equality_to_true(compact_right, truth, premises[1], right_target)?;
                let right_true = equality_symmetry(&mut self.kernel, self.bool_ty, right_true)?;
                let combined = equality_transitivity(
                    &mut self.kernel,
                    self.bool_ty,
                    left_true,
                    right_true.theorem,
                )?;
                return self.convert_equality(combined.theorem, combined.equality, target);
            }
        }
        if left_args.len() != premises.len() || right_args.len() != premises.len() {
            return Err(Error::Malformed {
                message: "cong premise count does not match application arity".to_owned(),
            });
        }
        join_same_syntax(&mut self.kernel, left_head, right_head)?;
        let proved = self.kernel.refl(self.bool_ty, left_head)?;
        let mut theorem = proved.theorem;
        let mut equality = proved.equality;
        let mut right_function = right_head;
        for ((&left_arg, &right_arg), &premise) in left_args.iter().zip(&right_args).zip(premises) {
            let [_argument_ty, premise_left, premise_right] = equality_children(
                &self.kernel,
                positive_theorem_equality(&self.kernel, premise)?,
            )?;
            join_same_syntax(&mut self.kernel, premise_left, left_arg)?;
            join_same_syntax(&mut self.kernel, premise_right, right_arg)?;
            let applied_function = self.kernel.ap_thm(theorem, left_arg)?;
            let applied_argument = self.kernel.ap_term(premise, right_function)?;
            let combined = equality_transitivity(
                &mut self.kernel,
                self.bool_ty,
                applied_function.theorem,
                applied_argument.theorem,
            )?;
            theorem = combined.theorem;
            equality = combined.equality;
            right_function = applied_argument.right;
        }
        let raw_target = self.kernel.eq(self.bool_ty, left, right)?;
        join_same_syntax(&mut self.kernel, equality, raw_target)?;
        self.kernel
            .convert_conclusions(theorem, equality, raw_target)?;
        let classifier = self.kernel.syn_refl(None, SynRel::Conv, self.bool_ty)?;
        let left = self.kernel.syn_symm(None, left_expansion.fact)?;
        let right = self.kernel.syn_symm(None, right_expansion.fact)?;
        let conversion = self.kernel.syn_congr(
            None,
            SynRel::Conv,
            None,
            None,
            raw_target,
            target,
            &[classifier, left, right],
        )?;
        self.kernel.union_syn_fact(conversion)?;
        self.kernel
            .convert_conclusions(theorem, raw_target, target)?;
        Ok(theorem)
    }

    fn equiv_pos2(&mut self, clause: &[Lit]) -> Result<ThmId, Error> {
        let [not_equality, _, _] = clause else {
            return Err(Error::Malformed {
                message: "equiv_pos2 requires three literals".to_owned(),
            });
        };
        if not_equality.is_positive() {
            return Err(Error::Malformed {
                message: "equiv_pos2 has invalid polarities".to_owned(),
            });
        }
        let equality = reference(not_equality.magnitude())?;
        let [_domain, left, _right] = equality_children(&self.kernel, equality)?;
        let equality_identity = self.kernel.identity(not_equality.negated())?;
        let left_identity = self.kernel.identity(Lit::positive(left.get()))?;
        let result = self.kernel.eq_mp(equality_identity, left_identity)?;
        self.kernel.not_right(result, not_equality.negated())?;
        self.kernel.not_right(result, Lit::positive(left.get()))?;
        self.kernel.contract_theorem(result)?;
        Ok(result)
    }

    fn flatten_clause(&mut self, theorem: ThmId) -> Result<ThmId, Error> {
        let formulas = conclusion_literals(&self.kernel, theorem)?;
        let mut result = theorem;
        for formula in formulas {
            result = self.kernel.flatten_conclusion(result, formula)?;
        }
        self.kernel.contract_theorem(result)?;
        Ok(result)
    }

    fn convert_equality(
        &mut self,
        theorem: ThmId,
        source: Ref,
        target: Ref,
    ) -> Result<ThmId, Error> {
        if !self.kernel.equivalent(source, target)? {
            join_same_syntax(&mut self.kernel, source, target)?;
        }
        self.kernel.convert_conclusions(theorem, source, target)?;
        Ok(theorem)
    }

    fn check_clause(
        &mut self,
        step: &str,
        theorem: ThmId,
        expected: &[Lit],
    ) -> Result<ThmId, Error> {
        let mut actual = conclusion_literals(&self.kernel, theorem)?;
        for &literal in expected {
            let reference = reference(literal.magnitude())?;
            let is_false = matches!(
                (
                    literal.is_positive(),
                    self.kernel.arena().bool_value(reference)
                ),
                (true, Some(false)) | (false, Some(true))
            );
            if is_false && !actual.contains(&literal) {
                self.kernel.weaken(theorem, &[], &[literal])?;
            }
        }
        actual = conclusion_literals(&self.kernel, theorem)?;
        let mut expected = expected.to_vec();
        actual.sort_unstable();
        expected.sort_unstable();
        if actual != expected {
            for wanted in &expected {
                let wanted_reference = reference(wanted.magnitude())?;
                for candidate in &actual {
                    if candidate.is_positive() != wanted.is_positive() {
                        continue;
                    }
                    let candidate_reference = reference(candidate.magnitude())?;
                    if join_same_syntax(&mut self.kernel, candidate_reference, wanted_reference)
                        .is_ok()
                    {
                        self.kernel.convert_conclusions(
                            theorem,
                            candidate_reference,
                            wanted_reference,
                        )?;
                    }
                }
            }
            self.kernel.contract_theorem(theorem)?;
            actual = conclusion_literals(&self.kernel, theorem)?;
            actual.sort_unstable();
        }
        if actual != expected {
            let canonical_actual = actual
                .iter()
                .copied()
                .map(|literal| canonical_clause_literal(&self.kernel, literal))
                .collect::<Result<Vec<_>, _>>()?;
            let canonical_expected = expected
                .iter()
                .copied()
                .map(|literal| canonical_clause_literal(&self.kernel, literal))
                .collect::<Result<Vec<_>, _>>()?;
            if canonical_actual == canonical_expected {
                return Ok(theorem);
            }
            return Err(Error::ClauseMismatch {
                step: step.to_owned(),
                actual,
                expected,
            });
        }
        Ok(theorem)
    }

    fn check_exact_goal(&self, theorem: ThmId) -> Result<(), Error> {
        let value = self
            .kernel
            .thm()
            .get(theorem)
            .ok_or_else(|| Error::Malformed {
                message: format!("missing theorem {theorem:?}"),
            })?;
        if value.rhs.rows().next().is_some() {
            return Err(Error::NoRefutation);
        }
        let actual = value
            .lhs
            .rows()
            .map(|row| match row {
                [literal] => Ok(*literal),
                _ => Err(Error::Malformed {
                    message: "refutation contains a non-unit premise".to_owned(),
                }),
            })
            .collect::<Result<BTreeSet<_>, _>>()?;
        let expected = self.assertions.iter().copied().collect::<BTreeSet<_>>();
        if actual != expected {
            return Err(Error::Malformed {
                message: "refutation is not bound to the exact assertion set".to_owned(),
            });
        }
        Ok(())
    }
}

fn canonical_clause_literal(kernel: &Kernel, literal: Lit) -> Result<Lit, Error> {
    if !literal.is_positive() {
        return Ok(literal);
    }
    let formula = reference(literal.magnitude())?;
    if kernel.arena().op1(formula) != Some(Op1::Not) {
        return Ok(literal);
    }
    let child = kernel
        .arena()
        .children(formula)
        .and_then(|mut children| children.next())
        .ok_or_else(|| Error::Malformed {
            message: "negation has no operand".to_owned(),
        })?;
    Ok(Lit::positive(child.get()).negated())
}

/// Replays a QF_UF Alethe proof and binds its empty-clause theorem to the
/// exact normalized assertion set from `problem`.
///
/// # Errors
///
/// Returns [`Error`] for unsupported syntax or rules, unasserted assumptions,
/// missing premises, mismatched clauses, or any rejected checked derivation.
pub fn replay_qf_uf(problem: &SmtProblem, proof: &AletheProof) -> Result<Refutation, Error> {
    let mut replayer = Replayer::new()?;
    replayer.ingest_problem(problem)?;
    replayer.ingest_proof(proof)
}

fn symbol(expression: &Expr) -> Result<&str, Error> {
    match expression.node() {
        ExprKind::Atom(node) => match SpannedRepr::atom(node) {
            Atom::Symbol(value) => Ok(value),
            _ => Err(Error::Malformed {
                message: "expected a symbol".to_owned(),
            }),
        },
        ExprKind::List(_) => Err(Error::Malformed {
            message: "expected a symbol".to_owned(),
        }),
    }
}

fn string_value(expression: &Expr) -> Option<&str> {
    match expression.node() {
        ExprKind::Atom(node) => match SpannedRepr::atom(node) {
            Atom::String(value) => Some(value),
            _ => None,
        },
        ExprKind::List(_) => None,
    }
}

fn number_value(expression: &Expr) -> Result<&str, Error> {
    match expression.node() {
        ExprKind::Atom(node) => match SpannedRepr::atom(node) {
            Atom::Number(value) => Ok(value),
            _ => Err(Error::Malformed {
                message: "expected a numeric argument".to_owned(),
            }),
        },
        ExprKind::List(_) => Err(Error::Malformed {
            message: "expected a numeric argument".to_owned(),
        }),
    }
}

fn keyword(expression: &Expr) -> Result<&str, Error> {
    match expression.node() {
        ExprKind::Atom(node) => match SpannedRepr::atom(node) {
            Atom::Keyword(value) => Ok(value),
            _ => Err(Error::Malformed {
                message: "expected an attribute".to_owned(),
            }),
        },
        ExprKind::List(_) => Err(Error::Malformed {
            message: "expected an attribute".to_owned(),
        }),
    }
}

fn reference(magnitude: u32) -> Result<Ref, Error> {
    let value = i32::try_from(magnitude).map_err(|_| Error::Malformed {
        message: "literal reference exceeds i32".to_owned(),
    })?;
    Ref::new(value).ok_or_else(|| Error::Malformed {
        message: "literal references are one-based".to_owned(),
    })
}

fn positive_unit(clause: &[Lit], rule: &str) -> Result<Ref, Error> {
    let [literal] = clause else {
        return Err(Error::Malformed {
            message: format!("{rule} requires a unit clause"),
        });
    };
    if !literal.is_positive() {
        return Err(Error::Malformed {
            message: format!("{rule} requires a positive equality"),
        });
    }
    reference(literal.magnitude())
}

fn equality_children(kernel: &Kernel, equality: Ref) -> Result<[Ref; 3], Error> {
    if kernel.arena().tag(equality) != Some(Tag::Tm(TmTag::Eq)) {
        return Err(Error::Malformed {
            message: "expected an equality term".to_owned(),
        });
    }
    kernel
        .arena()
        .children(equality)
        .ok_or_else(|| Error::Malformed {
            message: "equality has no children".to_owned(),
        })?
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|_| Error::Malformed {
            message: "equality has the wrong arity".to_owned(),
        })
}

fn positive_theorem_equality(kernel: &Kernel, theorem: ThmId) -> Result<Ref, Error> {
    let value = kernel.thm().get(theorem).ok_or_else(|| Error::Malformed {
        message: format!("missing theorem {theorem:?}"),
    })?;
    let rows = value.rhs.rows().collect::<Vec<_>>();
    match rows.as_slice() {
        [row] if row.len() == 1 && row[0].is_positive() => reference(row[0].magnitude()),
        _ => Err(Error::Malformed {
            message: "premise does not conclude one positive equality".to_owned(),
        }),
    }
}

fn conclusion_literals(kernel: &Kernel, theorem: ThmId) -> Result<Vec<Lit>, Error> {
    kernel
        .thm()
        .get(theorem)
        .ok_or_else(|| Error::Malformed {
            message: format!("missing theorem {theorem:?}"),
        })?
        .rhs
        .rows()
        .map(|row| match row {
            [literal] => Ok(*literal),
            _ => Err(Error::Malformed {
                message: "Alethe clause theorem contains a non-unit DNF row".to_owned(),
            }),
        })
        .collect()
}

fn application_spine(kernel: &Kernel, mut term: Ref) -> Result<(Ref, Vec<Ref>), Error> {
    let mut reversed = Vec::new();
    while kernel.arena().tag(term) == Some(Tag::Tm(TmTag::App)) {
        let children = kernel
            .arena()
            .children(term)
            .ok_or_else(|| Error::Malformed {
                message: "application has no children".to_owned(),
            })?
            .collect::<Vec<_>>();
        let [function, argument] = children.as_slice() else {
            return Err(Error::Malformed {
                message: "application has the wrong arity".to_owned(),
            });
        };
        term = *function;
        reversed.push(*argument);
    }
    reversed.reverse();
    Ok((term, reversed))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parse_alethe, parse_cvc5_output, parse_smtlib2};
    use std::io::Write as _;
    use std::process::{Command, Stdio};

    const PROBLEM: &str =
        include_str!("../../../proof/alethe/tests/fixtures/cvc5-qf-uf/problem.smt2");
    const PROOF: &str =
        include_str!("../../../proof/alethe/tests/fixtures/cvc5-qf-uf/proof.alethe");

    #[test]
    fn replays_the_selected_cvc5_qf_uf_refutation() {
        let problem = parse_smtlib2(PROBLEM).expect("problem parses");
        let proof = parse_alethe(PROOF).expect("proof parses");
        let result = replay_qf_uf(&problem, &proof).expect("proof replays");
        let theorem = result
            .kernel()
            .thm()
            .get(result.theorem())
            .expect("refutation theorem");
        assert_eq!(theorem.lhs.rows().count(), 3);
        assert!(theorem.rhs.rows().next().is_none());
    }

    #[test]
    fn generates_and_replays_a_proof_with_cvc5() {
        generate_and_replay(PROBLEM);
    }

    #[test]
    fn replays_a_live_cvc5_qf_uf_rule_corpus() {
        const CASES: &[&str] = &[
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(assert (not (= a a)))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(declare-const b U)\n(declare-const c U)\n(assert (= a b))\n(assert (= b c))\n(assert (not (= a c)))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n(assert p)\n(assert (not q))\n(assert (=> p q))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n(assert (and p q))\n(assert (or (not p) (not q)))\n(check-sat)\n",
        ];
        for problem in CASES {
            generate_and_replay(problem);
        }
    }

    fn generate_and_replay(problem_source: &str) {
        let mut child = Command::new("cvc5")
            .args([
                "--produce-proofs",
                "--proof-format-mode=alethe",
                "--proof-granularity=dsl-rewrite-strict",
                "--no-proof-allow-trust",
                "--dump-proofs",
                "--lang=smt2",
            ])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .expect("cvc5 is part of the Nix test environment");
        child
            .stdin
            .take()
            .expect("cvc5 stdin")
            .write_all(problem_source.as_bytes())
            .expect("write problem to cvc5");
        let output = child.wait_with_output().expect("wait for cvc5");
        assert!(output.status.success(), "cvc5 failed: {output:?}");
        let stdout = String::from_utf8(output.stdout).expect("cvc5 emits UTF-8");
        let problem = parse_smtlib2(problem_source).expect("problem parses");
        let proof = parse_cvc5_output(&stdout).expect("generated proof parses");
        replay_qf_uf(&problem, &proof).unwrap_or_else(|error| {
            panic!(
                "generated proof replays for:\n{problem_source}\nproof:\n{stdout}\nerror: {error}"
            )
        });
    }

    #[test]
    fn rejects_an_unasserted_assumption_and_a_forged_clause() {
        let problem = parse_smtlib2(PROBLEM).expect("problem parses");
        let unasserted = parse_alethe("(assume x true)").expect("proof parses");
        assert!(matches!(
            replay_qf_uf(&problem, &unasserted),
            Err(Error::UnassertedAssumption)
        ));

        let forged = PROOF.replace("(step t4 (cl)", "(step t4 (cl @p_4)");
        let forged = parse_alethe(&forged).expect("proof parses");
        assert!(matches!(
            replay_qf_uf(&problem, &forged),
            Err(Error::ClauseMismatch { .. }) | Err(Error::Kernel { .. })
        ));
    }
}
