//! Proof-producing `QF_UF` replay through checked HOL operations.

use std::collections::{BTreeSet, HashMap};

use covalence_data_sexpr::{Atom, Expr, ExprKind, Repr, SpannedRepr};
use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{
    Kernel, KernelError, Lit, Ref, SynRel, Tag, ThmId, TmTag,
    builtin::{Op1, Op2},
    init,
};
use covalence_logic_hol_derived::{
    Conditional, ConditionalError, EqualityError, SyntaxError, conditional, conditional_when_false,
    conditional_when_true, equality_symmetry, equality_transitivity, join_same_syntax,
};

use crate::{AletheCommand, AletheProof, SmtCommand, SmtProblem};

/// A checked refutation bound to one exact normalized SMT assertion set.
#[derive(Debug)]
pub struct Refutation {
    kernel: Kernel,
    theorem: ThmId,
    assertions: Vec<Lit>,
}

/// Checked context offered to a user-defined handler for an unknown rule.
///
/// Terms and clauses have already been lowered into `kernel`'s arena. The
/// replay engine independently checks the returned theorem against `clause`.
pub struct RuleRequest<'a> {
    /// Kernel containing all lowered terms and premise theorems.
    pub kernel: &'a mut Kernel,
    /// Kernel Boolean type.
    pub bool_ty: Ref,
    /// Alethe rule name not implemented by the default replayer.
    pub rule: &'a str,
    /// Lowered expected conclusion clause.
    pub clause: &'a [Lit],
    /// Checked premise theorem indices.
    pub premises: &'a [ThmId],
    /// Untrusted rule arguments from the parsed proof.
    pub args: &'a [Expr],
}

/// Optional userspace fallback for Alethe rules outside the default set.
pub trait RuleHandler {
    /// Attempts to derive the requested clause with ordinary checked kernel
    /// operations. Returning `None` preserves the default unsupported-rule
    /// error.
    ///
    /// # Errors
    ///
    /// Returns [`Error`] when the handler recognizes the rule but rejects its
    /// arguments or cannot construct checked evidence.
    fn apply(&mut self, request: RuleRequest<'_>) -> Result<Option<ThmId>, Error>;
}

struct RejectUnknownRules;

impl RuleHandler for RejectUnknownRules {
    fn apply(&mut self, _request: RuleRequest<'_>) -> Result<Option<ThmId>, Error> {
        Ok(None)
    }
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

/// Why a `QF_UF` problem or Alethe derivation was rejected.
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
    /// A userspace-derived polymorphic conditional was rejected.
    #[snafu(transparent)]
    Conditional { source: ConditionalError },
    /// Input uses a command, rule, sort, or term outside `QF_UF`.
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
    /// A term nests more deeply than the replayer lowers.
    #[snafu(display("term nesting exceeds the replay budget of {limit} levels"))]
    TermTooDeep {
        /// Greatest nesting depth the replayer lowers.
        limit: usize,
    },
}

/// Greatest term nesting depth `Replayer` lowers.
///
/// Lowering recurses once per nesting level over untrusted problem and proof
/// text, so the budget keeps a deeply nested term a rejected input rather than
/// an aborted process.
const MAX_TERM_DEPTH: usize = 256;

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
    locals: Vec<HashMap<String, Term>>,
    conditionals: Vec<(Ref, Ref, Ref, Conditional)>,
    named: HashMap<String, Term>,
    assertions: Vec<Lit>,
    assertion_terms: Vec<Term>,
    assertion_transports: Vec<(Ref, Ref)>,
    steps: HashMap<String, ThmId>,
}

impl Replayer {
    fn new() -> Result<Self, Error> {
        const MANIFEST: &str = include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../../theories/init-boolean.checked.json"
        ));
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
            locals: Vec::new(),
            conditionals: Vec::new(),
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
        // `@` spellings name Alethe `:named` terms, which `term_at` resolves
        // ahead of declared functions, so such a declaration is unreachable.
        if name.starts_with('@') {
            return Err(Error::Unsupported {
                message: format!("declared function {name:?} uses the reserved @ namespace"),
            });
        }
        if self.named.contains_key(name) {
            return Err(Error::Malformed {
                message: format!("function {name:?} collides with a named term"),
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
        self.term_at(expression, 0)
    }

    fn term_at(&mut self, expression: &Expr, depth: usize) -> Result<Term, Error> {
        if depth >= MAX_TERM_DEPTH {
            return Err(Error::TermTooDeep {
                limit: MAX_TERM_DEPTH,
            });
        }
        let depth = depth + 1;
        match expression.node() {
            ExprKind::Atom(node) => match SpannedRepr::atom(node) {
                Atom::Symbol(value) => {
                    // SMT-LIB 2.6 s3.6.1: a `let` binder shadows any function
                    // symbol of the same name, `true`, `false` and `:named`
                    // spellings included, so locals are scanned first.
                    if let Some(term) = self
                        .locals
                        .iter()
                        .rev()
                        .find_map(|scope| scope.get(value.as_str()))
                    {
                        return Ok(*term);
                    }
                    if value == "true" {
                        return Ok(Term::positive(self.kernel.bool(self.bool_ty, true)?));
                    }
                    if value == "false" {
                        return Ok(Term::positive(self.kernel.bool(self.bool_ty, false)?));
                    }
                    if value.starts_with('@') {
                        return self
                            .named
                            .get(value.as_str())
                            .copied()
                            .map(|term| Term::positive(term.reference))
                            .ok_or_else(|| Error::Malformed {
                                message: format!("unknown named term {value:?}"),
                            });
                    }
                    // A `:named` label and a declared function never share a
                    // spelling, so the two lookups cannot disagree.
                    if let Some(term) = self.functions.get(value.as_str()).copied() {
                        return Ok(term);
                    }
                    self.named
                        .get(value.as_str())
                        .copied()
                        .map(|term| Term::positive(term.reference))
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
                    "!" => self.annotation(items, depth),
                    "not" if items.len() == 2 => {
                        let inner = self.term_at(&items[1], depth)?;
                        let reference = self.kernel.op1(Op1::Not, inner.reference)?;
                        Ok(Term {
                            reference,
                            literal: inner.literal.negated(),
                        })
                    }
                    "=" if items.len() >= 3 => self.chain_equality(&items[1..], depth),
                    "distinct" if items.len() >= 3 => self.distinct(&items[1..], depth),
                    "xor" if items.len() >= 3 => self.fold_xor(&items[1..], depth),
                    "ite" if items.len() == 4 => self.ite(&items[1], &items[2], &items[3], depth),
                    "let" if items.len() == 3 => self.let_term(&items[1], &items[2], depth),
                    "and" | "or" => self.fold_boolean(symbol(head)?, &items[1..], depth),
                    "=>" => self.fold_implication(&items[1..], depth),
                    _ => {
                        let mut function = self.term_at(head, depth)?.reference;
                        for argument in &items[1..] {
                            let argument = self.term_at(argument, depth)?.reference;
                            function = self.kernel.app(function, argument)?;
                        }
                        Ok(Term::positive(function))
                    }
                }
            }
        }
    }

    fn fold_xor(&mut self, arguments: &[Expr], depth: usize) -> Result<Term, Error> {
        let (first, rest) = arguments.split_first().ok_or_else(|| Error::Malformed {
            message: "xor requires at least two arguments".to_owned(),
        })?;
        let mut result = self.term_at(first, depth)?.reference;
        // `xor` lowers to a chain of Boolean disequalities, and `Kernel::eq`
        // reads the operand sort off its left argument, so the Boolean sort of
        // both operands is required here rather than inferred.
        self.require_boolean(result, "xor")?;
        for argument in rest {
            let right = self.term_at(argument, depth)?.reference;
            self.require_boolean(right, "xor")?;
            let equality = self.kernel.eq(self.bool_ty, result, right)?;
            result = self.kernel.op1(Op1::Not, equality)?;
        }
        Ok(Term::positive(result))
    }

    fn require_boolean(&self, term: Ref, operator: &str) -> Result<(), Error> {
        if self
            .kernel
            .equivalent(self.kernel.classifier(term)?, self.bool_ty)?
        {
            return Ok(());
        }
        Err(Error::Malformed {
            message: format!("{operator} operands must be Boolean"),
        })
    }

    fn chain_equality(&mut self, arguments: &[Expr], depth: usize) -> Result<Term, Error> {
        let mut terms = arguments.iter();
        let mut left = self
            .term_at(
                terms.next().expect("the caller requires two arguments"),
                depth,
            )?
            .reference;
        let mut equalities = Vec::new();
        for argument in terms {
            let right = self.term_at(argument, depth)?.reference;
            equalities.push(self.kernel.eq(self.bool_ty, left, right)?);
            left = right;
        }
        let (first, rest) = equalities
            .split_first()
            .expect("two terms produce at least one equality");
        let mut result = *first;
        for &equality in rest {
            result = self.kernel.op2(Op2::And, result, equality)?;
        }
        Ok(Term::positive(result))
    }

    fn distinct(&mut self, arguments: &[Expr], depth: usize) -> Result<Term, Error> {
        let terms = arguments
            .iter()
            .map(|argument| self.term_at(argument, depth).map(|term| term.reference))
            .collect::<Result<Vec<_>, _>>()?;
        let mut inequalities = Vec::new();
        for (index, &left) in terms.iter().enumerate() {
            for &right in &terms[index + 1..] {
                let equality = self.kernel.eq(self.bool_ty, left, right)?;
                inequalities.push(self.kernel.op1(Op1::Not, equality)?);
            }
        }
        let (first, rest) = inequalities.split_first().ok_or_else(|| Error::Malformed {
            message: "distinct requires at least two arguments".to_owned(),
        })?;
        let mut result = *first;
        for &inequality in rest {
            result = self.kernel.op2(Op2::And, result, inequality)?;
        }
        Ok(Term::positive(result))
    }

    fn ite(
        &mut self,
        condition: &Expr,
        then_: &Expr,
        else_: &Expr,
        depth: usize,
    ) -> Result<Term, Error> {
        let condition = self.term_at(condition, depth)?.reference;
        let then_ = self.term_at(then_, depth)?.reference;
        let else_ = self.term_at(else_, depth)?.reference;
        let result_ty = self.kernel.classifier(then_)?;
        if !self
            .kernel
            .equivalent(result_ty, self.kernel.classifier(else_)?)?
        {
            return Err(Error::Malformed {
                message: "ite branches have different sorts".to_owned(),
            });
        }
        for &(cached_condition, cached_then, cached_else, conditional) in &self.conditionals {
            if join_same_syntax(&mut self.kernel, cached_condition, condition).is_ok()
                && join_same_syntax(&mut self.kernel, cached_then, then_).is_ok()
                && join_same_syntax(&mut self.kernel, cached_else, else_).is_ok()
            {
                return Ok(Term::positive(conditional.term));
            }
        }
        let binder_name = self.name()?;
        let binder = self.kernel.tm_fv(binder_name, result_ty)?;
        let result = conditional(
            &mut self.kernel,
            self.bool_ty,
            result_ty,
            binder,
            condition,
            then_,
            else_,
        )?;
        self.conditionals.push((condition, then_, else_, result));
        Ok(Term::positive(result.term))
    }

    fn let_term(&mut self, bindings: &Expr, body: &Expr, depth: usize) -> Result<Term, Error> {
        let ExprKind::List(node) = bindings.node() else {
            return Err(Error::Malformed {
                message: "let bindings must be a list".to_owned(),
            });
        };
        let mut scope = HashMap::new();
        for binding in SpannedRepr::list_items(node) {
            let ExprKind::List(node) = binding.node() else {
                return Err(Error::Malformed {
                    message: "let binding must be a pair".to_owned(),
                });
            };
            let pair = SpannedRepr::list_items(node);
            let [name, value] = pair else {
                return Err(Error::Malformed {
                    message: "let binding must be a pair".to_owned(),
                });
            };
            let name = symbol(name)?;
            if scope.contains_key(name) {
                return Err(Error::Malformed {
                    message: format!("duplicate let binding {name:?}"),
                });
            }
            let value = self.term_at(value, depth)?;
            scope.insert(name.to_owned(), value);
        }
        self.locals.push(scope);
        let result = self.term_at(body, depth);
        self.locals.pop();
        result
    }

    fn annotation(&mut self, items: &[Expr], depth: usize) -> Result<Term, Error> {
        if items.len() < 4 || !items.len().is_multiple_of(2) {
            return Err(Error::Malformed {
                message: "annotation requires attribute-value pairs".to_owned(),
            });
        }
        let value = self.term_at(&items[1], depth)?;
        for pair in items[2..].chunks_exact(2) {
            if keyword(&pair[0])? != "named" {
                return Err(Error::Unsupported {
                    message: format!("term attribute :{}", keyword(&pair[0])?),
                });
            }
            let name = symbol(&pair[1])?;
            // `named` is one flat map shared by the problem and the proof, so a
            // name that also denotes a declared function is rejected rather
            // than silently preferred over it.
            if self.functions.contains_key(name) {
                return Err(Error::Malformed {
                    message: format!("named term {name:?} collides with a declared function"),
                });
            }
            if self.named.insert(name.to_owned(), value).is_some() {
                return Err(Error::Malformed {
                    message: format!("duplicate named term {name:?}"),
                });
            }
        }
        Ok(value)
    }

    /// Lowers `:left-assoc` `and` and `or` by folding their arguments left.
    fn fold_boolean(
        &mut self,
        operator: &str,
        arguments: &[Expr],
        depth: usize,
    ) -> Result<Term, Error> {
        let (first, rest) = arity_at_least_two(operator, arguments)?;
        let mut result = self.term_at(first, depth)?.reference;
        for argument in rest {
            let right = self.term_at(argument, depth)?.reference;
            result = match operator {
                "and" => self.kernel.op2(Op2::And, result, right)?,
                "or" => self.kernel.op2(Op2::Or, result, right)?,
                _ => unreachable!("caller limits Boolean operators"),
            };
        }
        Ok(Term::positive(result))
    }

    /// Lowers `=>`, which SMT-LIB Core declares `:right-assoc`, so that
    /// `(=> a b c)` denotes `a -> (b -> c)` rather than `(a -> b) -> c`.
    fn fold_implication(&mut self, arguments: &[Expr], depth: usize) -> Result<Term, Error> {
        arity_at_least_two("=>", arguments)?;
        // Lower left to right, so `:named` registration and `ite` binder names
        // still follow source order, then fold the lowered rows right.
        let rows = arguments
            .iter()
            .map(|argument| self.term_at(argument, depth).map(|term| term.reference))
            .collect::<Result<Vec<_>, _>>()?;
        let (last, rest) = rows
            .split_last()
            .expect("two arguments produce two lowered rows");
        let mut result = *last;
        for &antecedent in rest.iter().rev() {
            result = self.kernel.op2(Op2::Imp, antecedent, result)?;
        }
        Ok(Term::positive(result))
    }

    fn ingest_proof(
        mut self,
        proof: &AletheProof,
        handler: &mut impl RuleHandler,
    ) -> Result<Refutation, Error> {
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
                    let built_in_rejects_args = !args.is_empty()
                        && matches!(
                            rule.as_str(),
                            "resolution"
                                | "th_resolution"
                                | "refl"
                                | "symm"
                                | "trans"
                                | "cong"
                                | "equiv_pos2"
                                | "implies"
                                | "or_pos"
                                | "xor1"
                                | "xor2"
                                | "xor_pos2"
                                | "not_symm"
                                | "distinct_elim"
                                | "evaluate"
                                | "false"
                        );
                    if !discharge.is_empty() || built_in_rejects_args {
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
                    let theorem = self.apply_rule(rule, &clause, &premises, args, handler)?;
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
        handler: &mut impl RuleHandler,
    ) -> Result<ThmId, Error> {
        match rule {
            "resolution" | "th_resolution" => self.resolution(premises),
            "refl" | "distinct_elim" => self.reflexivity(clause),
            "symm" => self.symmetry(clause, premises),
            "trans" => self.transitivity(clause, premises),
            "cong" => self.congruence(clause, premises),
            "equiv_pos2" => self.equiv_pos2(clause),
            "implies" => self.implies(premises),
            "or_pos" => self.or_pos(clause),
            "and" => self.and_elimination(clause, premises, args),
            "xor1" => self.xor_one(clause, premises),
            "xor2" => self.xor_two(clause, premises),
            "xor_pos2" => self.xor_positive_two(clause, premises),
            "not_symm" => self.not_symmetry(clause, premises),
            "rare_rewrite" => self.rare_rewrite(clause, args),
            "evaluate" => self.evaluate(clause),
            "false" => self.false_rule(clause),
            // A `hole` step is a solver trust placeholder carrying no checked
            // content, so it is rejected before any handler can accept it.
            "hole" => Err(Error::Unsupported {
                message: "rule \"hole\" states an unchecked solver step".to_owned(),
            }),
            other => handler
                .apply(RuleRequest {
                    kernel: &mut self.kernel,
                    bool_ty: self.bool_ty,
                    rule: other,
                    clause,
                    premises,
                    args,
                })?
                .ok_or_else(|| Error::Unsupported {
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
        let mut theorem =
            self.kernel
                .expand_conclusion(theorem, Lit::positive(disjunction.get()), None)?;
        // The lowered disjunction is a binary tree, so a stated clause wider
        // than two disjuncts needs further expansion. Expansion is directed by
        // the stated clause, which keeps a disjunct that Alethe states as one
        // literal, such as the left operand of `(or (or a b) c)`, intact.
        let stated = clause[1..]
            .iter()
            .map(|literal| canonical_clause_literal(&self.kernel, *literal))
            .collect::<Result<BTreeSet<_>, _>>()?;
        loop {
            let mut expandable = None;
            for literal in conclusion_literals(&self.kernel, theorem)? {
                if !literal.is_positive() || stated.contains(&literal) {
                    continue;
                }
                let formula = reference(literal.magnitude())?;
                if self.kernel.arena().op2(formula) == Some(Op2::Or) {
                    expandable = Some(literal);
                    break;
                }
            }
            let Some(literal) = expandable else {
                break;
            };
            theorem = self.kernel.expand_conclusion(theorem, literal, None)?;
        }
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
        let (selected, theorem) = self.and_projection(conjunction, index)?;
        let theorem = self.kernel.cut(*premise, theorem, *source)?;
        self.convert_equality(theorem, selected, positive_unit(clause, "and")?)
    }

    fn and_projection(&mut self, conjunction: Ref, index: usize) -> Result<(Ref, ThmId), Error> {
        let Some((left, right)) = self.kernel.arena().op2(conjunction).and_then(|operator| {
            (operator == Op2::And).then(|| {
                let mut children = self
                    .kernel
                    .arena()
                    .children(conjunction)
                    .expect("a checked binary operator has children");
                (
                    children
                        .next()
                        .expect("a binary operator has a left operand"),
                    children
                        .next()
                        .expect("a binary operator has a right operand"),
                )
            })
        }) else {
            if index != 0 {
                return Err(Error::Malformed {
                    message: "and index is outside the conjunction".to_owned(),
                });
            }
            return Ok((
                conjunction,
                self.kernel.identity(Lit::positive(conjunction.get()))?,
            ));
        };
        let left_arity = conjunction_arity(&self.kernel, left);
        let (selected, theorem, other) = if index < left_arity {
            let (selected, theorem) = self.and_projection(left, index)?;
            (selected, theorem, right)
        } else {
            let (selected, theorem) = self.and_projection(right, index - left_arity)?;
            (selected, theorem, left)
        };
        self.kernel
            .weaken(theorem, &[Lit::positive(other.get())], &[])?;
        let theorem = self
            .kernel
            .and_left(theorem, Lit::positive(conjunction.get()))?;
        Ok((selected, theorem))
    }

    /// Derives `(cl (not a) b)` from an `(=> a b)` premise.
    ///
    /// Exactly one implication is expanded per literal, so a right-nested
    /// consequent such as `(=> p (=> q r))` keeps its inner implication
    /// instead of flattening into `(cl (not p) (not q) r)`.
    fn implies(&mut self, premises: &[ThmId]) -> Result<ThmId, Error> {
        let [premise] = premises else {
            return Err(Error::Malformed {
                message: "implies requires one premise".to_owned(),
            });
        };
        let formulas = conclusion_literals(&self.kernel, *premise)?;
        let mut result = *premise;
        let mut expanded = false;
        for formula in formulas {
            if !formula.is_positive() {
                continue;
            }
            let reference = reference(formula.magnitude())?;
            if self.kernel.arena().op2(reference) != Some(Op2::Imp) {
                continue;
            }
            result = self.kernel.expand_conclusion(result, formula, None)?;
            expanded = true;
        }
        if !expanded {
            return Err(Error::Malformed {
                message: "implies premise must conclude an implication".to_owned(),
            });
        }
        self.kernel.contract_theorem(result)?;
        Ok(result)
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
            "bool-xor-refl" => self.evaluate(clause),
            "distinct-binary-elim" => self.reflexivity(clause),
            "bool-eq-true" => self.bool_eq_true(clause),
            "bool-eq-false" => self.bool_eq_false(clause),
            "ite-true-cond" => self.ite_constant(clause, true),
            "ite-false-cond" => self.ite_constant(clause, false),
            other => Err(Error::Unsupported {
                message: format!("rare_rewrite {other:?}"),
            }),
        }
    }

    fn bool_eq_true(&mut self, clause: &[Lit]) -> Result<ThmId, Error> {
        let target = positive_unit(clause, "bool-eq-true")?;
        let [_bool_ty, equality, proposition] = equality_children(&self.kernel, target)?;
        let [_inner_bool_ty, left, truth] = equality_children(&self.kernel, equality)?;
        if self.kernel.arena().bool_value(truth) != Some(true) {
            return Err(Error::Malformed {
                message: "bool-eq-true does not compare with true".to_owned(),
            });
        }
        join_same_syntax(&mut self.kernel, left, proposition)?;

        let equality_assumption = self.kernel.identity(Lit::positive(equality.get()))?;
        let equality_implies_proposition = self.kernel.eqt_elim(equality_assumption)?;
        let proposition_assumption = self.kernel.identity(Lit::positive(proposition.get()))?;
        let proposition_implies_equality =
            self.equality_to_true(proposition, truth, proposition_assumption, equality)?;
        let result = self.kernel.deduct_antisym(
            self.bool_ty,
            equality,
            proposition,
            equality_implies_proposition,
            proposition_implies_equality,
        )?;
        self.convert_equality(result.theorem, result.equality, target)
    }

    fn bool_eq_false(&mut self, clause: &[Lit]) -> Result<ThmId, Error> {
        let target = positive_unit(clause, "bool-eq-false")?;
        let [_bool_ty, equality, negation] = equality_children(&self.kernel, target)?;
        let [_inner_bool_ty, proposition, falsehood] = equality_children(&self.kernel, equality)?;
        if self.kernel.arena().bool_value(falsehood) != Some(false)
            || self.kernel.arena().op1(negation) != Some(Op1::Not)
        {
            return Err(Error::Malformed {
                message: "bool-eq-false has the wrong shape".to_owned(),
            });
        }
        let negated = self
            .kernel
            .arena()
            .children(negation)
            .and_then(|mut children| children.next())
            .ok_or_else(|| Error::Malformed {
                message: "bool-eq-false negation has no operand".to_owned(),
            })?;
        join_same_syntax(&mut self.kernel, proposition, negated)?;

        let equality_assumption = self.kernel.identity(Lit::positive(equality.get()))?;
        let proposition_assumption = self.kernel.identity(Lit::positive(proposition.get()))?;
        let equality_implies_false = self
            .kernel
            .eq_mp(equality_assumption, proposition_assumption)?;
        self.kernel
            .not_right(equality_implies_false, Lit::positive(proposition.get()))?;
        let equality_implies_false = self
            .kernel
            .flatten_conclusion(equality_implies_false, Lit::positive(falsehood.get()))?;
        let equality_implies_negation = self
            .kernel
            .fold_conclusion(equality_implies_false, Lit::positive(negation.get()))?;

        let negation_assumption = self.kernel.identity(Lit::positive(negation.get()))?;
        let negation_assumption = self.kernel.expand_conclusion(
            negation_assumption,
            Lit::positive(negation.get()),
            None,
        )?;
        let proposition_assumption = self.kernel.identity(Lit::positive(proposition.get()))?;
        let contradiction = self.kernel.resolve(
            proposition_assumption,
            negation_assumption,
            Lit::positive(proposition.get()),
        )?;
        self.kernel
            .weaken(contradiction, &[], &[Lit::positive(falsehood.get())])?;
        let false_implies_proposition = self.kernel.false_left(Lit::positive(falsehood.get()))?;
        self.kernel.weaken(
            false_implies_proposition,
            &[],
            &[Lit::positive(proposition.get())],
        )?;
        let negation_implies_equality = self.kernel.deduct_antisym(
            self.bool_ty,
            proposition,
            falsehood,
            contradiction,
            false_implies_proposition,
        )?;
        let negation_implies_equality = self.convert_equality(
            negation_implies_equality.theorem,
            negation_implies_equality.equality,
            equality,
        )?;
        let result = self.kernel.deduct_antisym(
            self.bool_ty,
            equality,
            negation,
            equality_implies_negation,
            negation_implies_equality,
        )?;
        self.convert_equality(result.theorem, result.equality, target)
    }

    fn ite_constant(&mut self, clause: &[Lit], value: bool) -> Result<ThmId, Error> {
        let target = positive_unit(
            clause,
            if value {
                "ite-true-cond"
            } else {
                "ite-false-cond"
            },
        )?;
        let [_bool_ty, source, branch] = equality_children(&self.kernel, target)?;
        let cached = self.conditionals.clone();
        let conditional = cached
            .into_iter()
            .find_map(|(_, _, _, conditional)| {
                join_same_syntax(&mut self.kernel, conditional.term, source)
                    .ok()
                    .map(|_| conditional)
            })
            .ok_or_else(|| Error::Malformed {
                message: "ite rewrite does not name a lowered conditional".to_owned(),
            })?;
        if self.kernel.arena().bool_value(conditional.condition) != Some(value) {
            return Err(Error::Malformed {
                message: "ite rewrite condition is not the stated constant".to_owned(),
            });
        }
        let theorem = if value {
            conditional_when_true(&mut self.kernel, self.bool_ty, conditional)?
        } else {
            conditional_when_false(&mut self.kernel, self.bool_ty, conditional)?
        };
        let condition_equality = if value {
            conditional.condition_true
        } else {
            conditional.condition_false
        };
        let proved = self.kernel.refl(self.bool_ty, conditional.condition)?;
        let proved = self.convert_equality(proved.theorem, proved.equality, condition_equality)?;
        let theorem = self
            .kernel
            .cut(proved, theorem, Lit::positive(condition_equality.get()))?;
        let derived = positive_theorem_equality(&self.kernel, theorem)?;
        join_same_syntax(&mut self.kernel, conditional.term, source)?;
        join_same_syntax(
            &mut self.kernel,
            if value {
                conditional.then_branch
            } else {
                conditional.else_branch
            },
            branch,
        )?;
        self.convert_equality(theorem, derived, target)
    }

    fn xor_two(&mut self, clause: &[Lit], premises: &[ThmId]) -> Result<ThmId, Error> {
        let [premise] = premises else {
            return Err(Error::Malformed {
                message: "xor2 requires one premise".to_owned(),
            });
        };
        let [left_literal, right_literal] = clause else {
            return Err(Error::Malformed {
                message: "xor2 requires two literals".to_owned(),
            });
        };
        if left_literal.is_positive() || right_literal.is_positive() {
            return Err(Error::Unsupported {
                message: "xor2 polarity other than the negative pair".to_owned(),
            });
        }
        let source = conclusion_literals(&self.kernel, *premise)?;
        let [source] = source.as_slice() else {
            return Err(Error::Malformed {
                message: "xor2 premise must conclude one xor".to_owned(),
            });
        };
        let xor = reference(source.magnitude())?;
        let equality = self
            .kernel
            .arena()
            .children(xor)
            .and_then(|mut children| children.next())
            .ok_or_else(|| Error::Malformed {
                message: "xor2 premise is not a lowered xor".to_owned(),
            })?;
        let [_bool_ty, left, right] = equality_children(&self.kernel, equality)?;
        let truth = self.kernel.bool(self.bool_ty, true)?;
        let left_assumption = self.kernel.identity(Lit::positive(left.get()))?;
        let left_target = self.kernel.eq(self.bool_ty, left, truth)?;
        let left_true = self.equality_to_true(left, truth, left_assumption, left_target)?;
        let right_assumption = self.kernel.identity(Lit::positive(right.get()))?;
        let right_target = self.kernel.eq(self.bool_ty, right, truth)?;
        let right_true = self.equality_to_true(right, truth, right_assumption, right_target)?;
        let truth_right = equality_symmetry(&mut self.kernel, self.bool_ty, right_true)?;
        let equal = equality_transitivity(
            &mut self.kernel,
            self.bool_ty,
            left_true,
            truth_right.theorem,
        )?;
        let equal = self.convert_equality(equal.theorem, equal.equality, equality)?;
        let negative_equality = self.kernel.expand_conclusion(*premise, *source, None)?;
        let theorem = self.kernel.resolve(
            negative_equality,
            equal,
            Lit::positive(equality.get()).negated(),
        )?;
        self.kernel.not_right(theorem, Lit::positive(left.get()))?;
        self.kernel.not_right(theorem, Lit::positive(right.get()))?;
        self.kernel.contract_theorem(theorem)?;
        Ok(theorem)
    }

    fn xor_one(&mut self, clause: &[Lit], premises: &[ThmId]) -> Result<ThmId, Error> {
        let [premise] = premises else {
            return Err(Error::Malformed {
                message: "xor1 requires one premise".to_owned(),
            });
        };
        let [left_literal, right_literal] = clause else {
            return Err(Error::Malformed {
                message: "xor1 requires two literals".to_owned(),
            });
        };
        if !left_literal.is_positive() || !right_literal.is_positive() {
            return Err(Error::Unsupported {
                message: "xor1 polarity other than the positive pair".to_owned(),
            });
        }
        let source = conclusion_literals(&self.kernel, *premise)?;
        let [source] = source.as_slice() else {
            return Err(Error::Malformed {
                message: "xor1 premise must conclude one xor".to_owned(),
            });
        };
        let xor = reference(source.magnitude())?;
        let equality = self
            .kernel
            .arena()
            .children(xor)
            .and_then(|mut children| children.next())
            .ok_or_else(|| Error::Malformed {
                message: "xor1 premise is not a lowered xor".to_owned(),
            })?;
        let [_bool_ty, left, right] = equality_children(&self.kernel, equality)?;
        let falsehood = self.kernel.bool(self.bool_ty, false)?;
        let left_false = self.equality_under_negation(left, falsehood)?;
        let right_false = self.equality_under_negation(right, falsehood)?;
        let false_right = equality_symmetry(&mut self.kernel, self.bool_ty, right_false)?;
        let equal = equality_transitivity(
            &mut self.kernel,
            self.bool_ty,
            left_false,
            false_right.theorem,
        )?;
        let equal = self.convert_equality(equal.theorem, equal.equality, equality)?;
        let negative_equality = self.kernel.expand_conclusion(*premise, *source, None)?;
        let theorem = self.kernel.resolve(
            negative_equality,
            equal,
            Lit::positive(equality.get()).negated(),
        )?;
        self.kernel
            .not_right(theorem, Lit::positive(left.get()).negated())?;
        self.kernel
            .not_right(theorem, Lit::positive(right.get()).negated())?;
        self.kernel.contract_theorem(theorem)?;
        Ok(theorem)
    }

    fn xor_positive_two(&mut self, clause: &[Lit], premises: &[ThmId]) -> Result<ThmId, Error> {
        if !premises.is_empty() {
            return Err(Error::Malformed {
                message: "xor_pos2 does not take premises".to_owned(),
            });
        }
        let [negated_xor, left, right] = clause else {
            return Err(Error::Malformed {
                message: "xor_pos2 requires three literals".to_owned(),
            });
        };
        if negated_xor.is_positive() {
            return Err(Error::Malformed {
                message: "xor_pos2 must negate its xor".to_owned(),
            });
        }
        let xor = reference(negated_xor.magnitude())?;
        let assumption = self.kernel.identity(Lit::positive(xor.get()))?;
        let theorem = self.xor_two(&[*left, *right], &[assumption])?;
        self.kernel.not_right(theorem, Lit::positive(xor.get()))?;
        self.kernel.contract_theorem(theorem)?;
        Ok(theorem)
    }

    fn equality_under_negation(
        &mut self,
        proposition: Ref,
        falsehood: Ref,
    ) -> Result<ThmId, Error> {
        let positive = self.kernel.identity(Lit::positive(proposition.get()))?;
        let negative = self
            .kernel
            .identity(Lit::positive(proposition.get()).negated())?;
        let contradiction =
            self.kernel
                .resolve(positive, negative, Lit::positive(proposition.get()))?;
        self.kernel
            .weaken(contradiction, &[], &[Lit::positive(falsehood.get())])?;
        let false_implies_proposition = self.kernel.false_left(Lit::positive(falsehood.get()))?;
        self.kernel.weaken(
            false_implies_proposition,
            &[],
            &[Lit::positive(proposition.get())],
        )?;
        let equality = self.kernel.deduct_antisym(
            self.bool_ty,
            proposition,
            falsehood,
            contradiction,
            false_implies_proposition,
        )?;
        Ok(equality.theorem)
    }

    fn not_symmetry(&mut self, clause: &[Lit], premises: &[ThmId]) -> Result<ThmId, Error> {
        let [premise] = premises else {
            return Err(Error::Malformed {
                message: "not_symm requires one premise".to_owned(),
            });
        };
        let target = positive_unit(clause, "not_symm")?;
        let target_equality = self
            .kernel
            .arena()
            .children(target)
            .and_then(|mut children| children.next())
            .ok_or_else(|| Error::Malformed {
                message: "not_symm target is not a negation".to_owned(),
            })?;
        let source = conclusion_literals(&self.kernel, *premise)?;
        let [source] = source.as_slice() else {
            return Err(Error::Malformed {
                message: "not_symm premise must conclude one negation".to_owned(),
            });
        };
        let source_negation = reference(source.magnitude())?;
        let source_equality = self
            .kernel
            .arena()
            .children(source_negation)
            .and_then(|mut children| children.next())
            .ok_or_else(|| Error::Malformed {
                message: "not_symm premise is not a negation".to_owned(),
            })?;
        let negative_source = self.kernel.expand_conclusion(*premise, *source, None)?;
        let target_assumption = self.kernel.identity(Lit::positive(target_equality.get()))?;
        let symmetric = equality_symmetry(&mut self.kernel, self.bool_ty, target_assumption)?;
        let symmetric =
            self.convert_equality(symmetric.theorem, symmetric.equality, source_equality)?;
        let theorem = self.kernel.resolve(
            negative_source,
            symmetric,
            Lit::positive(source_equality.get()).negated(),
        )?;
        self.kernel
            .not_right(theorem, Lit::positive(target_equality.get()))?;
        let theorem = self
            .kernel
            .fold_conclusion(theorem, Lit::positive(target.get()))?;
        Ok(theorem)
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
        let conclusions = conclusion_literals(&self.kernel, left)?;
        if conclusions.is_empty() {
            self.kernel
                .weaken(left, &[], &[Lit::positive(constant.get())])?;
        } else if let [literal] = conclusions.as_slice()
            && !literal.is_positive()
        {
            let equality = reference(literal.magnitude())?;
            let [_domain, lhs, rhs] = equality_children(&self.kernel, equality)?;
            join_same_syntax(&mut self.kernel, lhs, rhs)?;
            let proved = self.kernel.refl(self.bool_ty, lhs)?;
            let proved = self.convert_equality(proved.theorem, proved.equality, equality)?;
            let contradiction = self.kernel.resolve(left, proved, *literal)?;
            self.kernel
                .weaken(contradiction, &[], &[Lit::positive(constant.get())])?;
            return self.equality_to_false(proposition, constant, contradiction, target);
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

    fn equality_to_false(
        &mut self,
        proposition: Ref,
        falsehood: Ref,
        proposition_implies_false: ThmId,
        target: Ref,
    ) -> Result<ThmId, Error> {
        let false_implies_proposition = self.kernel.false_left(Lit::positive(falsehood.get()))?;
        self.kernel.weaken(
            false_implies_proposition,
            &[],
            &[Lit::positive(proposition.get())],
        )?;
        let result = self.kernel.deduct_antisym(
            self.bool_ty,
            proposition,
            falsehood,
            proposition_implies_false,
            false_implies_proposition,
        )?;
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

    #[allow(clippy::too_many_lines)]
    fn congruence(&mut self, clause: &[Lit], premises: &[ThmId]) -> Result<ThmId, Error> {
        let target = positive_unit(clause, "cong")?;
        let [_domain, compact_left, compact_right] = equality_children(&self.kernel, target)?;
        if let Some(theorem) =
            self.conditional_congruence(target, compact_left, compact_right, premises)?
        {
            return Ok(theorem);
        }
        if let Some(theorem) =
            self.equality_congruence(target, compact_left, compact_right, premises)?
        {
            return Ok(theorem);
        }
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
                message: format!(
                    "cong premise count {} does not match application arities {} and {} for {compact_left:?} {:?} and {compact_right:?} {:?}; conditional terms {:?}",
                    premises.len(),
                    left_args.len(),
                    right_args.len(),
                    self.kernel.arena().tag(compact_left),
                    self.kernel.arena().tag(compact_right),
                    self.conditionals
                        .iter()
                        .map(|entry| entry.3.term)
                        .collect::<Vec<_>>(),
                ),
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

    #[allow(clippy::too_many_lines)]
    fn conditional_congruence(
        &mut self,
        target: Ref,
        left: Ref,
        right: Ref,
        premises: &[ThmId],
    ) -> Result<Option<ThmId>, Error> {
        let cached = self.conditionals.clone();
        let left_conditional = cached.iter().find_map(|(_, _, _, conditional)| {
            (conditional.term == left)
                .then_some(*conditional)
                .or_else(|| {
                    join_same_syntax(&mut self.kernel, conditional.term, left)
                        .ok()
                        .map(|_| *conditional)
                })
        });
        let right_conditional = cached.iter().find_map(|(_, _, _, conditional)| {
            (conditional.term == right)
                .then_some(*conditional)
                .or_else(|| {
                    join_same_syntax(&mut self.kernel, conditional.term, right)
                        .ok()
                        .map(|_| *conditional)
                })
        });
        let (Some(left_conditional), Some(right_conditional)) =
            (left_conditional, right_conditional)
        else {
            if left_conditional.is_some() || right_conditional.is_some() {
                return Err(Error::Malformed {
                    message: format!(
                        "cong relates one lowered conditional: left={}, right={}",
                        left_conditional.is_some(),
                        right_conditional.is_some()
                    ),
                });
            }
            return Ok(None);
        };
        let Some(value) = self.kernel.arena().bool_value(right_conditional.condition) else {
            return Ok(None);
        };
        if join_same_syntax(
            &mut self.kernel,
            left_conditional.then_branch,
            right_conditional.then_branch,
        )
        .is_err()
            || join_same_syntax(
                &mut self.kernel,
                left_conditional.else_branch,
                right_conditional.else_branch,
            )
            .is_err()
        {
            return Ok(None);
        }
        let [condition_premise, ..] = premises else {
            return Err(Error::Malformed {
                message: "conditional congruence has no condition premise".to_owned(),
            });
        };
        let condition_equality = positive_theorem_equality(&self.kernel, *condition_premise)?;
        let left_condition_equality = if value {
            left_conditional.condition_true
        } else {
            left_conditional.condition_false
        };
        self.convert_equality(
            *condition_premise,
            condition_equality,
            left_condition_equality,
        )?;

        let left_law = if value {
            conditional_when_true(&mut self.kernel, self.bool_ty, left_conditional)?
        } else {
            conditional_when_false(&mut self.kernel, self.bool_ty, left_conditional)?
        };
        let left_law = self.kernel.cut(
            *condition_premise,
            left_law,
            Lit::positive(left_condition_equality.get()),
        )?;

        let right_condition_equality = if value {
            right_conditional.condition_true
        } else {
            right_conditional.condition_false
        };
        let right_condition = self
            .kernel
            .refl(self.bool_ty, right_conditional.condition)?;
        let right_condition = self.convert_equality(
            right_condition.theorem,
            right_condition.equality,
            right_condition_equality,
        )?;
        let right_law = if value {
            conditional_when_true(&mut self.kernel, self.bool_ty, right_conditional)?
        } else {
            conditional_when_false(&mut self.kernel, self.bool_ty, right_conditional)?
        };
        let right_law = self.kernel.cut(
            right_condition,
            right_law,
            Lit::positive(right_condition_equality.get()),
        )?;
        let right_law = equality_symmetry(&mut self.kernel, self.bool_ty, right_law)?;
        let result =
            equality_transitivity(&mut self.kernel, self.bool_ty, left_law, right_law.theorem)?;
        self.convert_equality(result.theorem, result.equality, target)
            .map(Some)
    }

    fn equality_congruence(
        &mut self,
        target: Ref,
        left: Ref,
        right: Ref,
        premises: &[ThmId],
    ) -> Result<Option<ThmId>, Error> {
        if self.kernel.arena().tag(left) != Some(Tag::Tm(TmTag::Eq))
            || self.kernel.arena().tag(right) != Some(Tag::Tm(TmTag::Eq))
        {
            return Ok(None);
        }
        let [_left_ty, left_left, left_right] = equality_children(&self.kernel, left)?;
        let [_right_ty, right_left, right_right] = equality_children(&self.kernel, right)?;
        let left_operands = self.operand_equality(left_left, right_left, premises)?;
        let right_operands = self.operand_equality(left_right, right_right, premises)?;

        let left_reversed = equality_symmetry(&mut self.kernel, self.bool_ty, left_operands)?;
        let left_identity = self.kernel.identity(Lit::positive(left.get()))?;
        let forward = equality_transitivity(
            &mut self.kernel,
            self.bool_ty,
            left_reversed.theorem,
            left_identity,
        )?;
        let forward = equality_transitivity(
            &mut self.kernel,
            self.bool_ty,
            forward.theorem,
            right_operands,
        )?;
        let forward = self.convert_equality(forward.theorem, forward.equality, right)?;

        let right_reversed = equality_symmetry(&mut self.kernel, self.bool_ty, right_operands)?;
        let right_identity = self.kernel.identity(Lit::positive(right.get()))?;
        let backward = equality_transitivity(
            &mut self.kernel,
            self.bool_ty,
            left_operands,
            right_identity,
        )?;
        let backward = equality_transitivity(
            &mut self.kernel,
            self.bool_ty,
            backward.theorem,
            right_reversed.theorem,
        )?;
        let backward = self.convert_equality(backward.theorem, backward.equality, left)?;
        let result = self
            .kernel
            .deduct_antisym(self.bool_ty, left, right, forward, backward)?;
        self.convert_equality(result.theorem, result.equality, target)
            .map(Some)
    }

    fn operand_equality(
        &mut self,
        left: Ref,
        right: Ref,
        premises: &[ThmId],
    ) -> Result<ThmId, Error> {
        let target = self.kernel.eq(self.bool_ty, left, right)?;
        if join_same_syntax(&mut self.kernel, left, right).is_ok() {
            let proved = self.kernel.refl(self.bool_ty, left)?;
            return self.convert_equality(proved.theorem, proved.equality, target);
        }
        for &premise in premises {
            let source = positive_theorem_equality(&self.kernel, premise)?;
            let [_ty, source_left, source_right] = equality_children(&self.kernel, source)?;
            if join_same_syntax(&mut self.kernel, source_left, left).is_ok()
                && join_same_syntax(&mut self.kernel, source_right, right).is_ok()
            {
                let theorem = self.kernel.copy_theorem(premise)?;
                return self.convert_equality(theorem, source, target);
            }
            if join_same_syntax(&mut self.kernel, source_left, right).is_ok()
                && join_same_syntax(&mut self.kernel, source_right, left).is_ok()
            {
                let reversed = equality_symmetry(&mut self.kernel, self.bool_ty, premise)?;
                return self.convert_equality(reversed.theorem, reversed.equality, target);
            }
        }
        Err(Error::Malformed {
            message: "cong has no premise for a changed equality operand".to_owned(),
        })
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
                message: format!(
                    "refutation is not bound to the exact assertion set: actual {actual:?}, expected {expected:?}"
                ),
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

/// Replays a `QF_UF` Alethe proof and binds its empty-clause theorem to the
/// exact normalized assertion set from `problem`.
///
/// # Errors
///
/// Returns [`Error`] for unsupported syntax or rules, unasserted assumptions,
/// missing premises, mismatched clauses, or any rejected checked derivation.
pub fn replay_qf_uf(problem: &SmtProblem, proof: &AletheProof) -> Result<Refutation, Error> {
    replay_qf_uf_with_handler(problem, proof, &mut RejectUnknownRules)
}

/// Replays a `QF_UF` proof with a checked userspace fallback for unknown rules.
///
/// Handler results pass the same exact-clause and final assertion-set checks as
/// built-in replay rules.
///
/// # Errors
///
/// Returns [`Error`] under the same conditions as [`replay_qf_uf`], or when
/// `handler` rejects a rule it recognizes.
pub fn replay_qf_uf_with_handler(
    problem: &SmtProblem,
    proof: &AletheProof,
    handler: &mut impl RuleHandler,
) -> Result<Refutation, Error> {
    let mut replayer = Replayer::new()?;
    replayer.ingest_problem(problem)?;
    replayer.ingest_proof(proof, handler)
}

/// Requires the SMT-LIB Core minimum arity shared by `and`, `or` and `=>`.
fn arity_at_least_two<'a>(
    operator: &str,
    arguments: &'a [Expr],
) -> Result<(&'a Expr, &'a [Expr]), Error> {
    match arguments.split_first() {
        Some((first, rest)) if !rest.is_empty() => Ok((first, rest)),
        _ => Err(Error::Malformed {
            message: format!(
                "{operator} requires at least two arguments, got {}",
                arguments.len()
            ),
        }),
    }
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

fn conjunction_arity(kernel: &Kernel, term: Ref) -> usize {
    if kernel.arena().op2(term) != Some(Op2::And) {
        return 1;
    }
    kernel
        .arena()
        .children(term)
        .expect("a checked binary operator has children")
        .map(|child| conjunction_arity(kernel, child))
        .sum()
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

    const PROBLEM: &str = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../proof/alethe/tests/fixtures/cvc5-qf-uf/problem.smt2"
    ));
    const PROOF: &str = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../proof/alethe/tests/fixtures/cvc5-qf-uf/proof.alethe"
    ));

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
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert (xor p p))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(declare-const b U)\n(assert (distinct a b))\n(assert (= a b))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(declare-const b U)\n(declare-const p Bool)\n(assert (not (= (ite p a b) (ite p a b))))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert (let ((x p)) (and x (not x))))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(declare-const b U)\n(declare-const p Bool)\n(assert p)\n(assert (not (= (ite p a b) a)))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(declare-const b U)\n(declare-const p Bool)\n(assert (not p))\n(assert (not (= (ite p a b) b)))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n(assert (xor p q))\n(assert p)\n(assert q)\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(declare-const b U)\n(declare-const c U)\n(assert (distinct a b c))\n(assert (= a b))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n(assert (xor p q))\n(assert (not p))\n(assert (not q))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n(declare-const r Bool)\n(assert (xor p q r))\n(assert p)\n(assert q)\n(assert (not r))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n(assert (= p q))\n(assert p)\n(assert (not q))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n(declare-const r Bool)\n(assert (=> p q r))\n(assert p)\n(assert q)\n(assert (not r))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n(declare-const r Bool)\n(assert (or p q r))\n(assert (not p))\n(assert (not q))\n(assert (not r))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert (! p :named hyp))\n(assert (not p))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(declare-const b U)\n(declare-const c U)\n(assert (= a b c))\n(assert (not (= a c)))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(declare-const b U)\n(declare-const c U)\n(assert (distinct a b c))\n(assert (= b c))\n(check-sat)\n",
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
                "--proof-granularity=dsl-rewrite",
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
            Err(Error::ClauseMismatch { .. } | Error::Kernel { .. })
        ));
    }

    /// Lowers `problem_source` and returns its kernel with the lowered
    /// assertion rows in source order.
    fn lowered_assertions(problem_source: &str) -> (Kernel, Vec<Ref>) {
        let problem = parse_smtlib2(problem_source).expect("problem parses");
        let mut replayer = Replayer::new().expect("checked Boolean init compiles");
        replayer.ingest_problem(&problem).expect("problem lowers");
        let rows = replayer
            .assertion_terms
            .iter()
            .map(|term| term.reference)
            .collect();
        (replayer.kernel, rows)
    }

    #[test]
    fn lowers_implication_right_associatively() {
        let (mut kernel, rows) = lowered_assertions(
            "(set-logic QF_UF)\n\
             (declare-const p Bool)\n\
             (declare-const q Bool)\n\
             (declare-const r Bool)\n\
             (assert (=> p q r))\n\
             (assert (=> p (=> q r)))\n\
             (assert (=> (=> p q) r))\n\
             (check-sat)\n",
        );
        let [flat, nested, left] = rows.as_slice() else {
            panic!("three assertions lower to three rows");
        };
        assert!(
            join_same_syntax(&mut kernel, *flat, *left).is_err(),
            "(=> p q r) must not lower like (=> (=> p q) r)"
        );
        join_same_syntax(&mut kernel, *flat, *nested)
            .expect("(=> p q r) lowers like (=> p (=> q r))");
    }

    #[test]
    fn rejects_a_left_associated_implication_assumption() {
        // The problem is satisfiable (p false, r false); only the discarded
        // left-associative reading of `(=> p q r)` is unsatisfiable, so the
        // assumption stating that reading must not match any assertion.
        let problem = parse_smtlib2(
            "(set-logic QF_UF)\n\
             (declare-const p Bool)\n\
             (declare-const q Bool)\n\
             (declare-const r Bool)\n\
             (assert (=> p q r))\n\
             (assert (not p))\n\
             (assert (not r))\n\
             (check-sat)\n",
        )
        .expect("problem parses");
        let proof = parse_alethe("(assume a0 (=> (=> p q) r))").expect("proof parses");
        assert!(matches!(
            replay_qf_uf(&problem, &proof),
            Err(Error::UnassertedAssumption)
        ));
    }

    #[test]
    fn rejects_degenerate_boolean_arities() {
        for source in [
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert (=> p))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert (and p))\n(check-sat)\n",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert (or p))\n(check-sat)\n",
        ] {
            let problem = parse_smtlib2(source).expect("problem parses");
            let proof = parse_alethe("(assume a0 p)").expect("proof parses");
            assert!(
                matches!(replay_qf_uf(&problem, &proof), Err(Error::Malformed { .. })),
                "unary Boolean operator accepted in: {source}"
            );
        }
    }

    #[test]
    fn let_binders_shadow_constants() {
        let (mut kernel, rows) = lowered_assertions(
            "(set-logic QF_UF)\n\
             (assert (let ((true false)) true))\n\
             (assert false)\n\
             (check-sat)\n",
        );
        let [shadowed, constant] = rows.as_slice() else {
            panic!("two assertions lower to two rows");
        };
        join_same_syntax(&mut kernel, *shadowed, *constant)
            .expect("a let binder shadows the constant true");
    }

    #[test]
    fn let_binders_shadow_named_terms() {
        let (mut kernel, rows) = lowered_assertions(
            "(set-logic QF_UF)\n\
             (declare-const p Bool)\n\
             (declare-const q Bool)\n\
             (assert (! p :named @x))\n\
             (assert (let ((@x q)) @x))\n\
             (assert q)\n\
             (check-sat)\n",
        );
        let [named, shadowed, binding] = rows.as_slice() else {
            panic!("three assertions lower to three rows");
        };
        assert!(
            join_same_syntax(&mut kernel, *shadowed, *named).is_err(),
            "a let binder must win over the @-named term"
        );
        join_same_syntax(&mut kernel, *shadowed, *binding)
            .expect("a let binder resolves to its bound value");
    }

    #[test]
    fn rejects_reserved_and_colliding_names() {
        let problem = parse_smtlib2(
            "(set-logic QF_UF)\n(declare-const @p_1 Bool)\n(assert @p_1)\n(check-sat)\n",
        )
        .expect("problem parses");
        let proof = parse_alethe("(assume a0 @p_1)").expect("proof parses");
        assert!(matches!(
            replay_qf_uf(&problem, &proof),
            Err(Error::Unsupported { .. })
        ));

        let problem = parse_smtlib2(
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert (! p :named p))\n(check-sat)\n",
        )
        .expect("problem parses");
        let proof = parse_alethe("(assume a0 p)").expect("proof parses");
        assert!(matches!(
            replay_qf_uf(&problem, &proof),
            Err(Error::Malformed { .. })
        ));
    }

    #[test]
    fn rejects_non_boolean_xor_operands() {
        let problem = parse_smtlib2(
            "(set-logic QF_UF)\n\
             (declare-sort U 0)\n\
             (declare-const a U)\n\
             (declare-const b U)\n\
             (assert (xor a b))\n\
             (check-sat)\n",
        )
        .expect("problem parses");
        let proof = parse_alethe("(assume a0 (xor a b))").expect("proof parses");
        assert!(matches!(
            replay_qf_uf(&problem, &proof),
            Err(Error::Malformed { .. })
        ));
    }

    #[test]
    fn rejects_a_hole_step_without_consulting_a_handler() {
        struct AcceptEverything(bool);

        impl RuleHandler for AcceptEverything {
            fn apply(&mut self, _request: RuleRequest<'_>) -> Result<Option<ThmId>, Error> {
                self.0 = true;
                Ok(None)
            }
        }

        let problem = parse_smtlib2(
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n",
        )
        .expect("problem parses");
        let proof = parse_alethe(
            "(assume a0 p)\n\
             (assume a1 (not p))\n\
             (step t0 (cl) :rule hole :premises (a0 a1))",
        )
        .expect("proof parses");
        let mut handler = AcceptEverything(false);
        assert!(matches!(
            replay_qf_uf_with_handler(&problem, &proof, &mut handler),
            Err(Error::Unsupported { .. })
        ));
        assert!(!handler.0, "a hole step must never reach a rule handler");
    }

    #[test]
    fn rejects_an_over_deep_term() {
        let depth = MAX_TERM_DEPTH + 8;
        let source = format!(
            "(set-logic QF_UF)\n(declare-const p Bool)\n(assert {}p{})\n(check-sat)\n",
            "(not ".repeat(depth),
            ")".repeat(depth)
        );
        let problem = parse_smtlib2(&source).expect("problem parses");
        let proof = parse_alethe("(assume a0 p)").expect("proof parses");
        assert!(matches!(
            replay_qf_uf(&problem, &proof),
            Err(Error::TermTooDeep {
                limit: MAX_TERM_DEPTH
            })
        ));
    }

    #[test]
    fn checks_a_user_defined_rule_handler() {
        struct ReflexivityHandler;

        impl RuleHandler for ReflexivityHandler {
            fn apply(&mut self, request: RuleRequest<'_>) -> Result<Option<ThmId>, Error> {
                if request.rule != "user-refute-refl" {
                    return Ok(None);
                }
                if !request.clause.is_empty() {
                    return Err(Error::Malformed {
                        message: "user-refute-refl expects the empty clause".to_owned(),
                    });
                }
                let [premise] = request.premises else {
                    return Err(Error::Malformed {
                        message: "user-refute-refl expects one premise".to_owned(),
                    });
                };
                let conclusions = conclusion_literals(request.kernel, *premise)?;
                let [source] = conclusions.as_slice() else {
                    return Err(Error::Malformed {
                        message: "user-refute-refl premise is not a unit".to_owned(),
                    });
                };
                let negation = reference(source.magnitude())?;
                let target = request
                    .kernel
                    .arena()
                    .children(negation)
                    .and_then(|mut children| children.next())
                    .ok_or_else(|| Error::Malformed {
                        message: "user-refute-refl premise is not a negation".to_owned(),
                    })?;
                let [_ty, left, right] = equality_children(request.kernel, target)?;
                join_same_syntax(request.kernel, left, right)?;
                let theorem = request.kernel.refl(request.bool_ty, left)?;
                join_same_syntax(request.kernel, theorem.equality, target)?;
                request
                    .kernel
                    .convert_conclusions(theorem.theorem, theorem.equality, target)?;
                let negative = request.kernel.expand_conclusion(*premise, *source, None)?;
                Ok(Some(request.kernel.resolve(
                    negative,
                    theorem.theorem,
                    Lit::positive(target.get()).negated(),
                )?))
            }
        }

        let problem = parse_smtlib2(
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(assert (not (= a a)))\n(check-sat)\n",
        )
        .expect("problem parses");
        let proof = parse_alethe(
            "(assume a0 (not (= a a)))\n\
             (step t0 (cl) :rule user-refute-refl :premises (a0))",
        )
        .expect("proof parses");
        replay_qf_uf_with_handler(&problem, &proof, &mut ReflexivityHandler)
            .expect("handler theorem is checked and replayed");
        assert!(matches!(
            replay_qf_uf(&problem, &proof),
            Err(Error::Unsupported { .. })
        ));
    }
}
