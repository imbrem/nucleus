//! Lossless browser boundary for the checked classical HOL kernel.

use covalence_logic_hol::{
    Kernel, Lit, LitVec, Ref, RowId, ThmId,
    builtin::{Op1, Op2},
};
use wasm_bindgen::prelude::*;

use crate::classical::Refutation;

use crate::to_js;

/// A checked classical HOL prover for browser tactics.
///
/// Proposition, theorem, and matrix-row identifiers cross the `JavaScript`
/// boundary as native signed 32-bit numbers.
#[wasm_bindgen]
pub struct HolProver {
    kernel: Kernel,
    bool_ty: Ref,
}

#[wasm_bindgen]
impl HolProver {
    /// Creates an empty prover with its Boolean type initialized.
    ///
    /// # Errors
    ///
    /// Returns an error if the kernel reference space is exhausted.
    #[wasm_bindgen(constructor)]
    pub fn new() -> Result<Self, JsError> {
        Self::try_new().map_err(to_js)
    }

    /// Creates a Boolean free variable and returns its positive literal.
    ///
    /// # Errors
    ///
    /// Returns an error if `name` is not a decimal `u64`, or allocation fails.
    #[wasm_bindgen(js_name = proposition)]
    pub fn proposition_js(&mut self, name: &str) -> Result<i32, JsError> {
        self.proposition(name).map(format_prop).map_err(to_js)
    }

    /// Creates a Boolean constant and returns its positive literal.
    ///
    /// # Errors
    ///
    /// Returns an error if allocation fails.
    #[wasm_bindgen(js_name = boolean)]
    pub fn boolean_js(&mut self, value: bool) -> Result<i32, JsError> {
        self.boolean(value).map(format_prop).map_err(to_js)
    }

    /// Returns the complementary signed literal.
    ///
    /// # Errors
    ///
    /// Returns an error if `proposition` is zero or outside the literal domain.
    #[wasm_bindgen(js_name = complement)]
    pub fn complement_js(proposition: i32) -> Result<i32, JsError> {
        parse_prop(proposition)
            .map(Lit::negated)
            .map(format_prop)
            .map_err(to_js)
    }

    /// Builds the conjunction of two signed propositions.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or failed checked construction.
    #[wasm_bindgen(js_name = and)]
    pub fn and_js(&mut self, left: i32, right: i32) -> Result<i32, JsError> {
        self.binary(Op2::And, left, right)
            .map(format_prop)
            .map_err(to_js)
    }

    /// Builds the disjunction of two signed propositions.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or failed checked construction.
    #[wasm_bindgen(js_name = or)]
    pub fn or_js(&mut self, left: i32, right: i32) -> Result<i32, JsError> {
        self.binary(Op2::Or, left, right)
            .map(format_prop)
            .map_err(to_js)
    }

    /// Builds the implication of two signed propositions.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or failed checked construction.
    #[wasm_bindgen(js_name = implies)]
    pub fn implies_js(&mut self, left: i32, right: i32) -> Result<i32, JsError> {
        self.binary(Op2::Imp, left, right)
            .map(format_prop)
            .map_err(to_js)
    }

    /// Introduces `[p] |- [p]`.
    ///
    /// # Errors
    ///
    /// Returns an error for an invalid proposition or failed kernel rule.
    pub fn identity(&mut self, proposition: i32) -> Result<i32, JsError> {
        let proposition = parse_prop(proposition).map_err(to_js)?;
        self.kernel
            .identity(proposition)
            .map(format_thm)
            .map_err(to_js)
    }

    /// Weakens a theorem with native signed 32-bit literal arrays.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed contexts, a missing theorem, or a failed rule.
    pub fn weaken(
        &mut self,
        theorem: i32,
        premises: &[i32],
        conclusions: &[i32],
    ) -> Result<(), JsError> {
        let theorem = parse_thm(theorem).map_err(to_js)?;
        let premises = parse_context(premises).map_err(to_js)?;
        let conclusions = parse_context(conclusions).map_err(to_js)?;
        self.kernel
            .weaken(theorem, &premises, &conclusions)
            .map_err(to_js)
    }

    /// Cuts `proposition` between two theorems.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs, missing theorems, or mismatched evidence.
    pub fn cut(&mut self, left: i32, right: i32, proposition: i32) -> Result<i32, JsError> {
        self.rule2_prop(left, right, proposition, Kernel::cut)
    }

    /// Introduces checked falsity on the left.
    ///
    /// # Errors
    ///
    /// Returns an error unless the ID names signed false.
    #[wasm_bindgen(js_name = falseLeft)]
    pub fn false_left(&mut self, proposition: i32) -> Result<i32, JsError> {
        self.rule0_prop(proposition, Kernel::false_left)
    }

    /// Introduces checked truth on the right.
    ///
    /// # Errors
    ///
    /// Returns an error unless the ID names signed true.
    #[wasm_bindgen(js_name = trueRight)]
    pub fn true_right(&mut self, proposition: i32) -> Result<i32, JsError> {
        self.rule0_prop(proposition, Kernel::true_right)
    }

    /// Applies left polarity transfer.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or mismatched evidence.
    #[wasm_bindgen(js_name = notLeft)]
    pub fn not_left(&mut self, theorem: i32, proposition: i32) -> Result<(), JsError> {
        let theorem = parse_thm(theorem).map_err(to_js)?;
        let proposition = parse_prop(proposition).map_err(to_js)?;
        self.kernel.not_left(theorem, proposition).map_err(to_js)
    }

    /// Applies right polarity transfer.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or mismatched evidence.
    #[wasm_bindgen(js_name = notRight)]
    pub fn not_right(&mut self, theorem: i32, proposition: i32) -> Result<(), JsError> {
        let theorem = parse_thm(theorem).map_err(to_js)?;
        let proposition = parse_prop(proposition).map_err(to_js)?;
        self.kernel.not_right(theorem, proposition).map_err(to_js)
    }

    /// Introduces conjunction on the left.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or mismatched evidence.
    #[wasm_bindgen(js_name = andLeft)]
    pub fn and_left(&mut self, theorem: i32, proposition: i32) -> Result<i32, JsError> {
        self.rule1_prop(theorem, proposition, Kernel::and_left)
    }

    /// Introduces conjunction on the right.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or mismatched evidence.
    #[wasm_bindgen(js_name = andRight)]
    pub fn and_right(&mut self, left: i32, right: i32, proposition: i32) -> Result<i32, JsError> {
        self.rule2_prop(left, right, proposition, Kernel::and_right)
    }

    /// Introduces disjunction on the left.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or mismatched evidence.
    #[wasm_bindgen(js_name = orLeft)]
    pub fn or_left(&mut self, left: i32, right: i32, proposition: i32) -> Result<i32, JsError> {
        self.rule2_prop(left, right, proposition, Kernel::or_left)
    }

    /// Introduces disjunction on the right.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or mismatched evidence.
    #[wasm_bindgen(js_name = orRight)]
    pub fn or_right(&mut self, theorem: i32, proposition: i32) -> Result<i32, JsError> {
        self.rule1_prop(theorem, proposition, Kernel::or_right)
    }

    /// Introduces implication on the left.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or mismatched evidence.
    #[wasm_bindgen(js_name = impLeft)]
    pub fn imp_left(&mut self, left: i32, right: i32, proposition: i32) -> Result<i32, JsError> {
        self.rule2_prop(left, right, proposition, Kernel::imp_left)
    }

    /// Introduces implication on the right.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or mismatched evidence.
    #[wasm_bindgen(js_name = impRight)]
    pub fn imp_right(&mut self, theorem: i32, proposition: i32) -> Result<i32, JsError> {
        self.rule1_prop(theorem, proposition, Kernel::imp_right)
    }

    /// Resolves complementary conclusions.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or mismatched evidence.
    pub fn resolve(&mut self, left: i32, right: i32, proposition: i32) -> Result<i32, JsError> {
        self.rule2_prop(left, right, proposition, Kernel::resolve)
    }

    /// Expands one connective in a theorem conclusion.
    ///
    /// `branch` is required for a conjunctive normalized result and ignored
    /// for a disjunctive result.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs, an unsupported connective, or an
    /// inappropriate branch.
    #[wasm_bindgen(js_name = expandConclusion)]
    pub fn expand_conclusion(
        &mut self,
        theorem: i32,
        formula: i32,
        branch: Option<bool>,
    ) -> Result<i32, JsError> {
        let theorem = parse_thm(theorem).map_err(to_js)?;
        let formula = parse_prop(formula).map_err(to_js)?;
        self.kernel
            .expand_conclusion(theorem, formula, branch)
            .map(format_thm)
            .map_err(to_js)
    }

    /// Recursively flattens a disjunctive opcode tree in a conclusion.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs, mismatched evidence, or a
    /// conjunctive normalized node.
    #[wasm_bindgen(js_name = flattenConclusion)]
    pub fn flatten_conclusion(&mut self, theorem: i32, formula: i32) -> Result<i32, JsError> {
        self.rule1_prop(theorem, formula, Kernel::flatten_conclusion)
    }

    /// Recursively flattens a conjunctive opcode tree in a premise.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs, mismatched evidence, or a
    /// disjunctive normalized node.
    #[wasm_bindgen(js_name = flattenPremise)]
    pub fn flatten_premise(&mut self, theorem: i32, formula: i32) -> Result<i32, JsError> {
        self.rule1_prop(theorem, formula, Kernel::flatten_premise)
    }

    /// Folds all conjunctive leaves in a premise into an opcode tree.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs, mismatched evidence, or a
    /// disjunctive normalized node.
    #[wasm_bindgen(js_name = foldPremise)]
    pub fn fold_premise(&mut self, theorem: i32, formula: i32) -> Result<i32, JsError> {
        self.rule1_prop(theorem, formula, Kernel::fold_premise)
    }

    /// Folds all disjunctive leaves in a conclusion into an opcode tree.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs, mismatched evidence, or a
    /// conjunctive normalized node.
    #[wasm_bindgen(js_name = foldConclusion)]
    pub fn fold_conclusion(&mut self, theorem: i32, formula: i32) -> Result<i32, JsError> {
        self.rule1_prop(theorem, formula, Kernel::fold_conclusion)
    }

    /// Copies a theorem into an allocated or reused slot.
    ///
    /// # Errors
    ///
    /// Returns an error if the source ID is malformed or absent.
    #[wasm_bindgen(js_name = copyTheorem)]
    pub fn copy_theorem(&mut self, source: i32) -> Result<i32, JsError> {
        let source = parse_thm(source).map_err(to_js)?;
        self.kernel
            .copy_theorem(source)
            .map(format_thm)
            .map_err(to_js)
    }

    /// Introduces object-language equality reflexivity.
    ///
    /// Returns `[equality, theorem]` using native signed 32-bit identifiers.
    ///
    /// # Errors
    ///
    /// Returns an error unless `bool_ty` is Boolean and `term` is checked.
    #[wasm_bindgen(js_name = refl)]
    pub fn refl(&mut self, bool_ty: i32, term: i32) -> Result<Vec<i32>, JsError> {
        self.kernel
            .refl(
                parse_ref(bool_ty).map_err(to_js)?,
                parse_ref(term).map_err(to_js)?,
            )
            .map(|result| vec![result.equality.get(), result.theorem.get()])
            .map_err(to_js)
    }

    /// Applies a proved function equality to one term, preserving its premises.
    ///
    /// The returned `Int32Array` is `[left, right, equality, theorem]`.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed or mismatched evidence. Rejection does
    /// not mutate the prover.
    #[wasm_bindgen(js_name = apThm)]
    pub fn ap_thm(&mut self, theorem: i32, argument: i32) -> Result<Vec<i32>, JsError> {
        let theorem = parse_thm(theorem).map_err(to_js)?;
        let argument = parse_ref(argument).map_err(to_js)?;
        self.kernel
            .ap_thm(theorem, argument)
            .map(|result| {
                vec![
                    result.left.get(),
                    result.right.get(),
                    result.equality.get(),
                    result.theorem.get(),
                ]
            })
            .map_err(to_js)
    }

    /// Applies one function to both sides of a proved equality.
    ///
    /// Returns `[left, right, equality, theorem]`.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed or mismatched evidence.
    #[wasm_bindgen(js_name = apTerm)]
    pub fn ap_term(&mut self, theorem: i32, function: i32) -> Result<Vec<i32>, JsError> {
        let theorem = parse_thm(theorem).map_err(to_js)?;
        let function = parse_ref(function).map_err(to_js)?;
        self.kernel
            .ap_term(theorem, function)
            .map(|result| {
                vec![
                    result.left.get(),
                    result.right.get(),
                    result.equality.get(),
                    result.theorem.get(),
                ]
            })
            .map_err(to_js)
    }

    /// Rewrites a proved proposition through a proved Boolean equality.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed or mismatched evidence.
    #[wasm_bindgen(js_name = eqMp)]
    pub fn eq_mp(&mut self, equality: i32, premise: i32) -> Result<i32, JsError> {
        self.kernel
            .eq_mp(
                parse_thm(equality).map_err(to_js)?,
                parse_thm(premise).map_err(to_js)?,
            )
            .map(format_thm)
            .map_err(to_js)
    }

    /// Generalizes one theorem over a fresh term variable.
    ///
    /// Returns `[universal, theorem]`.
    ///
    /// # Errors
    ///
    /// Returns an error if the freshness or theorem-shape check fails.
    #[wasm_bindgen(js_name = forallIntro)]
    pub fn forall_intro(&mut self, theorem: i32, binder: i32) -> Result<Vec<i32>, JsError> {
        self.kernel
            .forall_intro(
                parse_thm(theorem).map_err(to_js)?,
                parse_ref(binder).map_err(to_js)?,
            )
            .map(|result| vec![result.universal.get(), result.theorem.get()])
            .map_err(to_js)
    }

    /// Generalizes into an existing equality-encoded universal.
    ///
    /// # Errors
    ///
    /// Returns an error if the target or freshness check fails.
    #[wasm_bindgen(js_name = forallIntroAt)]
    pub fn forall_intro_at(
        &mut self,
        theorem: i32,
        binder: i32,
        universal: i32,
    ) -> Result<i32, JsError> {
        self.kernel
            .forall_intro_at(
                parse_thm(theorem).map_err(to_js)?,
                parse_ref(binder).map_err(to_js)?,
                parse_ref(universal).map_err(to_js)?,
            )
            .map(format_thm)
            .map_err(to_js)
    }

    /// Introduces Hilbert choice, returning `[witness, proposition, theorem]`.
    ///
    /// # Errors
    ///
    /// Returns an error unless the theorem concludes a predicate application.
    #[wasm_bindgen(js_name = choiceIntro)]
    pub fn choice_intro(&mut self, theorem: i32) -> Result<Vec<i32>, JsError> {
        self.kernel
            .choice_intro(parse_thm(theorem).map_err(to_js)?)
            .map(|result| {
                vec![
                    result.witness.get(),
                    result.proposition.get(),
                    result.theorem.get(),
                ]
            })
            .map_err(to_js)
    }

    /// Introduces Hilbert choice into an existing target proposition.
    ///
    /// # Errors
    ///
    /// Returns an error unless the target is the matching choice application.
    #[wasm_bindgen(js_name = choiceIntroAt)]
    pub fn choice_intro_at(&mut self, theorem: i32, target: i32) -> Result<i32, JsError> {
        self.kernel
            .choice_intro_at(
                parse_thm(theorem).map_err(to_js)?,
                parse_ref(target).map_err(to_js)?,
            )
            .map(format_thm)
            .map_err(to_js)
    }

    /// Rewrites every occurrence of one semantically equal theorem atom.
    ///
    /// # Errors
    ///
    /// Returns an error unless the theorem and semantic equality exist.
    #[wasm_bindgen(js_name = convertTheorem)]
    pub fn convert_theorem(
        &mut self,
        theorem: i32,
        source: i32,
        target: i32,
    ) -> Result<(), JsError> {
        self.kernel
            .convert_theorem(
                parse_thm(theorem).map_err(to_js)?,
                parse_ref(source).map_err(to_js)?,
                parse_ref(target).map_err(to_js)?,
            )
            .map_err(to_js)
    }

    /// Rewrites one semantically equal atom only in theorem conclusions.
    ///
    /// # Errors
    ///
    /// Returns an error unless the theorem and semantic equality exist.
    #[wasm_bindgen(js_name = convertConclusions)]
    pub fn convert_conclusions(
        &mut self,
        theorem: i32,
        source: i32,
        target: i32,
    ) -> Result<(), JsError> {
        self.kernel
            .convert_conclusions(
                parse_thm(theorem).map_err(to_js)?,
                parse_ref(source).map_err(to_js)?,
                parse_ref(target).map_err(to_js)?,
            )
            .map_err(to_js)
    }

    /// Contracts duplicate theorem rows and literals in place.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem handle is absent.
    #[wasm_bindgen(js_name = contractTheorem)]
    pub fn contract_theorem(&mut self, theorem: i32) -> Result<(), JsError> {
        self.kernel
            .contract_theorem(parse_thm(theorem).map_err(to_js)?)
            .map_err(to_js)
    }

    /// Eliminates `Γ ⊢ p = true` to `Γ ⊢ p`.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed or mismatched evidence.
    #[wasm_bindgen(js_name = eqtElim)]
    pub fn eqt_elim(&mut self, theorem: i32) -> Result<i32, JsError> {
        let theorem = parse_thm(theorem).map_err(to_js)?;
        self.kernel.eqt_elim(theorem).map(format_thm).map_err(to_js)
    }

    /// Removes one theorem, returning whether the handle was live.
    ///
    /// # Errors
    ///
    /// Returns an error if `theorem` is not a valid theorem ID.
    #[wasm_bindgen(js_name = removeTheorem)]
    pub fn remove_theorem(&mut self, theorem: i32) -> Result<bool, JsError> {
        let theorem = parse_thm(theorem).map_err(to_js)?;
        Ok(self.kernel.remove_theorem(theorem))
    }

    /// Returns a theorem as JSON containing numeric proposition arrays.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem ID is malformed, absent, or deleted.
    #[wasm_bindgen(js_name = theoremJson)]
    pub fn theorem_json(&self, theorem: i32) -> Result<String, JsError> {
        self.snapshot(theorem).map_err(to_js)
    }

    /// Copies a checked propositional refutation into the universal syllogism arena.
    ///
    /// # Errors
    ///
    /// Returns an error if theorem storage is exhausted.
    #[wasm_bindgen(js_name = copyRefutationToSyllogisms)]
    pub fn copy_refutation_to_syllogisms(
        &mut self,
        refutation: &Refutation,
    ) -> Result<i32, JsError> {
        self.kernel
            .syl_mut()
            .copy_refutation(&refutation.0)
            .map(ThmId::get)
            .map_err(to_js)
    }

    /// Copies a checked propositional refutation into the HOL theorem arena.
    ///
    /// # Errors
    ///
    /// Returns an error if theorem storage is exhausted.
    #[wasm_bindgen(js_name = copyRefutationToTheorems)]
    pub fn copy_refutation_to_theorems(&mut self, refutation: &Refutation) -> Result<i32, JsError> {
        self.kernel
            .thm_mut()
            .copy_refutation(&refutation.0)
            .map(ThmId::get)
            .map_err(to_js)
    }

    /// Weakens a theorem with complete CNF clauses and DNF cubes.
    ///
    /// Both matrix arguments are JSON arrays of rows containing signed
    /// literals as JSON numbers.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed JSON, invalid IDs, a missing theorem,
    /// or a row containing a non-Boolean proposition.
    #[wasm_bindgen(js_name = weakenMatrix)]
    pub fn weaken_matrix(
        &mut self,
        theorem: i32,
        premises_json: &str,
        conclusions_json: &str,
    ) -> Result<(), JsError> {
        let theorem = parse_thm(theorem).map_err(to_js)?;
        let premises = parse_matrix(premises_json).map_err(to_js)?;
        let conclusions = parse_matrix(conclusions_json).map_err(to_js)?;
        self.kernel
            .weaken_matrix(theorem, &premises, &conclusions)
            .map_err(to_js)
    }

    /// Moves a one-based left clause to the right with complemented literals.
    ///
    /// # Errors
    ///
    /// Returns an error for a malformed index or absent theorem/clause.
    #[wasm_bindgen(js_name = moveCnfRight)]
    pub fn move_cnf_right(&mut self, theorem: i32, index: i32) -> Result<(), JsError> {
        let theorem = parse_thm(theorem).map_err(to_js)?;
        let row = parse_cnf(index).map_err(to_js)?;
        self.kernel.move_cnf_right(theorem, row).map_err(to_js)
    }

    /// Moves a one-based right cube to the left with complemented literals.
    ///
    /// # Errors
    ///
    /// Returns an error for a malformed index or absent theorem/cube.
    #[wasm_bindgen(js_name = moveDnfLeft)]
    pub fn move_dnf_left(&mut self, theorem: i32, index: i32) -> Result<(), JsError> {
        let theorem = parse_thm(theorem).map_err(to_js)?;
        let row = parse_dnf(index).map_err(to_js)?;
        self.kernel.move_dnf_left(theorem, row).map_err(to_js)
    }

    /// Sorts and deduplicates the selected one-based left clause in place.
    ///
    /// # Errors
    ///
    /// Returns an error for a malformed index or absent theorem/clause.
    #[wasm_bindgen(js_name = normalizeCnf)]
    pub fn normalize_cnf(&mut self, theorem: i32, index: i32) -> Result<(), JsError> {
        let theorem = parse_thm(theorem).map_err(to_js)?;
        let row = parse_cnf(index).map_err(to_js)?;
        self.kernel.normalize_cnf(theorem, row).map_err(to_js)
    }

    /// Sorts and deduplicates the selected one-based right cube in place.
    ///
    /// # Errors
    ///
    /// Returns an error for a malformed index or absent theorem/cube.
    #[wasm_bindgen(js_name = normalizeDnf)]
    pub fn normalize_dnf(&mut self, theorem: i32, index: i32) -> Result<(), JsError> {
        let theorem = parse_thm(theorem).map_err(to_js)?;
        let row = parse_dnf(index).map_err(to_js)?;
        self.kernel.normalize_dnf(theorem, row).map_err(to_js)
    }
}

impl HolProver {
    fn try_new() -> Result<Self, covalence_logic_hol::KernelError> {
        let mut kernel = Kernel::new();
        let star = kernel.star()?;
        let bool_ty = kernel.bool_ty(star)?;
        Ok(Self { kernel, bool_ty })
    }

    fn proposition(&mut self, name: &str) -> Result<Lit, String> {
        let name = parse_u64(name, "proposition name")?;
        self.kernel
            .tm_fv(name, self.bool_ty)
            .map(|reference| Lit::positive(reference.get()))
            .map_err(|error| error.to_string())
    }

    fn boolean(&mut self, value: bool) -> Result<Lit, String> {
        self.kernel
            .bool(self.bool_ty, value)
            .map(|reference| Lit::positive(reference.get()))
            .map_err(|error| error.to_string())
    }

    fn materialize(&mut self, proposition: Lit) -> Result<Ref, String> {
        if proposition.is_positive() {
            Ok(Ref::new(
                i32::try_from(proposition.magnitude()).expect("literal magnitude fits i32"),
            )
            .expect("literal magnitude is nonzero"))
        } else {
            self.kernel
                .op1(
                    Op1::Not,
                    Ref::new(
                        i32::try_from(proposition.magnitude()).expect("literal magnitude fits i32"),
                    )
                    .expect("literal magnitude is nonzero"),
                )
                .map_err(|error| error.to_string())
        }
    }

    fn binary(&mut self, op: Op2, left: i32, right: i32) -> Result<Lit, String> {
        let left = self.materialize(parse_prop(left)?)?;
        let right = self.materialize(parse_prop(right)?)?;
        self.kernel
            .op2(op, left, right)
            .map(|reference| Lit::positive(reference.get()))
            .map_err(|error| error.to_string())
    }

    fn snapshot(&self, theorem: i32) -> Result<String, String> {
        let id = parse_thm(theorem)?;
        let theorem = self
            .kernel
            .thm()
            .get(id)
            .ok_or_else(|| format!("theorem {} is absent", id.get()))?;
        Ok(format!(
            "{{\"premises\":[{}],\"conclusions\":[{}]}}",
            json_rows(theorem.lhs.rows()),
            json_rows(theorem.rhs.rows())
        ))
    }

    fn rule0_prop(
        &mut self,
        proposition: i32,
        rule: fn(&mut Kernel, Lit) -> Result<ThmId, covalence_logic_hol::KernelError>,
    ) -> Result<i32, JsError> {
        let proposition = parse_prop(proposition).map_err(to_js)?;
        rule(&mut self.kernel, proposition)
            .map(format_thm)
            .map_err(to_js)
    }

    fn rule1_prop(
        &mut self,
        theorem: i32,
        proposition: i32,
        rule: fn(&mut Kernel, ThmId, Lit) -> Result<ThmId, covalence_logic_hol::KernelError>,
    ) -> Result<i32, JsError> {
        let theorem = parse_thm(theorem).map_err(to_js)?;
        let proposition = parse_prop(proposition).map_err(to_js)?;
        rule(&mut self.kernel, theorem, proposition)
            .map(format_thm)
            .map_err(to_js)
    }

    fn rule2_prop(
        &mut self,
        left: i32,
        right: i32,
        proposition: i32,
        rule: fn(&mut Kernel, ThmId, ThmId, Lit) -> Result<ThmId, covalence_logic_hol::KernelError>,
    ) -> Result<i32, JsError> {
        let left = parse_thm(left).map_err(to_js)?;
        let right = parse_thm(right).map_err(to_js)?;
        let proposition = parse_prop(proposition).map_err(to_js)?;
        rule(&mut self.kernel, left, right, proposition)
            .map(format_thm)
            .map_err(to_js)
    }
}

fn parse_u64(text: &str, label: &str) -> Result<u64, String> {
    text.parse()
        .map_err(|_| format!("{label} must be a decimal u64"))
}

fn parse_prop(value: i32) -> Result<Lit, String> {
    Lit::try_new(value).map_err(|error| error.to_string())
}

fn parse_ref(value: i32) -> Result<Ref, String> {
    Ref::new(value).ok_or_else(|| "references are one-based".to_owned())
}

fn parse_thm(value: i32) -> Result<ThmId, String> {
    ThmId::new(value).ok_or_else(|| "theorem IDs are one-based".to_owned())
}

fn parse_cnf(value: i32) -> Result<RowId, String> {
    RowId::new(value).ok_or_else(|| "CNF row IDs are one-based".to_owned())
}

fn parse_dnf(value: i32) -> Result<RowId, String> {
    RowId::new(value).ok_or_else(|| "DNF row IDs are one-based".to_owned())
}

fn parse_context(values: &[i32]) -> Result<Vec<Lit>, String> {
    values.iter().copied().map(parse_prop).collect()
}

fn parse_matrix(text: &str) -> Result<Vec<LitVec>, String> {
    let rows: Vec<Vec<i32>> = covalence_lib_json::from_str(text)
        .map_err(|error| format!("invalid matrix JSON: {error}"))?;
    rows.into_iter()
        .map(|row| row.into_iter().map(parse_prop).collect())
        .collect()
}

fn format_prop(proposition: Lit) -> i32 {
    proposition.get()
}

fn format_thm(theorem: ThmId) -> i32 {
    theorem.get()
}

fn json_props(propositions: &[Lit]) -> String {
    propositions
        .iter()
        .map(|proposition| proposition.get().to_string())
        .collect::<Vec<_>>()
        .join(",")
}

fn json_rows<'a>(rows: impl IntoIterator<Item = &'a [Lit]>) -> String {
    rows.into_iter()
        .map(|row| format!("[{}]", json_props(row)))
        .collect::<Vec<_>>()
        .join(",")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn prover() -> HolProver {
        HolProver::try_new().unwrap()
    }

    #[allow(clippy::needless_pass_by_value)]
    fn unit_premises(theorem: covalence_logic_hol::ThmRef) -> Vec<Lit> {
        theorem.lhs.rows().map(|clause| clause[0]).collect()
    }

    #[allow(clippy::needless_pass_by_value)]
    fn unit_conclusions(theorem: covalence_logic_hol::ThmRef) -> Vec<Lit> {
        theorem.rhs.rows().map(|cube| cube[0]).collect()
    }

    #[test]
    fn lossless_signed_ids_and_non_normal_contexts() {
        assert!(parse_prop(0).is_err());
        assert!(parse_prop(i32::MIN).is_err());
        assert!(parse_prop(i32::MAX).is_err());
        assert!(parse_thm(0).is_err());
        assert_eq!(parse_thm(i32::MAX).unwrap().get(), i32::MAX);

        let mut prover = prover();
        let p = prover.proposition("18446744073709551615").unwrap();
        let q = prover.proposition("2").unwrap();
        let base = prover.kernel.identity(p).unwrap();
        prover.kernel.weaken(base, &[q, p, q], &[q, p]).unwrap();
        let snapshot = prover.snapshot(format_thm(base)).unwrap();
        assert_eq!(
            snapshot,
            format!(
                "{{\"premises\":[[{}],[{}],[{}],[{}]],\"conclusions\":[[{}],[{}],[{}]]}}",
                p.get(),
                q.get(),
                p.get(),
                q.get(),
                p.get(),
                q.get(),
                p.get()
            )
        );
    }

    #[test]
    fn deletion_is_atomic_and_slots_are_reused_lifo() {
        let mut prover = prover();
        let p = prover.proposition("1").unwrap();
        let q = prover.proposition("2").unwrap();
        let first = prover.kernel.identity(p).unwrap();
        let second = prover.kernel.identity(q).unwrap();

        assert!(prover.kernel.remove_theorem(first));
        assert!(!prover.kernel.remove_theorem(first));
        assert!(prover.kernel.thm().get(first).is_none());
        assert!(prover.kernel.thm().get(second).is_some());

        assert!(prover.kernel.remove_theorem(second));
        assert!(prover.kernel.thm().get(second).is_none());
        let reused_second = prover.kernel.identity(p).unwrap();
        let reused_first = prover.kernel.identity(q).unwrap();
        assert_eq!(reused_second, second);
        assert_eq!(reused_first, first);
    }

    #[test]
    fn copy_allocates_and_reuses_freed_slots() {
        let mut prover = prover();
        let p = prover.proposition("1").unwrap();
        let q = prover.proposition("2").unwrap();
        let source = prover.kernel.identity(p).unwrap();
        let freed = prover.kernel.identity(q).unwrap();

        let copied = prover.kernel.copy_theorem(source).unwrap();
        assert_ne!(copied, source);
        assert_ne!(copied, freed);
        assert_eq!(
            prover.kernel.thm().get(copied).unwrap(),
            prover.kernel.thm().get(source).unwrap()
        );
        assert!(prover.kernel.remove_theorem(freed));
        let reused = prover.kernel.copy_theorem(source).unwrap();
        assert_eq!(reused, freed);
        assert_eq!(unit_premises(prover.kernel.thm().get(source).unwrap()), [p]);
        assert_eq!(unit_premises(prover.kernel.thm().get(reused).unwrap()), [p]);
    }

    #[test]
    fn theorem_lifecycle_boundary_returns_i32_ids_and_booleans() {
        let mut prover = prover();
        let p = prover.proposition("1").unwrap();
        let source = prover.kernel.identity(p).unwrap();
        let copied = prover.copy_theorem(format_thm(source)).unwrap();

        assert_ne!(copied, format_thm(source));
        assert!(prover.remove_theorem(copied).unwrap());
        assert!(!prover.remove_theorem(copied).unwrap());
    }

    #[test]
    fn matrix_boundary_round_trips_nested_rows_and_indexed_transfer() {
        let mut prover = prover();
        let p = prover.proposition("1").unwrap();
        let q = prover.proposition("2").unwrap();
        let theorem = prover.kernel.identity(p).unwrap();
        let theorem_id = format_thm(theorem);
        let clause_json = format!(r"[[{},{}]]", q.get(), p.negated().get());
        let cube_json = format!(r"[[{},{}]]", q.negated().get(), p.get());
        prover
            .weaken_matrix(theorem_id, &clause_json, &cube_json)
            .unwrap();
        let snapshot = prover.theorem_json(theorem_id).unwrap();
        assert!(snapshot.contains(&format!(r"[{},{}]", q.get(), p.negated().get())));
        assert!(snapshot.contains(&format!(r"[{},{}]", q.negated().get(), p.get())));

        let clause_index = prover
            .kernel
            .thm()
            .get(theorem)
            .unwrap()
            .lhs
            .rows()
            .position(|clause| clause.len() == 2)
            .unwrap();
        prover
            .move_cnf_right(theorem_id, i32::try_from(clause_index + 1).unwrap())
            .unwrap();
        assert!(
            prover
                .kernel
                .thm()
                .get(theorem)
                .unwrap()
                .rhs
                .rows()
                .any(|cube| cube.len() == 2)
        );
    }

    #[test]
    fn matrix_boundary_emits_exact_nested_json_and_exposes_normalization() {
        let mut prover = prover();
        let p = prover.proposition("1").unwrap();
        let q = prover.proposition("2").unwrap();
        let theorem = prover.kernel.identity(p).unwrap();
        let theorem_id = format_thm(theorem);
        let clauses = format!(
            r"[[{},{},{}],[{}],[{},{},{}]]",
            q.get(),
            p.get(),
            q.get(),
            p.get(),
            p.get(),
            q.get(),
            p.get()
        );
        let cubes = format!(
            r"[[{},{},{}],[{}],[{},{},{}]]",
            p.get(),
            q.get(),
            p.get(),
            p.get(),
            q.get(),
            p.get(),
            q.get()
        );
        prover.weaken_matrix(theorem_id, &clauses, &cubes).unwrap();

        let raw = format!(
            concat!(
                "{{\"premises\":[[{}],[{},{},{}],[{}],[{},{},{}]],",
                "\"conclusions\":[[{}],[{},{},{}],[{}],[{},{},{}]]}}"
            ),
            p.get(),
            q.get(),
            p.get(),
            q.get(),
            p.get(),
            p.get(),
            q.get(),
            p.get(),
            p.get(),
            p.get(),
            q.get(),
            p.get(),
            p.get(),
            q.get(),
            p.get(),
            q.get()
        );
        assert_eq!(prover.theorem_json(theorem_id).unwrap(), raw);

        prover.normalize_cnf(theorem_id, 2).unwrap();
        prover.normalize_dnf(theorem_id, 2).unwrap();
        let normalized_rows = format!(
            concat!(
                "{{\"premises\":[[{}],[{},{}],[{}],[{},{},{}]],",
                "\"conclusions\":[[{}],[{},{}],[{}],[{},{},{}]]}}"
            ),
            p.get(),
            q.get(),
            p.get(),
            p.get(),
            p.get(),
            q.get(),
            p.get(),
            p.get(),
            q.get(),
            p.get(),
            p.get(),
            q.get(),
            p.get(),
            q.get()
        );
        assert_eq!(prover.theorem_json(theorem_id).unwrap(), normalized_rows);
    }

    #[test]
    fn matrix_index_failures_leave_theorem_unchanged() {
        let mut prover = prover();
        let p = prover.proposition("1").unwrap();
        let q = prover.proposition("2").unwrap();
        let theorem = prover.kernel.identity(p).unwrap();
        let theorem_id = format_thm(theorem);
        prover
            .weaken_matrix(
                theorem_id,
                &format!(r"[[{},{},{}]]", q.get(), p.get(), q.get()),
                &format!(r"[[{},{},{}]]", p.get(), q.get(), p.get()),
            )
            .unwrap();
        let before = prover.theorem_json(theorem_id).unwrap();

        assert!(parse_cnf(-1).is_err());
        assert!(parse_cnf(0).is_err());
        assert_eq!(prover.theorem_json(theorem_id).unwrap(), before);
        assert!(
            prover
                .kernel
                .normalize_cnf(theorem, RowId::new(99).unwrap())
                .is_err()
        );
        assert_eq!(prover.theorem_json(theorem_id).unwrap(), before);
        assert!(parse_dnf(-1).is_err());
        assert!(parse_dnf(0).is_err());
        assert_eq!(prover.theorem_json(theorem_id).unwrap(), before);
        assert!(
            prover
                .kernel
                .normalize_dnf(theorem, RowId::new(99).unwrap())
                .is_err()
        );
        assert_eq!(prover.theorem_json(theorem_id).unwrap(), before);
        assert!(
            prover
                .kernel
                .move_cnf_right(theorem, RowId::new(99).unwrap())
                .is_err()
        );
        assert_eq!(prover.theorem_json(theorem_id).unwrap(), before);
        assert!(
            prover
                .kernel
                .move_dnf_left(theorem, RowId::new(99).unwrap())
                .is_err()
        );
        assert_eq!(prover.theorem_json(theorem_id).unwrap(), before);
    }

    #[test]
    fn in_place_rules_preserve_handle_and_are_transactional() {
        let mut prover = prover();
        let p = prover.proposition("1").unwrap();
        let q = prover.proposition("2").unwrap();
        let theorem = prover.kernel.identity(p).unwrap();
        let theorem_id = format_thm(theorem);

        prover
            .weaken(theorem_id, &[format_prop(q)], &[format_prop(q)])
            .unwrap();
        let weakened = prover.snapshot(theorem_id).unwrap();
        assert!(weakened.contains(&format!("{}", p.get())));
        assert!(weakened.contains(&format!("{}", q.get())));

        assert!(prover.kernel.not_left(theorem, q.negated()).is_err());
        assert_eq!(prover.snapshot(theorem_id).unwrap(), weakened);
        prover.not_left(theorem_id, format_prop(p)).unwrap();
        assert_eq!(
            unit_conclusions(prover.kernel.thm().get(theorem).unwrap()),
            [q]
        );

        prover.not_right(theorem_id, format_prop(q)).unwrap();
        assert_eq!(
            unit_premises(prover.kernel.thm().get(theorem).unwrap()),
            [p, p.negated()]
        );
        assert_eq!(
            unit_conclusions(prover.kernel.thm().get(theorem).unwrap()),
            [q, q.negated()]
        );
    }

    #[test]
    fn every_exported_rule_rejects_bad_evidence() {
        let mut prover = prover();
        let p = prover.proposition("1").unwrap();
        let q = prover.proposition("2").unwrap();
        let p_id = format_prop(p);
        let q_id = format_prop(q);
        let theorem = prover.kernel.identity(p).unwrap();
        let theorem_id = format_thm(theorem);
        let conjunction = format_prop(prover.binary(Op2::And, p_id, q_id).unwrap());
        let disjunction = format_prop(prover.binary(Op2::Or, p_id, q_id).unwrap());
        let implication = format_prop(prover.binary(Op2::Imp, p_id, q_id).unwrap());

        assert!(prover.kernel.cut(theorem, theorem, q).is_err());
        assert!(prover.kernel.false_left(p).is_err());
        assert!(prover.kernel.true_right(p).is_err());
        assert!(prover.kernel.not_left(theorem, q).is_err());
        assert!(prover.kernel.not_right(theorem, q).is_err());
        assert!(
            prover
                .kernel
                .and_left(theorem, parse_prop(conjunction).unwrap())
                .is_err()
        );
        assert!(
            prover
                .kernel
                .and_right(theorem, theorem, parse_prop(conjunction).unwrap())
                .is_err()
        );
        assert!(
            prover
                .kernel
                .or_left(theorem, theorem, parse_prop(disjunction).unwrap())
                .is_err()
        );
        assert!(
            prover
                .kernel
                .or_right(theorem, parse_prop(disjunction).unwrap())
                .is_err()
        );
        assert!(
            prover
                .kernel
                .imp_left(theorem, theorem, parse_prop(implication).unwrap())
                .is_err()
        );
        assert!(
            prover
                .kernel
                .imp_right(theorem, parse_prop(implication).unwrap())
                .is_err()
        );
        assert!(prover.kernel.resolve(theorem, theorem, p).is_err());

        assert!(prover.kernel.remove_theorem(theorem));
        assert!(prover.snapshot(theorem_id).is_err());
        assert!(prover.kernel.weaken(theorem, &[], &[]).is_err());
    }

    #[test]
    fn signed_operands_are_materialized_without_changing_meaning() {
        let mut prover = prover();
        let p = prover.proposition("1").unwrap();
        let not_p = p.negated();
        let conjunction = prover
            .binary(Op2::And, format_prop(not_p), format_prop(p))
            .unwrap();
        assert!(conjunction.is_positive());
        let children = prover
            .kernel
            .children(Ref::new(i32::try_from(conjunction.magnitude()).unwrap()).unwrap())
            .unwrap()
            .collect::<Vec<_>>();
        assert_eq!(children.len(), 2);
        assert_eq!(prover.kernel.arena().op1(children[0]), Some(Op1::Not));
        assert_eq!(
            children[1],
            Ref::new(i32::try_from(p.magnitude()).unwrap()).unwrap()
        );
    }

    #[test]
    fn boundary_parsing_and_tree_operations_round_trip() {
        let mut prover = prover();
        let p = prover.proposition("1").unwrap();
        let q = prover.proposition("2").unwrap();
        let conjunction = prover
            .binary(Op2::And, format_prop(p), format_prop(q))
            .unwrap();
        let identity = prover.kernel.identity(conjunction).unwrap();

        let flattened = prover
            .kernel
            .flatten_premise(identity, conjunction)
            .unwrap();
        let flattened_json = prover.snapshot(format_thm(flattened)).unwrap();
        assert!(flattened_json.contains(&format!("{}", p.get())));
        assert!(flattened_json.contains(&format!("{}", q.get())));

        let folded = prover.kernel.fold_premise(flattened, conjunction).unwrap();
        assert_eq!(
            unit_premises(prover.kernel.thm().get(folded).unwrap()),
            [conjunction]
        );
        assert_eq!(
            parse_context(&[q.get(), p.get(), q.get()]).unwrap(),
            [q, p, q]
        );
        assert!(parse_context(&[-1, 0]).is_err());
    }

    #[test]
    fn standard_hol_rules_cross_the_i32_browser_boundary() {
        let mut prover = prover();
        let p = prover.proposition("1").unwrap();
        let q = prover.proposition("2").unwrap();
        let p_ref = Ref::new(i32::try_from(p.magnitude()).unwrap()).unwrap();
        let q_ref = Ref::new(i32::try_from(q.magnitude()).unwrap()).unwrap();
        let bool_ty = prover.bool_ty;

        let reflexive = prover.refl(bool_ty.get(), p_ref.get()).unwrap();
        assert_eq!(reflexive.len(), 2);
        assert!(reflexive.iter().all(|value| *value > 0));

        let equality = prover.kernel.eq(bool_ty, p_ref, q_ref).unwrap();
        let equality_assumption = prover
            .kernel
            .identity(Lit::positive(equality.get()))
            .unwrap();
        let function_ty = prover.kernel.ty_arr(bool_ty, bool_ty).unwrap();
        let function = prover.kernel.tm_fv(20, function_ty).unwrap();
        let applied = prover
            .ap_term(equality_assumption.get(), function.get())
            .unwrap();
        assert_eq!(applied.len(), 4);
        assert!(applied.iter().all(|value| *value > 0));

        let premise = prover.kernel.identity(p).unwrap();
        let rewritten = prover
            .eq_mp(equality_assumption.get(), premise.get())
            .unwrap();
        assert_eq!(
            unit_conclusions(
                prover
                    .kernel
                    .thm()
                    .get(ThmId::new(rewritten).unwrap())
                    .unwrap()
            ),
            [q]
        );

        let binder = prover.kernel.tm_fv(21, bool_ty).unwrap();
        let truth = prover.kernel.bool(bool_ty, true).unwrap();
        let body = prover
            .kernel
            .true_right(Lit::positive(truth.get()))
            .unwrap();
        let generalized = prover.forall_intro(body.get(), binder.get()).unwrap();
        assert_eq!(generalized.len(), 2);

        let predicate = prover.kernel.tm_fv(22, function_ty).unwrap();
        let application = prover.kernel.app(predicate, p_ref).unwrap();
        let witnessed = prover
            .kernel
            .identity(Lit::positive(application.get()))
            .unwrap();
        let choice = prover.choice_intro(witnessed.get()).unwrap();
        assert_eq!(choice.len(), 3);
        assert!(choice.iter().all(|value| *value > 0));
    }
}
