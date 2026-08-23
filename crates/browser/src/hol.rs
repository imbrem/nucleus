//! Lossless browser boundary for the checked classical HOL kernel.

use covalence_logic_hol::{
    Kernel, PropId, Ref, ThmId,
    builtin::{Op1, Op2},
};
use wasm_bindgen::prelude::*;

use crate::to_js;

/// A checked classical HOL prover for browser tactics.
///
/// Proposition and theorem identifiers cross the `JavaScript` boundary as
/// decimal strings, so all valid kernel identifiers remain exact.
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

    /// Creates a Boolean free variable and returns its positive proposition ID.
    ///
    /// # Errors
    ///
    /// Returns an error if `name` is not a decimal `u64`, or allocation fails.
    #[wasm_bindgen(js_name = proposition)]
    pub fn proposition_js(&mut self, name: &str) -> Result<String, JsError> {
        self.proposition(name).map(format_prop).map_err(to_js)
    }

    /// Creates a Boolean literal and returns its positive proposition ID.
    ///
    /// # Errors
    ///
    /// Returns an error if allocation fails.
    #[wasm_bindgen(js_name = boolean)]
    pub fn boolean_js(&mut self, value: bool) -> Result<String, JsError> {
        self.boolean(value).map(format_prop).map_err(to_js)
    }

    /// Returns the complementary signed proposition ID.
    ///
    /// # Errors
    ///
    /// Returns an error if `proposition` is not a valid signed decimal ID.
    #[wasm_bindgen(js_name = complement)]
    pub fn complement_js(proposition: &str) -> Result<String, JsError> {
        parse_prop(proposition)
            .map(PropId::negated)
            .map(format_prop)
            .map_err(to_js)
    }

    /// Builds the conjunction of two signed propositions.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or failed checked construction.
    #[wasm_bindgen(js_name = and)]
    pub fn and_js(&mut self, left: &str, right: &str) -> Result<String, JsError> {
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
    pub fn or_js(&mut self, left: &str, right: &str) -> Result<String, JsError> {
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
    pub fn implies_js(&mut self, left: &str, right: &str) -> Result<String, JsError> {
        self.binary(Op2::Imp, left, right)
            .map(format_prop)
            .map_err(to_js)
    }

    /// Introduces `[p] |- [p]`.
    ///
    /// # Errors
    ///
    /// Returns an error for an invalid proposition or failed kernel rule.
    pub fn identity(&mut self, proposition: &str) -> Result<String, JsError> {
        let proposition = parse_prop(proposition).map_err(to_js)?;
        self.kernel
            .identity(proposition)
            .map(format_thm)
            .map_err(to_js)
    }

    /// Weakens a theorem with whitespace-separated signed proposition IDs.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed contexts, a missing theorem, or a failed rule.
    pub fn weaken(
        &mut self,
        theorem: &str,
        premises: &str,
        conclusions: &str,
    ) -> Result<String, JsError> {
        let theorem = parse_thm(theorem).map_err(to_js)?;
        let premises = parse_context(premises).map_err(to_js)?;
        let conclusions = parse_context(conclusions).map_err(to_js)?;
        self.kernel
            .weaken(theorem, &premises, &conclusions)
            .map(format_thm)
            .map_err(to_js)
    }

    /// Cuts `proposition` between two theorems.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs, missing theorems, or mismatched evidence.
    pub fn cut(&mut self, left: &str, right: &str, proposition: &str) -> Result<String, JsError> {
        self.rule2_prop(left, right, proposition, Kernel::cut)
    }

    /// Introduces checked falsity on the left.
    ///
    /// # Errors
    ///
    /// Returns an error unless the ID names signed false.
    #[wasm_bindgen(js_name = falseLeft)]
    pub fn false_left(&mut self, proposition: &str) -> Result<String, JsError> {
        self.rule0_prop(proposition, Kernel::false_left)
    }

    /// Introduces checked truth on the right.
    ///
    /// # Errors
    ///
    /// Returns an error unless the ID names signed true.
    #[wasm_bindgen(js_name = trueRight)]
    pub fn true_right(&mut self, proposition: &str) -> Result<String, JsError> {
        self.rule0_prop(proposition, Kernel::true_right)
    }

    /// Applies left polarity transfer.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or mismatched evidence.
    #[wasm_bindgen(js_name = notLeft)]
    pub fn not_left(&mut self, theorem: &str, proposition: &str) -> Result<String, JsError> {
        self.rule1_prop(theorem, proposition, Kernel::not_left)
    }

    /// Applies right polarity transfer.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or mismatched evidence.
    #[wasm_bindgen(js_name = notRight)]
    pub fn not_right(&mut self, theorem: &str, proposition: &str) -> Result<String, JsError> {
        self.rule1_prop(theorem, proposition, Kernel::not_right)
    }

    /// Introduces conjunction on the left.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or mismatched evidence.
    #[wasm_bindgen(js_name = andLeft)]
    pub fn and_left(&mut self, theorem: &str, proposition: &str) -> Result<String, JsError> {
        self.rule1_prop(theorem, proposition, Kernel::and_left)
    }

    /// Introduces conjunction on the right.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or mismatched evidence.
    #[wasm_bindgen(js_name = andRight)]
    pub fn and_right(
        &mut self,
        left: &str,
        right: &str,
        proposition: &str,
    ) -> Result<String, JsError> {
        self.rule2_prop(left, right, proposition, Kernel::and_right)
    }

    /// Introduces disjunction on the left.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or mismatched evidence.
    #[wasm_bindgen(js_name = orLeft)]
    pub fn or_left(
        &mut self,
        left: &str,
        right: &str,
        proposition: &str,
    ) -> Result<String, JsError> {
        self.rule2_prop(left, right, proposition, Kernel::or_left)
    }

    /// Introduces disjunction on the right.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or mismatched evidence.
    #[wasm_bindgen(js_name = orRight)]
    pub fn or_right(&mut self, theorem: &str, proposition: &str) -> Result<String, JsError> {
        self.rule1_prop(theorem, proposition, Kernel::or_right)
    }

    /// Introduces implication on the left.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or mismatched evidence.
    #[wasm_bindgen(js_name = impLeft)]
    pub fn imp_left(
        &mut self,
        left: &str,
        right: &str,
        proposition: &str,
    ) -> Result<String, JsError> {
        self.rule2_prop(left, right, proposition, Kernel::imp_left)
    }

    /// Introduces implication on the right.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or mismatched evidence.
    #[wasm_bindgen(js_name = impRight)]
    pub fn imp_right(&mut self, theorem: &str, proposition: &str) -> Result<String, JsError> {
        self.rule1_prop(theorem, proposition, Kernel::imp_right)
    }

    /// Resolves complementary conclusions.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs or mismatched evidence.
    pub fn resolve(
        &mut self,
        left: &str,
        right: &str,
        proposition: &str,
    ) -> Result<String, JsError> {
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
        theorem: &str,
        formula: &str,
        branch: Option<bool>,
    ) -> Result<String, JsError> {
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
    pub fn flatten_conclusion(&mut self, theorem: &str, formula: &str) -> Result<String, JsError> {
        self.rule1_prop(theorem, formula, Kernel::flatten_conclusion)
    }

    /// Recursively flattens a conjunctive opcode tree in a premise.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs, mismatched evidence, or a
    /// disjunctive normalized node.
    #[wasm_bindgen(js_name = flattenPremise)]
    pub fn flatten_premise(&mut self, theorem: &str, formula: &str) -> Result<String, JsError> {
        self.rule1_prop(theorem, formula, Kernel::flatten_premise)
    }

    /// Folds all conjunctive leaves in a premise into an opcode tree.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs, mismatched evidence, or a
    /// disjunctive normalized node.
    #[wasm_bindgen(js_name = foldPremise)]
    pub fn fold_premise(&mut self, theorem: &str, formula: &str) -> Result<String, JsError> {
        self.rule1_prop(theorem, formula, Kernel::fold_premise)
    }

    /// Folds all disjunctive leaves in a conclusion into an opcode tree.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid IDs, mismatched evidence, or a
    /// conjunctive normalized node.
    #[wasm_bindgen(js_name = foldConclusion)]
    pub fn fold_conclusion(&mut self, theorem: &str, formula: &str) -> Result<String, JsError> {
        self.rule1_prop(theorem, formula, Kernel::fold_conclusion)
    }

    /// Deletes whitespace-separated theorem IDs atomically.
    ///
    /// # Errors
    ///
    /// Returns an error if any ID is malformed, duplicated, absent, or already deleted.
    #[wasm_bindgen(js_name = removeTheorems)]
    pub fn remove_theorems(&mut self, theorem_ids: &str) -> Result<(), JsError> {
        let ids = parse_theorems(theorem_ids).map_err(to_js)?;
        self.kernel.remove_theorems(&ids).map_err(to_js)
    }

    /// Returns a theorem as JSON containing string-valued proposition arrays.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem ID is malformed, absent, or deleted.
    #[wasm_bindgen(js_name = theoremJson)]
    pub fn theorem_json(&self, theorem: &str) -> Result<String, JsError> {
        self.snapshot(theorem).map_err(to_js)
    }
}

impl HolProver {
    fn try_new() -> Result<Self, covalence_logic_hol::KernelError> {
        let mut kernel = Kernel::new();
        let star = kernel.star()?;
        let bool_ty = kernel.bool_ty(star)?;
        Ok(Self { kernel, bool_ty })
    }

    fn proposition(&mut self, name: &str) -> Result<PropId, String> {
        let name = parse_u64(name, "proposition name")?;
        self.kernel
            .tm_fv(name, self.bool_ty)
            .map(PropId::positive)
            .map_err(|error| error.to_string())
    }

    fn boolean(&mut self, value: bool) -> Result<PropId, String> {
        self.kernel
            .bool(self.bool_ty, value)
            .map(PropId::positive)
            .map_err(|error| error.to_string())
    }

    fn materialize(&mut self, proposition: PropId) -> Result<Ref, String> {
        if proposition.is_positive() {
            Ok(proposition.reference())
        } else {
            self.kernel
                .op1(Op1::Not, proposition.reference())
                .map_err(|error| error.to_string())
        }
    }

    fn binary(&mut self, op: Op2, left: &str, right: &str) -> Result<PropId, String> {
        let left = self.materialize(parse_prop(left)?)?;
        let right = self.materialize(parse_prop(right)?)?;
        self.kernel
            .op2(op, left, right)
            .map(PropId::positive)
            .map_err(|error| error.to_string())
    }

    fn snapshot(&self, theorem: &str) -> Result<String, String> {
        let theorem = self
            .kernel
            .theorem(parse_thm(theorem)?)
            .map_err(|error| error.to_string())?;
        Ok(format!(
            "{{\"premises\":[{}],\"conclusions\":[{}]}}",
            json_props(theorem.premises()),
            json_props(theorem.conclusions())
        ))
    }

    fn rule0_prop(
        &mut self,
        proposition: &str,
        rule: fn(&mut Kernel, PropId) -> Result<ThmId, covalence_logic_hol::KernelError>,
    ) -> Result<String, JsError> {
        let proposition = parse_prop(proposition).map_err(to_js)?;
        rule(&mut self.kernel, proposition)
            .map(format_thm)
            .map_err(to_js)
    }

    fn rule1_prop(
        &mut self,
        theorem: &str,
        proposition: &str,
        rule: fn(&mut Kernel, ThmId, PropId) -> Result<ThmId, covalence_logic_hol::KernelError>,
    ) -> Result<String, JsError> {
        let theorem = parse_thm(theorem).map_err(to_js)?;
        let proposition = parse_prop(proposition).map_err(to_js)?;
        rule(&mut self.kernel, theorem, proposition)
            .map(format_thm)
            .map_err(to_js)
    }

    fn rule2_prop(
        &mut self,
        left: &str,
        right: &str,
        proposition: &str,
        rule: fn(
            &mut Kernel,
            ThmId,
            ThmId,
            PropId,
        ) -> Result<ThmId, covalence_logic_hol::KernelError>,
    ) -> Result<String, JsError> {
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

fn parse_prop(text: &str) -> Result<PropId, String> {
    let raw = text
        .parse::<i64>()
        .map_err(|_| "proposition ID must be a signed decimal i64".to_owned())?;
    PropId::from_raw(raw).map_err(|error| error.to_string())
}

fn parse_thm(text: &str) -> Result<ThmId, String> {
    let raw = parse_u64(text, "theorem ID")?;
    ThmId::new(raw).ok_or_else(|| "theorem IDs are one-based".to_owned())
}

fn parse_context(text: &str) -> Result<Vec<PropId>, String> {
    text.split_whitespace().map(parse_prop).collect()
}

fn parse_theorems(text: &str) -> Result<Vec<ThmId>, String> {
    text.split_whitespace().map(parse_thm).collect()
}

fn format_prop(proposition: PropId) -> String {
    proposition.get().to_string()
}

fn format_thm(theorem: ThmId) -> String {
    theorem.get().to_string()
}

fn json_props(propositions: &[PropId]) -> String {
    propositions
        .iter()
        .map(|proposition| format!("\"{}\"", proposition.get()))
        .collect::<Vec<_>>()
        .join(",")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn prover() -> HolProver {
        HolProver::try_new().unwrap()
    }

    #[test]
    fn lossless_signed_ids_and_canonical_contexts() {
        assert!(parse_prop("0").is_err());
        assert!(parse_prop(&i64::MIN.to_string()).is_err());
        assert!(parse_prop(&i64::MAX.to_string()).is_err());
        assert!(parse_thm("0").is_err());
        assert!(parse_thm("9007199254740993").is_ok());

        let mut prover = prover();
        let p = prover.proposition("18446744073709551615").unwrap();
        let q = prover.proposition("2").unwrap();
        let base = prover.kernel.identity(p).unwrap();
        let widened = prover.kernel.weaken(base, &[q, p, q], &[q, p]).unwrap();
        let snapshot = prover.snapshot(&format_thm(widened)).unwrap();
        assert_eq!(
            snapshot,
            format!(
                "{{\"premises\":[\"{}\",\"{}\"],\"conclusions\":[\"{}\",\"{}\"]}}",
                p.get().min(q.get()),
                p.get().max(q.get()),
                p.get().min(q.get()),
                p.get().max(q.get())
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

        assert!(prover.kernel.remove_theorems(&[first, first]).is_err());
        assert!(prover.kernel.theorem(first).is_ok());
        assert!(prover.kernel.theorem(second).is_ok());

        prover.kernel.remove_theorems(&[first, second]).unwrap();
        assert!(prover.kernel.theorem(first).is_err());
        assert!(prover.kernel.theorem(second).is_err());
        let reused_second = prover.kernel.identity(p).unwrap();
        let reused_first = prover.kernel.identity(q).unwrap();
        assert_eq!(reused_second, second);
        assert_eq!(reused_first, first);
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
        let conjunction = format_prop(prover.binary(Op2::And, &p_id, &q_id).unwrap());
        let disjunction = format_prop(prover.binary(Op2::Or, &p_id, &q_id).unwrap());
        let implication = format_prop(prover.binary(Op2::Imp, &p_id, &q_id).unwrap());

        assert!(prover.kernel.cut(theorem, theorem, q).is_err());
        assert!(prover.kernel.false_left(p).is_err());
        assert!(prover.kernel.true_right(p).is_err());
        assert!(prover.kernel.not_left(theorem, q).is_err());
        assert!(prover.kernel.not_right(theorem, q).is_err());
        assert!(
            prover
                .kernel
                .and_left(theorem, parse_prop(&conjunction).unwrap())
                .is_err()
        );
        assert!(
            prover
                .kernel
                .and_right(theorem, theorem, parse_prop(&conjunction).unwrap())
                .is_err()
        );
        assert!(
            prover
                .kernel
                .or_left(theorem, theorem, parse_prop(&disjunction).unwrap())
                .is_err()
        );
        assert!(
            prover
                .kernel
                .or_right(theorem, parse_prop(&disjunction).unwrap())
                .is_err()
        );
        assert!(
            prover
                .kernel
                .imp_left(theorem, theorem, parse_prop(&implication).unwrap())
                .is_err()
        );
        assert!(
            prover
                .kernel
                .imp_right(theorem, parse_prop(&implication).unwrap())
                .is_err()
        );
        assert!(prover.kernel.resolve(theorem, theorem, p).is_err());

        prover.kernel.remove_theorems(&[theorem]).unwrap();
        assert!(prover.snapshot(&theorem_id).is_err());
        assert!(prover.kernel.weaken(theorem, &[], &[]).is_err());
    }

    #[test]
    fn signed_operands_are_materialized_without_changing_meaning() {
        let mut prover = prover();
        let p = prover.proposition("1").unwrap();
        let not_p = p.negated();
        let conjunction = prover
            .binary(Op2::And, &format_prop(not_p), &format_prop(p))
            .unwrap();
        assert!(conjunction.is_positive());
        let children = prover
            .kernel
            .children(conjunction.reference())
            .unwrap()
            .collect::<Vec<_>>();
        assert_eq!(children.len(), 2);
        assert_eq!(prover.kernel.arena().op1(children[0]), Some(Op1::Not));
        assert_eq!(children[1], p.reference());
    }

    #[test]
    fn boundary_parsing_and_tree_operations_round_trip() {
        let mut prover = prover();
        let p = prover.proposition("1").unwrap();
        let q = prover.proposition("2").unwrap();
        let conjunction = prover
            .binary(Op2::And, &format_prop(p), &format_prop(q))
            .unwrap();
        let identity = prover.kernel.identity(conjunction).unwrap();

        let flattened = prover
            .kernel
            .flatten_premise(identity, conjunction)
            .unwrap();
        let flattened_json = prover.snapshot(&format_thm(flattened)).unwrap();
        assert!(flattened_json.contains(&format!("\"{}\"", p.get())));
        assert!(flattened_json.contains(&format!("\"{}\"", q.get())));

        let folded = prover.kernel.fold_premise(flattened, conjunction).unwrap();
        assert_eq!(
            prover.kernel.theorem(folded).unwrap().premises(),
            [conjunction]
        );
        assert_eq!(
            parse_context(&format!("{} {} {}", q.get(), p.get(), q.get())).unwrap(),
            [q, p, q]
        );
        assert!(parse_context("-1 nope").is_err());
    }
}
