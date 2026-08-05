//! Authority-free direct core-Wasm guest for the browser plan spike.
//!
//! The imported object is supplied by the browser kernel's wasm-bindgen
//! module. Its integer results are forgeable recipe offsets, not theorem or
//! database handles. The kernel independently seals, decodes, and replays the
//! completed recipe before signing anything.

use wasm_bindgen::prelude::*;

#[wasm_bindgen]
extern "C" {
    pub type WebHolProofPlan;

    #[wasm_bindgen(method, catch)]
    fn bool_type(this: &WebHolProofPlan) -> Result<u32, JsValue>;

    #[wasm_bindgen(method, catch)]
    fn bound_term(this: &WebHolProofPlan, index: u32, ty: u32) -> Result<u32, JsValue>;

    #[wasm_bindgen(method, catch)]
    fn lambda(this: &WebHolProofPlan, parameter_type: u32, body: u32) -> Result<u32, JsValue>;

    #[wasm_bindgen(method, catch)]
    fn bool_term(this: &WebHolProofPlan, value: bool) -> Result<u32, JsValue>;

    #[wasm_bindgen(method, catch)]
    fn empty_context(this: &WebHolProofPlan) -> Result<u32, JsValue>;

    #[wasm_bindgen(method, catch)]
    fn conversion_beta(
        this: &WebHolProofPlan,
        abstraction: u32,
        argument: u32,
    ) -> Result<u32, JsValue>;

    #[wasm_bindgen(method, catch)]
    fn prove_conversion_equality(
        this: &WebHolProofPlan,
        context: u32,
        conversion: u32,
    ) -> Result<u32, JsValue>;

    #[wasm_bindgen(method, catch)]
    fn persist_theorem(this: &WebHolProofPlan, theorem: u32) -> Result<(), JsValue>;

    #[wasm_bindgen(method, catch)]
    fn root_child_namespace(this: &WebHolProofPlan, name: Option<String>) -> Result<u32, JsValue>;

    #[wasm_bindgen(method, catch)]
    fn export_context(
        this: &WebHolProofPlan,
        namespace: u32,
        export_id: i64,
        context: u32,
        name: Option<String>,
    ) -> Result<(), JsValue>;

    #[wasm_bindgen(method, catch)]
    fn export_theorem_conclusion(
        this: &WebHolProofPlan,
        namespace: u32,
        export_id: i64,
        theorem: u32,
        name: Option<String>,
    ) -> Result<(), JsValue>;
}

/// Appends the same closed-beta recipe as the Component Model fixture.
///
/// The caller owns the plan and must seal it with the returned namespace.
///
/// # Errors
///
/// Returns a JavaScript exception from the host collector if any append is
/// rejected by its resource or name bounds.
#[wasm_bindgen]
pub fn build(plan: &WebHolProofPlan) -> Result<u32, JsValue> {
    let bool_type = plan.bool_type()?;
    let bound = plan.bound_term(0, bool_type)?;
    let identity = plan.lambda(bool_type, bound)?;
    let truth = plan.bool_term(true)?;
    let context = plan.empty_context()?;
    let conversion = plan.conversion_beta(identity, truth)?;
    let theorem = plan.prove_conversion_equality(context, conversion)?;
    plan.persist_theorem(theorem)?;
    let namespace = plan.root_child_namespace(Some("demo".into()))?;
    plan.export_context(namespace, 0, context, Some("empty_context".into()))?;
    plan.export_theorem_conclusion(namespace, 1, theorem, Some("identity_true_beta".into()))?;
    Ok(namespace)
}
