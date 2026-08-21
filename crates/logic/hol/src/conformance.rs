//! Runner for the shared empty/Boolean contract traces.

use serde_json::{Value, json};

use super::{Entry, Kernel, TmRepr, TyRepr};

const TRACES: &str = include_str!("../../../../theories/ethane/conformance/traces.json");

fn rows(arena: &Value) -> Result<&Vec<Value>, String> {
    arena
        .get("rows")
        .and_then(Value::as_array)
        .ok_or_else(|| "arena.rows must be an array".to_owned())
}

fn checked_arena(normalized: &Value) -> Result<Kernel, String> {
    let assumptions = normalized
        .get("assumptions")
        .and_then(Value::as_array)
        .ok_or_else(|| "arena.assumptions must be an array".to_owned())?;
    if !assumptions.is_empty() {
        return Err("the current Rust slice cannot reconstruct facts".to_owned());
    }

    rows(normalized)?
        .iter()
        .try_fold(Kernel::empty(), |kernel, row| {
            match row.get("tag").and_then(Value::as_str) {
                Some("boolTy") => kernel
                    .bool_ty()
                    .map(|(next, _)| next)
                    .map_err(|error| error.to_string()),
                Some("bool") => {
                    let value = row
                        .get("value")
                        .and_then(Value::as_bool)
                        .ok_or_else(|| "bool row must contain a Boolean value".to_owned())?;
                    kernel
                        .bool_const(value)
                        .map(|(next, _)| next)
                        .map_err(|error| error.to_string())
                }
                Some(tag) => Err(format!("unsupported row tag: {tag}")),
                None => Err("row.tag must be a string".to_owned()),
            }
        })
}

fn normalized_arena(kernel: &Kernel) -> Result<Value, String> {
    let rows = kernel
        .arena
        .entries
        .iter()
        .map(|entry| match entry {
            Entry::Type(ty) => match ty.0 {
                TyRepr::Bool => Ok(json!({ "tag": "boolTy" })),
            },
            Entry::Term(term) => match term.0 {
                TmRepr::Bool(value) => Ok(json!({ "tag": "bool", "value": value })),
            },
            Entry::Fact(_) => Err("fact rows are outside the current trace slice".to_owned()),
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(json!({ "rows": rows, "assumptions": [] }))
}

fn sole_old_arena(trace: &Value) -> Result<Kernel, String> {
    let old = trace
        .get("oldArenas")
        .and_then(Value::as_array)
        .ok_or_else(|| "trace.oldArenas must be an array".to_owned())?;
    let [arena] = old.as_slice() else {
        return Err("transition trace must have exactly one old arena".to_owned());
    };
    checked_arena(arena)
}

fn run(trace: &Value) -> Result<Value, String> {
    let operation = trace
        .get("operation")
        .and_then(Value::as_str)
        .ok_or_else(|| "trace.operation must be a string".to_owned())?;

    let (kernel, output) = match operation {
        "kernel.empty" => {
            let old = trace
                .get("oldArenas")
                .and_then(Value::as_array)
                .ok_or_else(|| "trace.oldArenas must be an array".to_owned())?;
            if !old.is_empty() {
                return Err("empty constructor cannot have an old arena".to_owned());
            }
            (Kernel::empty(), json!({}))
        }
        "type.bool" => {
            let old = sole_old_arena(trace)?;
            let output_ref = old.arena().len();
            let (next, _) = old.bool_ty().map_err(|error| error.to_string())?;
            (next, json!({ "ref": output_ref, "class": "type" }))
        }
        "term.bool" => {
            let old = sole_old_arena(trace)?;
            let value = trace
                .get("input")
                .and_then(|input| input.get("value"))
                .and_then(Value::as_bool)
                .ok_or_else(|| "term.bool input.value must be Boolean".to_owned())?;
            let output_ref = old.arena().len();
            let (next, _) = old.bool_const(value).map_err(|error| error.to_string())?;
            (next, json!({ "ref": output_ref, "class": "term" }))
        }
        operation => return Err(format!("unsupported operation: {operation}")),
    };

    Ok(json!({
        "result": "ok",
        "newArena": normalized_arena(&kernel)?,
        "output": output,
    }))
}

#[test]
fn rust_matches_shared_empty_and_boolean_traces() {
    let document: Value = serde_json::from_str(TRACES).expect("shared traces must be JSON");
    assert_eq!(
        document.get("format").and_then(Value::as_str),
        Some("nucleus.ethane.kernel-traces.v0")
    );

    let traces = document
        .get("traces")
        .and_then(Value::as_array)
        .expect("shared traces must contain an array");
    assert!(!traces.is_empty(), "shared trace set must not be empty");
    for trace in traces {
        let id = trace
            .get("id")
            .and_then(Value::as_str)
            .expect("trace id must be a string");
        let actual = run(trace).unwrap_or_else(|error| panic!("trace {id}: {error}"));
        assert_eq!(actual, trace["expected"], "trace {id}");
    }
}
