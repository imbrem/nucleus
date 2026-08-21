//! Runner for the shared empty/Boolean contract traces.

use serde_json::{Value, json};

use super::{Row, dense};

const TRACES: &str = include_str!("../fixtures/traces.json");

#[test]
fn cargo_fixture_matches_the_shared_contract_bytes() {
    let shared = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../theories/ethane/conformance/traces.json");
    if shared.is_file() {
        let shared = std::fs::read_to_string(shared).expect("read shared contract traces");
        assert_eq!(TRACES, shared, "crate fixture drifted from shared contract");
    }
}

fn rows(arena: &Value) -> Result<&Vec<Value>, String> {
    arena
        .get("rows")
        .and_then(Value::as_array)
        .ok_or_else(|| "arena.rows must be an array".to_owned())
}

fn checked_arena(normalized: &Value) -> Result<dense::Kernel, String> {
    let assumptions = normalized
        .get("assumptions")
        .and_then(Value::as_array)
        .ok_or_else(|| "arena.assumptions must be an array".to_owned())?;
    if !assumptions.is_empty() {
        return Err("the current Rust slice cannot reconstruct facts".to_owned());
    }

    let mut kernel = dense::Kernel::empty();
    for row in rows(normalized)? {
        match row.get("tag").and_then(Value::as_str) {
            Some("kindStar") => {
                kernel.star().map_err(|error| error.to_string())?;
            }
            Some("boolTy") => {
                kernel.bool_ty().map_err(|error| error.to_string())?;
            }
            Some("bool") => {
                let value = row
                    .get("value")
                    .and_then(Value::as_bool)
                    .ok_or_else(|| "bool row must contain a Boolean value".to_owned())?;
                kernel
                    .bool_const(value)
                    .map_err(|error| error.to_string())?;
            }
            Some(tag) => return Err(format!("unsupported row tag: {tag}")),
            None => return Err("row.tag must be a string".to_owned()),
        }
    }
    Ok(kernel)
}

fn normalized_arena(kernel: &dense::Kernel) -> Value {
    let rows = kernel
        .arena()
        .rows()
        .iter()
        .map(|row| match row {
            Row::KindStar => json!({ "tag": "kindStar" }),
            Row::BoolTy => json!({ "tag": "boolTy" }),
            Row::Bool(value) => json!({ "tag": "bool", "value": value }),
        })
        .collect::<Vec<_>>();
    json!({ "rows": rows, "assumptions": [] })
}

fn sole_old_arena(trace: &Value) -> Result<dense::Kernel, String> {
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
            (dense::Kernel::empty(), json!({}))
        }
        "type.bool" => {
            let mut kernel = sole_old_arena(trace)?;
            let output = kernel.bool_ty().map_err(|error| error.to_string())?;
            let output_ref = usize::try_from(output.index())
                .map_err(|_| "negative output reference".to_owned())?;
            (kernel, json!({ "ref": output_ref, "class": "type" }))
        }
        "term.bool" => {
            let mut kernel = sole_old_arena(trace)?;
            let value = trace
                .get("input")
                .and_then(|input| input.get("value"))
                .and_then(Value::as_bool)
                .ok_or_else(|| "term.bool input.value must be Boolean".to_owned())?;
            let output = kernel
                .bool_const(value)
                .map_err(|error| error.to_string())?;
            let output_ref = usize::try_from(output.index())
                .map_err(|_| "negative output reference".to_owned())?;
            (kernel, json!({ "ref": output_ref, "class": "term" }))
        }
        operation => return Err(format!("unsupported operation: {operation}")),
    };

    Ok(json!({
        "result": "ok",
        "newArena": normalized_arena(&kernel),
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
