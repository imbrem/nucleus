//! Shared operation traces exercised through the public kernel API.

use covalence_logic_hol::dense;
use serde_json::Value;

const TRACES: &str = include_str!("../fixtures/traces.json");

fn replay(rows: &[Value]) -> dense::Kernel {
    let mut kernel = dense::Kernel::empty();
    for row in rows {
        match row["tag"].as_str().expect("row tag") {
            "kind.star" => {
                kernel.star().expect("replay Star");
            }
            "ty.bool" => {
                kernel.bool_ty().expect("replay BoolTy");
            }
            "tm.bool.false" | "tm.bool.true" => {
                kernel
                    .bool_const(row["tag"] == "tm.bool.true")
                    .expect("replay Boolean");
            }
            tag => panic!("unsupported fixture row: {tag}"),
        }
    }
    kernel
}

#[test]
fn public_kernel_matches_shared_traces() {
    let document: Value = serde_json::from_str(TRACES).expect("valid trace JSON");
    for trace in document["traces"].as_array().expect("trace array") {
        let operation = trace["operation"].as_str().expect("operation");
        let expected = &trace["expected"];
        let old_rows: &[Value] = trace["oldArenas"]
            .as_array()
            .and_then(|arenas| arenas.first())
            .map_or(&[], |arena| {
                arena["rows"].as_array().expect("rows").as_slice()
            });
        let mut kernel = replay(old_rows);

        let output_index = match operation {
            "kernel.empty" => None,
            "kind.star" => Some(kernel.star().expect("Star").index()),
            "type.bool" => Some(kernel.bool_ty().expect("BoolTy").index()),
            "term.bool" => Some(
                kernel
                    .bool_const(trace["input"]["value"].as_bool().expect("value"))
                    .expect("Boolean")
                    .index(),
            ),
            other => panic!("unsupported operation: {other}"),
        };

        if let Some(index) = output_index {
            assert_eq!(index, expected["output"]["ref"].as_i64().unwrap());
        }
        assert_eq!(
            kernel.arena().len(),
            expected["newArena"]["rows"].as_array().unwrap().len()
        );
    }
}

#[test]
fn serde_wire_round_trips_the_public_dense_representation() {
    let mut kernel = dense::Kernel::empty();
    kernel.star().unwrap();
    kernel.bool_ty().unwrap();
    kernel.bool_const(true).unwrap();

    let mut encoded = Vec::new();
    covalence_logic_hol::wire::serialize(kernel.arena(), &mut encoded).unwrap();
    let decoded = covalence_logic_hol::wire::deserialize(encoded.as_slice()).unwrap();
    assert_eq!(&decoded, kernel.arena());
}
