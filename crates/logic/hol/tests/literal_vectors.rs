//! Keep the complete Rust/Lean inventory in ordinary Cargo and Buck test runs.

#[path = "support/literal_vectors.rs"]
mod fixtures;

#[test]
fn shared_fixture_matches_checked_builtin_inventory() {
    let expected: Vec<covalence_lib_json::Value> =
        covalence_lib_json::from_str(include_str!("../literal-vectors.json")).unwrap();
    assert_eq!(fixtures::vectors(), expected);
}
