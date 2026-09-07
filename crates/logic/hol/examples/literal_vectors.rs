//! Regenerate with `cargo run -p covalence-logic-hol --example literal_vectors`.

#[path = "../tests/support/literal_vectors.rs"]
mod fixtures;

fn main() {
    println!(
        "{}",
        covalence_lib_json::to_string_pretty(&fixtures::vectors()).unwrap()
    );
}
