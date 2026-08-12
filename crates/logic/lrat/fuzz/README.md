# LRAT fuzzing

```sh
cargo fuzz run --manifest-path crates/logic/lrat/fuzz/Cargo.toml binary_lrat -- -max_total_time=30
```

The smoke target bounds bytes, decoded terms, live clauses, and checker work.
Fuzzing and shared traces are implementation evidence complementary to—not a
replacement for—the Lean soundness development.
