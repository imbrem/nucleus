//! Cost of copying classical checked-syntax storage.
//!
//! HOL stages a full arena copy for every kernel rule, and three
//! [`ClassicalArena`] stores ride along in that copy. This isolates the price
//! of one theorem slot from the syntax rows that a HOL rule also allocates.
//!
//! Run with `cargo test --release -p covalence-logic-classical --test
//! slot_copy_cost -- --ignored --nocapture`.

use std::time::Instant;

use covalence_logic_classical::{ClassicalArena, Lit, LitVec, Matrix};

/// Builds an arena of `theorems` slots, each a `width`-row sequent.
fn build(theorems: u32, width: u32) -> ClassicalArena {
    let mut arena = ClassicalArena::new();
    for theorem in 0..theorems {
        let rows = |offset: u32| -> Vec<LitVec> {
            (0..width)
                .map(|row| {
                    let name = i32::try_from(theorem % 64 + row + offset).expect("small literal");
                    LitVec::from_slice(&[Lit::positive(name + 1)])
                })
                .collect()
        };
        arena
            .insert(Matrix::new(rows(0)), Matrix::new(rows(1)))
            .expect("insert");
    }
    arena
}

/// Median of several rounds, which rejects allocator and scheduler outliers.
fn median(mut samples: Vec<f64>) -> f64 {
    samples.sort_by(f64::total_cmp);
    samples[samples.len() / 2]
}

fn time_clone(arena: &ClassicalArena, iterations: u32) -> f64 {
    let start = Instant::now();
    for _ in 0..iterations {
        let copy = arena.clone();
        std::hint::black_box(&copy);
    }
    start.elapsed().as_secs_f64() * 1e6 / f64::from(iterations)
}

#[test]
#[ignore = "measurement, not a regression gate"]
fn copying_theorem_storage_scales_with_resident_slots() {
    println!("       thms     width    copy us      ns/slot");
    for (theorems, width) in [(500, 1), (1_100, 1), (2_200, 1), (2_200, 4), (2_200, 16)] {
        let arena = build(theorems, width);
        time_clone(&arena, 50);
        let copy = median((0..5).map(|_| time_clone(&arena, 500)).collect());
        let per = copy * 1_000.0 / f64::from(theorems);
        println!("{theorems:>11} {width:>9} {copy:>10.3} {per:>12.1}");
    }
}
