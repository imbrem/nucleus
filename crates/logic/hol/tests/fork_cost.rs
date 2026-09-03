//! Cost of the transactional arena copy that every kernel rule stages.
//!
//! Each checked rule stages `arena: self.arena.clone()` and commits only on
//! success, so the price of a rule is bounded below by the price of copying
//! the whole arena. These measurements separate the two things that grow:
//! dense syntax rows and classical theorem slots.
//!
//! Run with `cargo test --release -p covalence-logic-hol --test fork_cost
//! -- --ignored --nocapture`.

mod support;

use std::time::Instant;

use covalence_logic_hol::{Kernel, Ref};
use support::Fix;

struct Shape {
    kernel: Kernel,
    bool_ty: Ref,
    term: Ref,
}

/// Builds a kernel with `rows` extra syntax rows and `theorems` extra theorems.
fn build(rows: u64, theorems: u64) -> Shape {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let term = fix.var(0);
    for name in 1..=rows {
        fix.var(name);
    }
    for _ in 0..theorems {
        fix.kernel.refl(bool_ty, term).expect("reflexivity");
    }
    Shape {
        kernel: fix.kernel,
        bool_ty,
        term,
    }
}

/// Median of several timing rounds, which rejects allocator and scheduler
/// outliers that a single round reports as signal.
fn median(mut samples: Vec<f64>) -> f64 {
    samples.sort_by(f64::total_cmp);
    samples[samples.len() / 2]
}

fn time_fork(kernel: &Kernel, iterations: u32) -> f64 {
    let start = Instant::now();
    for _ in 0..iterations {
        let fork = kernel.fork();
        std::hint::black_box(&fork);
    }
    start.elapsed().as_secs_f64() * 1e6 / f64::from(iterations)
}

fn time_refl(shape: &Shape, iterations: u32) -> f64 {
    let start = Instant::now();
    for _ in 0..iterations {
        let mut fork = shape.kernel.fork();
        let theorem = fork.refl(shape.bool_ty, shape.term).expect("reflexivity");
        std::hint::black_box(&theorem);
    }
    start.elapsed().as_secs_f64() * 1e6 / f64::from(iterations)
}

/// A synthetic proof of the shape a normalizer evaluation drives: a chain of
/// rules applied in sequence to a kernel that already holds `resident`
/// theorems. Returns microseconds for the whole chain.
fn time_proof(shape: &Shape, steps: u32) -> f64 {
    let start = Instant::now();
    let mut kernel = shape.kernel.fork();
    for _ in 0..steps {
        let theorem = kernel.refl(shape.bool_ty, shape.term).expect("reflexivity");
        std::hint::black_box(&theorem);
    }
    std::hint::black_box(&kernel);
    start.elapsed().as_secs_f64() * 1e6
}

#[test]
#[ignore = "measurement, not a regression gate"]
fn arena_copy_cost_grows_with_rows_and_theorems() {
    println!("       rows      thms     fork us   fork+refl us");
    for (rows, theorems) in [
        (0, 0),
        (2_000, 0),
        (4_000, 0),
        (8_200, 0),
        (0, 500),
        (0, 1_100),
        (0, 2_200),
        (8_200, 2_200),
    ] {
        let shape = build(rows, theorems);
        // Warm the allocator and the branch predictors before measuring.
        time_fork(&shape.kernel, 200);
        let fork = median((0..5).map(|_| time_fork(&shape.kernel, 2_000)).collect());
        time_refl(&shape, 100);
        let refl = median((0..5).map(|_| time_refl(&shape, 1_000)).collect());
        println!("{rows:>11} {theorems:>9} {fork:>11.3} {refl:>14.3}");
    }
}

#[test]
#[ignore = "measurement, not a regression gate"]
fn a_synthetic_proof_costs_one_arena_copy_per_step() {
    println!("   resident     steps    total us      us/step");
    for resident in [0, 500, 1_100, 2_200] {
        let steps = 200;
        let shape = build(0, resident);
        time_proof(&shape, 20);
        let total = median((0..5).map(|_| time_proof(&shape, steps)).collect());
        let per = total / f64::from(steps);
        println!("{resident:>11} {steps:>9} {total:>11.1} {per:>12.3}");
    }
}
