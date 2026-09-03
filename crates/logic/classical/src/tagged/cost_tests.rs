//! Cost of validating, copying, and packing the tagged runtime arena.
//!
//! These are measurements, not regression gates. They exist so that a change
//! to the validator can be compared against the representation it replaced on
//! the same machine, in the same run, with the same shapes.
//!
//! Run with `cargo test --release -p covalence-logic-classical --test
//! tagged_cost -- --ignored --nocapture`.

use std::time::Instant;

use super::{Arena, Checked, Formula, Sequent, pack};

fn literal(atom: u32) -> Formula {
    Formula::Literal {
        atom,
        negative: false,
    }
}

/// A table of `count` unit sequents, the shape a theorem store holds.
fn unit_table(count: usize) -> Vec<Sequent> {
    (0..count)
        .map(|index| {
            let atom = u32::try_from(index).expect("test index fits") + 1;
            Sequent {
                premise: Formula::And {
                    negative: false,
                    children: vec![Formula::Or {
                        negative: false,
                        children: vec![literal(atom)],
                    }],
                },
                conclusion: Formula::Or {
                    negative: false,
                    children: vec![Formula::And {
                        negative: false,
                        children: vec![literal(atom)],
                    }],
                },
            }
        })
        .collect()
}

/// The shape one HOL theorem slot projects to: `rows` clauses of four literals.
fn projection(rows: usize) -> Sequent {
    let clause = |tag: u32| {
        (0..4)
            .map(|offset| literal(tag * 4 + offset + 1))
            .collect::<Vec<_>>()
    };
    let tags = || 0..u32::try_from(rows).expect("test row count fits");
    Sequent {
        premise: Formula::And {
            negative: false,
            children: tags()
                .map(|row| Formula::Or {
                    negative: false,
                    children: clause(row),
                })
                .collect(),
        },
        conclusion: Formula::Or {
            negative: false,
            children: tags()
                .map(|row| Formula::And {
                    negative: false,
                    children: clause(row),
                })
                .collect(),
        },
    }
}

fn median(mut samples: Vec<f64>) -> f64 {
    samples.sort_by(f64::total_cmp);
    samples[samples.len() / 2]
}

fn time_check(arena: &Arena, iterations: u32) -> f64 {
    let start = Instant::now();
    for _ in 0..iterations {
        let checked = Checked::check(arena.clone()).expect("valid arena");
        std::hint::black_box(&checked);
    }
    start.elapsed().as_secs_f64() * 1e6 / f64::from(iterations)
}

fn time_clone(arena: &Arena, iterations: u32) -> f64 {
    let start = Instant::now();
    for _ in 0..iterations {
        let copy = arena.clone();
        std::hint::black_box(&copy);
    }
    start.elapsed().as_secs_f64() * 1e6 / f64::from(iterations)
}

fn rounds(arena: &Arena, iterations: u32) -> (f64, f64) {
    time_check(arena, iterations.min(8));
    time_clone(arena, iterations.min(8));
    // Interleave the two arms round by round so machine drift lands on both.
    let mut checks = Vec::new();
    let mut clones = Vec::new();
    for _ in 0..7 {
        checks.push(time_check(arena, iterations));
        clones.push(time_clone(arena, iterations));
    }
    (median(checks), median(clones))
}

#[expect(clippy::cast_precision_loss, reason = "measurement report only")]
fn report(label: usize, arena: &Arena, iterations: u32) {
    let words = arena.words().len();
    let (check, clone) = rounds(arena, iterations);
    let net = check - clone;
    let per = net * 1e3 / words as f64;
    println!("{label:>10} {words:>10} {clone:>14.3} {check:>14.3} {net:>13.3} {per:>9.2}");
}

#[test]
#[ignore = "measurement, not a regression gate"]
fn validator_cost_versus_arena_size() {
    println!("  sequents      words       clone us       check us   check-clone   ns/word");
    for count in [16_usize, 64, 256, 512, 1024] {
        let checked = pack(&unit_table(count)).expect("packs");
        let iterations = if count >= 512 { 20 } else { 200 };
        report(count, checked.arena(), iterations);
    }
}

#[test]
#[ignore = "measurement, not a regression gate"]
fn validator_cost_on_the_hol_projection_shape() {
    println!("      rows      words       clone us       check us   check-clone   ns/word");
    for rows in [4_usize, 16, 64, 256, 1024] {
        let checked = pack(std::slice::from_ref(&projection(rows))).expect("packs");
        let iterations = if rows >= 256 { 20 } else { 200 };
        report(rows, checked.arena(), iterations);
    }
}

#[test]
#[ignore = "measurement, not a regression gate"]
fn pack_cost_on_one_small_slot() {
    let sequent = projection(1);
    let table = std::slice::from_ref(&sequent);
    for _ in 0..1_000 {
        std::hint::black_box(pack(table).expect("packs"));
    }
    let per = median(
        (0..7)
            .map(|_| {
                let start = Instant::now();
                for _ in 0..20_000 {
                    std::hint::black_box(pack(table).expect("packs"));
                }
                start.elapsed().as_secs_f64() * 1e6 / 20_000.0
            })
            .collect(),
    );
    println!("one-slot pack: {per:.4} us");
}
