//! An instruction-driven mini-LCF kernel for LRAT.
//!
//! The trusted surface is [`LratKernel`]: a clause store whose only way to
//! grow is the RUP-checked [`LratKernel::learn`] rule, exactly in the LCF
//! discipline — big-step, but a kernel like any other. Everything else is
//! untrusted driving: the ASCII and binary parsers produce [`LratInstr`]
//! streams, and a mangled file can only mis-drive the kernel into a
//! rejection, never into a false refutation, because every clause the
//! kernel checks against is either an initial clause supplied by the
//! caller (read from prop-kernel rows) or one it previously checked
//! itself.
//!
//! For the zero-added-TCB alternative, the same instruction stream can
//! drive small-step replay through the propositional rules in a scratch
//! table (`prop::scratch`); this module's kernel is the fast path.

use std::collections::{BTreeMap, BTreeSet};

/// One LRAT instruction.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LratInstr {
    /// Learn `clause` under `id`, justified by unit propagation over the
    /// clauses named in `hints` (in order, ending in a conflict).
    Learn {
        /// The new clause's identifier.
        id: u64,
        /// The clause's literals; empty is the refutation.
        clause: Vec<i64>,
        /// Propagation hints, in order; a negative hint opens a RAT
        /// group for the named clause.
        hints: Vec<i64>,
    },
    /// Forget the named clauses.
    Forget {
        /// The forgotten clause identifiers.
        ids: Vec<u64>,
    },
}

/// A failure while parsing a proof or applying an instruction.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LratError {
    /// The proof bytes are not well-formed LRAT.
    Parse {
        /// The offending line (ASCII) or byte offset (binary).
        at: usize,
    },
    /// A hint names a clause that is not live.
    UnknownClause {
        /// The instruction being applied.
        step: u64,
        /// The missing clause id.
        clause: u64,
    },
    /// A hint clause neither propagates nor conflicts.
    UselessHint {
        /// The instruction being applied.
        step: u64,
        /// The offending hint.
        clause: u64,
    },
    /// The hint list ended without reaching a conflict.
    NoConflict {
        /// The instruction being applied.
        step: u64,
    },
    /// A RAT step does not cover every clause containing the negated
    /// pivot.
    IncompleteRat {
        /// The instruction being applied.
        step: u64,
        /// A clause containing the negated pivot with no group.
        clause: u64,
    },
    /// A RAT step was encountered where only RUP is permitted.
    RatUnsupported {
        /// The instruction being applied.
        step: u64,
    },
    /// The instruction stream ended without deriving the empty clause.
    NoRefutation,
}

/// The mini-LCF clause kernel.
///
/// Clauses enter only through [`Self::new`] (the caller-vouched initial
/// clauses) and the checked [`Self::learn`]; [`Self::refuted`] reports
/// whether the empty clause has been established.
pub struct LratKernel {
    live: BTreeMap<u64, Vec<i64>>,
    refuted: bool,
}

impl LratKernel {
    /// Opens a kernel over the initial clauses, numbered `1..=n` in order.
    #[must_use]
    pub fn new(initial: &[Vec<i64>]) -> Self {
        Self {
            live: initial
                .iter()
                .enumerate()
                .map(|(index, clause)| (index as u64 + 1, clause.clone()))
                .collect(),
            refuted: false,
        }
    }

    /// The `learn` rule: admits `clause` iff its negation propagates to
    /// a conflict through the hinted clauses (RUP), or — when the hints
    /// contain RAT groups — every resolvent on the pivot (the clause's
    /// first literal) does. RAT additions preserve satisfiability rather
    /// than equivalence, which suffices for the kernel's only judgement,
    /// unsatisfiability of the initial clauses.
    ///
    /// # Errors
    ///
    /// Fails without changing kernel state when the hints do not certify
    /// the clause.
    pub fn learn(&mut self, id: u64, clause: &[i64], hints: &[i64]) -> Result<(), LratError> {
        let split = hints
            .iter()
            .position(|hint| *hint < 0)
            .unwrap_or(hints.len());
        let (rup_hints, rat_hints) = hints.split_at(split);
        let mut assigned: BTreeSet<i64> = clause.iter().map(|literal| -literal).collect();
        if !self.propagate(id, &mut assigned, rup_hints)? {
            if clause.is_empty() {
                return Err(LratError::NoConflict { step: id });
            }
            self.rat(id, clause, &assigned, rat_hints)?;
        }
        if clause.is_empty() {
            self.refuted = true;
        }
        self.live.insert(id, clause.to_vec());
        Ok(())
    }

    /// Checks the RAT groups against the propagated assignment: every
    /// live clause containing the negated pivot (the clause's first
    /// literal) must resolve to a conflict, either tautologically or
    /// through its group's propagation hints.
    fn rat(
        &self,
        id: u64,
        clause: &[i64],
        assigned: &BTreeSet<i64>,
        rat_hints: &[i64],
    ) -> Result<(), LratError> {
        let pivot = *clause.first().ok_or(LratError::NoConflict { step: id })?;
        let mut groups: Vec<(u64, Vec<i64>)> = Vec::new();
        for hint in rat_hints {
            if *hint < 0 {
                let key = u64::try_from(-hint).map_err(|_| LratError::NoConflict { step: id })?;
                groups.push((key, Vec::new()));
            } else if let Some(group) = groups.last_mut() {
                group.1.push(*hint);
            } else {
                return Err(LratError::NoConflict { step: id });
            }
        }
        let covered: BTreeSet<u64> = groups.iter().map(|(key, _)| *key).collect();
        for (other_id, other) in &self.live {
            if other.contains(&-pivot) && !covered.contains(other_id) {
                return Err(LratError::IncompleteRat {
                    step: id,
                    clause: *other_id,
                });
            }
        }
        for (key, group_hints) in &groups {
            let other = self.live.get(key).ok_or(LratError::UnknownClause {
                step: id,
                clause: *key,
            })?;
            if !other.contains(&-pivot) {
                continue;
            }
            // Resolvent assignment: extend the propagated assignment
            // with the negation of the other clause minus the resolved
            // literal. A contradictory extension is an immediate
            // (tautological) conflict.
            let mut assignment = assigned.clone();
            let mut contradictory = false;
            for literal in other {
                if *literal != -pivot {
                    if assignment.contains(literal) {
                        contradictory = true;
                        break;
                    }
                    assignment.insert(-literal);
                }
            }
            if contradictory {
                continue;
            }
            if !self.propagate(id, &mut assignment, group_hints)? {
                return Err(LratError::NoConflict { step: id });
            }
        }
        Ok(())
    }

    /// Unit-propagates through hinted clauses, extending `assigned`;
    /// returns whether a conflict was reached.
    fn propagate(
        &self,
        id: u64,
        assigned: &mut BTreeSet<i64>,
        hints: &[i64],
    ) -> Result<bool, LratError> {
        for hint in hints {
            let key = u64::try_from(*hint).map_err(|_| LratError::NoConflict { step: id })?;
            let hinted = self.live.get(&key).ok_or(LratError::UnknownClause {
                step: id,
                clause: key,
            })?;
            if hinted.iter().any(|literal| assigned.contains(literal)) {
                return Err(LratError::UselessHint {
                    step: id,
                    clause: key,
                });
            }
            let mut unassigned = hinted
                .iter()
                .filter(|literal| !assigned.contains(&-**literal));
            match (unassigned.next(), unassigned.next()) {
                (None, _) => return Ok(true),
                (Some(unit), None) => {
                    assigned.insert(*unit);
                }
                (Some(_), Some(_)) => {
                    return Err(LratError::UselessHint {
                        step: id,
                        clause: key,
                    });
                }
            }
        }
        Ok(false)
    }

    /// The `forget` rule: dropping clauses only ever weakens the kernel.
    pub fn forget(&mut self, ids: &[u64]) {
        for id in ids {
            self.live.remove(id);
        }
    }

    /// Whether the empty clause has been established.
    #[must_use]
    pub const fn refuted(&self) -> bool {
        self.refuted
    }

    /// Applies one instruction.
    ///
    /// # Errors
    ///
    /// Fails when a `Learn` instruction is not certified by its hints.
    pub fn apply(&mut self, instruction: &LratInstr) -> Result<(), LratError> {
        match instruction {
            LratInstr::Learn { id, clause, hints } => self.learn(*id, clause, hints),
            LratInstr::Forget { ids } => {
                self.forget(ids);
                Ok(())
            }
        }
    }
}

/// Drives a fresh kernel through an instruction stream and demands a
/// refutation.
///
/// # Errors
///
/// Fails on the first uncertified instruction, or if the stream ends
/// without deriving the empty clause.
pub fn check(initial: &[Vec<i64>], instructions: &[LratInstr]) -> Result<(), LratError> {
    let mut kernel = LratKernel::new(initial);
    for instruction in instructions {
        kernel.apply(instruction)?;
        if kernel.refuted() {
            return Ok(());
        }
    }
    Err(LratError::NoRefutation)
}

/// Parses a proof, auto-detecting the binary format by its marker bytes.
///
/// # Errors
///
/// Fails on malformed input; parsing is untrusted, so a parse bug can
/// only mis-drive the kernel into rejection.
pub fn parse(bytes: &[u8]) -> Result<Vec<LratInstr>, LratError> {
    if bytes
        .first()
        .is_some_and(|byte| *byte == b'a' || *byte == b'd')
    {
        parse_binary(bytes)
    } else {
        parse_text(std::str::from_utf8(bytes).map_err(|_| LratError::Parse { at: 0 })?)
    }
}

/// Parses the ASCII LRAT format.
///
/// # Errors
///
/// Fails on any line that is not an addition or deletion step.
pub fn parse_text(text: &str) -> Result<Vec<LratInstr>, LratError> {
    let mut instructions = Vec::new();
    for (index, raw_line) in text.lines().enumerate() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        let parse_error = LratError::Parse { at: index + 1 };
        let mut tokens = line.split_ascii_whitespace();
        let id: u64 = tokens
            .next()
            .and_then(|token| token.parse().ok())
            .ok_or(parse_error.clone())?;
        let rest: Vec<&str> = tokens.collect();
        if rest.first() == Some(&"d") {
            let mut ids = Vec::new();
            for token in &rest[1..] {
                let value: u64 = token.parse().map_err(|_| parse_error.clone())?;
                if value == 0 {
                    break;
                }
                ids.push(value);
            }
            if rest.last() != Some(&"0") {
                return Err(parse_error);
            }
            instructions.push(LratInstr::Forget { ids });
            continue;
        }
        let mut clause = Vec::new();
        let mut hints = Vec::new();
        let mut in_hints = false;
        let mut terminated = false;
        for token in &rest {
            let value: i64 = token.parse().map_err(|_| parse_error.clone())?;
            if value == 0 {
                if in_hints {
                    terminated = true;
                    break;
                }
                in_hints = true;
            } else if in_hints {
                hints.push(value);
            } else {
                clause.push(value);
            }
        }
        if !terminated {
            return Err(parse_error);
        }
        instructions.push(LratInstr::Learn { id, clause, hints });
    }
    Ok(instructions)
}

/// Parses the binary LRAT format (`CaDiCaL`'s default).
///
/// Steps are marked `a`/`d`; every number is a variable-length integer
/// (7 data bits per byte, high bit continues) carrying the signed mapping
/// `2|n| + sign`, with `0x00` terminating each section.
///
/// # Errors
///
/// Fails on truncated or malformed input.
pub fn parse_binary(bytes: &[u8]) -> Result<Vec<LratInstr>, LratError> {
    let mut instructions = Vec::new();
    let mut position = 0_usize;
    while position < bytes.len() {
        let marker = bytes[position];
        position += 1;
        match marker {
            b'a' => {
                let id = read_unsigned(bytes, &mut position)?;
                let mut clause = Vec::new();
                loop {
                    let value = read_signed(bytes, &mut position)?;
                    if value == 0 {
                        break;
                    }
                    clause.push(value);
                }
                let mut hints = Vec::new();
                loop {
                    let value = read_signed(bytes, &mut position)?;
                    if value == 0 {
                        break;
                    }
                    hints.push(value);
                }
                instructions.push(LratInstr::Learn { id, clause, hints });
            }
            b'd' => {
                let mut ids = Vec::new();
                loop {
                    let value = read_signed(bytes, &mut position)?;
                    if value == 0 {
                        break;
                    }
                    let id = u64::try_from(value).map_err(|_| LratError::Parse { at: position })?;
                    ids.push(id);
                }
                instructions.push(LratInstr::Forget { ids });
            }
            _ => return Err(LratError::Parse { at: position - 1 }),
        }
    }
    Ok(instructions)
}

/// Reads one MSB-continuation varint.
fn read_varint(bytes: &[u8], position: &mut usize) -> Result<u64, LratError> {
    let mut value = 0_u64;
    let mut shift = 0_u32;
    loop {
        let byte = *bytes
            .get(*position)
            .ok_or(LratError::Parse { at: *position })?;
        *position += 1;
        if shift >= 63 {
            return Err(LratError::Parse { at: *position });
        }
        value |= u64::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            return Ok(value);
        }
        shift += 7;
    }
}

/// Reads a number in the signed mapping and demands it be non-negative.
fn read_unsigned(bytes: &[u8], position: &mut usize) -> Result<u64, LratError> {
    let value = read_signed(bytes, position)?;
    u64::try_from(value).map_err(|_| LratError::Parse { at: *position })
}

/// Reads a number in the signed mapping `2|n| + sign`.
fn read_signed(bytes: &[u8], position: &mut usize) -> Result<i64, LratError> {
    let raw = read_varint(bytes, position)?;
    let magnitude = i64::try_from(raw >> 1).map_err(|_| LratError::Parse { at: *position })?;
    Ok(if raw & 1 == 1 { -magnitude } else { magnitude })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_additions_and_deletions() {
        let instructions = parse_text("3 1 -2 0 1 2 0\n4 d 1 2 0\n5 0 3 4 0\n").expect("parse");
        assert_eq!(
            instructions,
            vec![
                LratInstr::Learn {
                    id: 3,
                    clause: vec![1, -2],
                    hints: vec![1, 2],
                },
                LratInstr::Forget { ids: vec![1, 2] },
                LratInstr::Learn {
                    id: 5,
                    clause: vec![],
                    hints: vec![3, 4],
                },
            ]
        );
        assert!(parse_text("nonsense").is_err());
    }

    #[test]
    fn binary_and_text_agree_on_a_real_proof() {
        // The pigeonhole proof emitted by CaDiCaL in both formats; the
        // binary bytes were captured from a live run.
        let text = "10 -2 0 7 8 2 3 6 0\n11 1 0 10 1 0\n12 -3 0 11 4 0\n\
                    13 -5 0 11 5 0\n14 4 0 12 2 0\n15 6 0 13 3 0\n16 0 14 15 9 0\n";
        let binary: &[u8] = &[
            0x61, 0x14, 0x05, 0x00, 0x0e, 0x10, 0x04, 0x06, 0x0c, 0x00, 0x61, 0x16, 0x02, 0x00,
            0x14, 0x02, 0x00, 0x61, 0x18, 0x07, 0x00, 0x16, 0x08, 0x00, 0x61, 0x1a, 0x0b, 0x00,
            0x16, 0x0a, 0x00, 0x61, 0x1c, 0x08, 0x00, 0x18, 0x04, 0x00, 0x61, 0x1e, 0x0c, 0x00,
            0x1a, 0x06, 0x00, 0x61, 0x20, 0x00, 0x1c, 0x1e, 0x12, 0x00,
        ];
        assert_eq!(
            parse(binary).expect("binary"),
            parse_text(text).expect("text")
        );
    }

    #[test]
    fn the_kernel_learns_only_certified_clauses() {
        let initial = vec![vec![1], vec![-1]];
        let mut kernel = LratKernel::new(&initial);
        assert_eq!(
            kernel.learn(3, &[], &[1, 1]),
            Err(LratError::UselessHint { step: 3, clause: 1 })
        );
        assert!(!kernel.refuted());
        kernel.learn(3, &[], &[1, 2]).expect("refutation");
        assert!(kernel.refuted());
    }

    #[test]
    fn checks_the_unit_contradiction() {
        let initial = vec![vec![1], vec![-1]];
        let instructions = parse_text("3 0 1 2 0\n").expect("parse");
        check(&initial, &instructions).expect("refutation");
    }

    #[test]
    fn rejects_bogus_hints_and_missing_refutations() {
        let initial = vec![vec![1], vec![-1]];
        assert_eq!(
            check(&initial, &parse_text("3 0 1 1 0\n").expect("parse")),
            Err(LratError::UselessHint { step: 3, clause: 1 })
        );
        // A valid but non-refuting instruction stream is not a refutation.
        assert_eq!(
            check(&initial, &parse_text("3 -1 0 2 0\n").expect("parse")),
            Err(LratError::NoRefutation)
        );
        assert_eq!(check(&initial, &[]), Err(LratError::NoRefutation));
    }

    #[test]
    fn accepts_rat_steps_with_fresh_variables() {
        // Mirrors the shape CaDiCaL's preprocessing emits: clauses over
        // fresh variable 3 introduced with vacuous/blocked RAT (empty
        // hints, no clause contains -3), then a full RAT step whose
        // resolvents are tautological.
        // The exact shape of CaDiCaL's php5 preprocessing steps
        // (46/47/48 there), relabeled: fresh variable 3 enters through
        // blocked clauses, then the definition's other direction is RAT
        // with tautological resolvents.
        let initial = vec![vec![1, 2], vec![-1, 2]];
        let mut kernel = LratKernel::new(&initial);
        // Blocked: no live clause contains -3.
        kernel.learn(3, &[3, -2], &[]).expect("blocked clause");
        kernel.learn(4, &[3, -1], &[]).expect("blocked clause");
        kernel
            .learn(5, &[-3, 2, 1], &[-3, -4])
            .expect("rat with tautological resolvents");
        // Incomplete coverage is rejected.
        assert_eq!(
            kernel.learn(6, &[-3, -2], &[-3]),
            Err(LratError::IncompleteRat { step: 6, clause: 4 })
        );
    }

    #[test]
    fn checks_a_three_variable_pigeonhole_style_proof() {
        let initial = vec![vec![1, 2], vec![-1, 2], vec![1, -2], vec![-1, -2]];
        let instructions = parse_text("5 2 0 1 2 0\n6 -2 0 3 4 0\n7 0 5 6 0\n").expect("parse");
        check(&initial, &instructions).expect("refutation");
    }
}
