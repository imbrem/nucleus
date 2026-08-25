//! Untrusted text and binary LRAT parsing.

use covalence_lib_error::snafu::{self, Snafu};

use crate::{Clause, Formula, Literal, RatGroup};

/// One parsed LRAT proof step.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Step {
    LearnRup {
        id: u64,
        clause: Clause,
        ordered_hints: Vec<u64>,
    },
    LearnRat {
        id: u64,
        clause: Clause,
        pivot: Literal,
        prefix_rup_hints: Vec<u64>,
        groups: Vec<RatGroup>,
    },
    Forget {
        ids: Vec<u64>,
    },
}

/// Input which is not a well-formed LRAT proof.
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(snafu))]
#[snafu(display("malformed LRAT proof at {at}"))]
pub struct ParseError {
    at: usize,
}

fn error(at: usize) -> ParseError {
    ParseError { at }
}

/// Parses a strict DIMACS CNF byte stream while preserving clause and literal order.
///
/// # Errors
///
/// Returns the byte or line position containing malformed UTF-8, headers, literals,
/// terminators, variable bounds, or clause counts.
pub fn parse_dimacs(bytes: &[u8]) -> Result<Formula, ParseError> {
    let text = std::str::from_utf8(bytes).map_err(|utf8| error(utf8.valid_up_to()))?;
    let mut header = None;
    let mut values = Vec::new();
    for (line_index, raw_line) in text.lines().enumerate() {
        let at = line_index + 1;
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        if line.starts_with('p') {
            if header.is_some() || !values.is_empty() {
                return Err(error(at));
            }
            let fields = line.split_ascii_whitespace().collect::<Vec<_>>();
            if fields.len() != 4 || fields[0] != "p" || fields[1] != "cnf" {
                return Err(error(at));
            }
            let variables = fields[2].parse::<u64>().map_err(|_| error(at))?;
            let clauses = fields[3].parse::<usize>().map_err(|_| error(at))?;
            header = Some((variables, clauses));
            continue;
        }
        if header.is_none() {
            return Err(error(at));
        }
        values.extend(
            line.split_ascii_whitespace()
                .map(|token| token.parse::<i64>().map_err(|_| error(at)))
                .collect::<Result<Vec<_>, _>>()?,
        );
    }
    let (variables, expected_clauses) = header.ok_or_else(|| error(0))?;
    let mut clauses = Vec::new();
    let mut clause = Vec::new();
    for value in values {
        if value == 0 {
            clauses.push(Clause::from_signed(std::mem::take(&mut clause)).map_err(|_| error(0))?);
        } else {
            let literal = Literal::new(value).map_err(|_| error(0))?;
            if literal.variable() > variables {
                return Err(error(0));
            }
            clause.push(value);
        }
    }
    if !clause.is_empty() || clauses.len() != expected_clauses {
        return Err(error(0));
    }
    Ok(Formula::new(clauses))
}

/// Parses compact binary DIMACS: LRAT-style signed varints with `0` terminating
/// each clause and EOF terminating the formula.
///
/// This preserves literal and clause order. An empty byte string is the empty
/// formula, while a single zero byte is one empty clause.
///
/// # Errors
///
/// Returns the byte offset of a malformed integer or unterminated clause.
pub fn parse_binary_dimacs(bytes: &[u8]) -> Result<Formula, ParseError> {
    let mut position = 0;
    let mut clauses = Vec::new();
    while position < bytes.len() {
        let mut clause = Vec::new();
        loop {
            if position == bytes.len() {
                return Err(error(position));
            }
            let literal = read_signed(bytes, &mut position)?;
            if literal == 0 {
                break;
            }
            clause.push(literal);
        }
        clauses.push(Clause::from_signed(clause).map_err(|_| error(position))?);
    }
    Ok(Formula::new(clauses))
}

/// Encodes compact binary DIMACS using LRAT's signed-varint convention.
#[must_use]
pub fn encode_binary_dimacs(formula: &Formula) -> Vec<u8> {
    let mut bytes = Vec::new();
    for clause in formula.clauses() {
        for literal in clause.iter() {
            let magnitude = literal.get().unsigned_abs();
            let value = (magnitude << 1) | u64::from(literal.get() < 0);
            write_varint(value, &mut bytes);
        }
        bytes.push(0);
    }
    bytes
}

fn write_varint(mut value: u64, bytes: &mut Vec<u8>) {
    while value >= 0x80 {
        bytes.push(u8::try_from(value & 0x7f).expect("seven bits fit u8") | 0x80);
        value >>= 7;
    }
    bytes.push(u8::try_from(value).expect("final varint byte fits u8"));
}

fn learn(id: u64, signed_clause: Vec<i64>, hints: Vec<i64>, at: usize) -> Result<Step, ParseError> {
    if id == 0 {
        return Err(error(at));
    }
    let clause = Clause::from_signed(signed_clause).map_err(|_| error(at))?;
    let first_rat = hints.iter().position(|hint| *hint < 0);
    let Some(first_rat) = first_rat else {
        let ordered_hints = hints
            .into_iter()
            .map(|hint| u64::try_from(hint).map_err(|_| error(at)))
            .collect::<Result<_, _>>()?;
        return Ok(Step::LearnRup {
            id,
            clause,
            ordered_hints,
        });
    };
    let pivot = clause.first().ok_or_else(|| error(at))?;
    let prefix_rup_hints = hints[..first_rat]
        .iter()
        .map(|hint| u64::try_from(*hint).map_err(|_| error(at)))
        .collect::<Result<_, _>>()?;
    let mut groups = Vec::new();
    let mut index = first_rat;
    while index < hints.len() {
        let opposing = hints[index];
        if opposing >= 0 || opposing == i64::MIN {
            return Err(error(at));
        }
        index += 1;
        let start = index;
        while index < hints.len() && hints[index] > 0 {
            index += 1;
        }
        let resolvent_rup_hints = hints[start..index]
            .iter()
            .map(|hint| u64::try_from(*hint).map_err(|_| error(at)))
            .collect::<Result<_, _>>()?;
        groups.push(RatGroup {
            opposing_clause_id: opposing.unsigned_abs(),
            resolvent_rup_hints,
        });
    }
    Ok(Step::LearnRat {
        id,
        clause,
        pivot,
        prefix_rup_hints,
        groups,
    })
}

/// Parses strict text LRAT into typed kernel calls.
///
/// # Errors
///
/// Returns the line containing malformed syntax or an invalid typed value.
pub fn parse_text(text: &str) -> Result<Vec<Step>, ParseError> {
    let mut calls = Vec::new();
    for (line_index, raw_line) in text.lines().enumerate() {
        let at = line_index + 1;
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        let mut tokens = line.split_ascii_whitespace();
        let id = tokens
            .next()
            .and_then(|token| token.parse::<u64>().ok())
            .ok_or_else(|| error(at))?;
        if id == 0 {
            return Err(error(at));
        }
        let first = tokens.next().ok_or_else(|| error(at))?;
        if first == "d" {
            let ids = terminated_unsigned(&mut tokens, at)?;
            if tokens.next().is_some() {
                return Err(error(at));
            }
            calls.push(Step::Forget { ids });
            continue;
        }
        let values = std::iter::once(first)
            .chain(tokens)
            .map(|token| token.parse::<i64>().map_err(|_| error(at)))
            .collect::<Result<Vec<_>, _>>()?;
        let first_zero = values
            .iter()
            .position(|value| *value == 0)
            .ok_or_else(|| error(at))?;
        let second_zero = values[first_zero + 1..]
            .iter()
            .position(|value| *value == 0)
            .map(|index| first_zero + 1 + index)
            .ok_or_else(|| error(at))?;
        if second_zero + 1 != values.len() {
            return Err(error(at));
        }
        calls.push(learn(
            id,
            values[..first_zero].to_vec(),
            values[first_zero + 1..second_zero].to_vec(),
            at,
        )?);
    }
    Ok(calls)
}

fn terminated_unsigned<'a>(
    tokens: &mut impl Iterator<Item = &'a str>,
    at: usize,
) -> Result<Vec<u64>, ParseError> {
    let mut values = Vec::new();
    for token in tokens.by_ref() {
        let value = token.parse::<u64>().map_err(|_| error(at))?;
        if value == 0 {
            return Ok(values);
        }
        values.push(value);
    }
    Err(error(at))
}

/// Parses binary LRAT into typed kernel calls.
///
/// # Errors
///
/// Returns the byte offset containing malformed or truncated data.
pub fn parse_binary(bytes: &[u8]) -> Result<Vec<Step>, ParseError> {
    let mut calls = Vec::new();
    let mut position = 0;
    while position < bytes.len() {
        let marker_at = position;
        let marker = bytes[position];
        position += 1;
        match marker {
            b'a' => {
                let id = read_unsigned(bytes, &mut position)?;
                let clause = read_signed_section(bytes, &mut position)?;
                let hints = read_signed_section(bytes, &mut position)?;
                calls.push(learn(id, clause, hints, marker_at)?);
            }
            b'd' => {
                let signed = read_signed_section(bytes, &mut position)?;
                let ids = signed
                    .into_iter()
                    .map(|id| u64::try_from(id).map_err(|_| error(position)))
                    .collect::<Result<_, _>>()?;
                calls.push(Step::Forget { ids });
            }
            _ => return Err(error(marker_at)),
        }
    }
    Ok(calls)
}

fn read_signed_section(bytes: &[u8], position: &mut usize) -> Result<Vec<i64>, ParseError> {
    let mut values = Vec::new();
    loop {
        let value = read_signed(bytes, position)?;
        if value == 0 {
            return Ok(values);
        }
        values.push(value);
    }
}

fn read_unsigned(bytes: &[u8], position: &mut usize) -> Result<u64, ParseError> {
    u64::try_from(read_signed(bytes, position)?).map_err(|_| error(*position))
}

fn read_signed(bytes: &[u8], position: &mut usize) -> Result<i64, ParseError> {
    let raw = read_varint(bytes, position)?;
    if raw == 1 {
        return Err(error(*position));
    }
    let magnitude = i64::try_from(raw >> 1).map_err(|_| error(*position))?;
    Ok(if raw & 1 == 1 { -magnitude } else { magnitude })
}

fn read_varint(bytes: &[u8], position: &mut usize) -> Result<u64, ParseError> {
    let mut value = 0;
    let mut shift = 0;
    let mut count = 0;
    loop {
        let byte = *bytes.get(*position).ok_or_else(|| error(*position))?;
        *position += 1;
        count += 1;
        let payload = byte & 0x7f;
        if shift == 63 && payload > 1 {
            return Err(error(*position));
        }
        value |= u64::from(payload) << shift;
        if byte & 0x80 == 0 {
            if count > 1 && payload == 0 {
                return Err(error(*position));
            }
            return Ok(value);
        }
        if count == 10 {
            return Err(error(*position));
        }
        shift += 7;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn text_and_binary_parse_to_the_same_calls() {
        let text = parse_text("3 0 1 2 0\n4 d 1 2 0\n").unwrap();
        let binary = parse_binary(&[b'a', 6, 0, 2, 4, 0, b'd', 2, 4, 0]).unwrap();
        assert_eq!(text, binary);
    }

    #[test]
    fn dimacs_preserves_order_duplicates_and_empty_clauses() {
        let formula = parse_dimacs(b"c demo\np cnf 2 2\n2 1 2 0\n0\n").unwrap();
        assert_eq!(
            formula.clauses()[0]
                .iter()
                .map(Literal::get)
                .collect::<Vec<_>>(),
            [2, 1, 2]
        );
        assert!(formula.clauses()[1].is_empty());
        assert!(parse_dimacs(b"p cnf 1 1\n2 0\n").is_err());
        assert!(parse_dimacs(b"p cnf 1 2\n1 0\n").is_err());
    }

    #[test]
    fn binary_dimacs_round_trips_and_distinguishes_empty_cases() {
        let formula = Formula::from_signed([vec![2, -1, 2], vec![]]).unwrap();
        let bytes = encode_binary_dimacs(&formula);
        assert_eq!(bytes, [4, 3, 4, 0, 0]);
        assert_eq!(parse_binary_dimacs(&bytes).unwrap(), formula);
        assert!(parse_binary_dimacs(&[]).unwrap().is_empty());
        assert_eq!(parse_binary_dimacs(&[0]).unwrap().len(), 1);
        assert!(parse_binary_dimacs(&[2]).is_err());
    }

    #[test]
    fn rat_hints_become_explicit_groups() {
        let calls = parse_text("4 -3 2 0 1 -3 2 -7 5 0\n").unwrap();
        let Step::LearnRat {
            pivot,
            prefix_rup_hints,
            groups,
            ..
        } = &calls[0]
        else {
            panic!("RAT call")
        };
        assert_eq!(pivot.get(), -3);
        assert_eq!(prefix_rup_hints, &[1]);
        assert_eq!(groups[0].opposing_clause_id, 3);
        assert_eq!(groups[1].resolvent_rup_hints, [5]);
    }
}
