//! Untrusted text and binary LRAT parsing.

use crate::{Clause, Kernel, Literal, RatGroup, kernel::Error};

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

impl Step {
    /// Applies this parsed step through the semantic kernel API.
    ///
    /// # Errors
    ///
    /// Returns the kernel's semantic rejection without changing its state.
    pub fn apply(&self, kernel: &mut Kernel) -> Result<(), Error> {
        match self {
            Self::LearnRup {
                id,
                clause,
                ordered_hints,
            } => kernel.learn_rup(*id, clause, ordered_hints),
            Self::LearnRat {
                id,
                clause,
                pivot,
                prefix_rup_hints,
                groups,
            } => kernel.learn_rat(*id, clause, *pivot, prefix_rup_hints, groups),
            Self::Forget { ids } => kernel.forget(ids),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseError {
    at: usize,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(output, "malformed LRAT proof at {}", self.at)
    }
}

impl std::error::Error for ParseError {}

fn error(at: usize) -> ParseError {
    ParseError { at }
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
