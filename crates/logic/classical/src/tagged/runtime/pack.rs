/// Canonically packs an abstract sequent table into fresh dense storage.
///
/// The output begins with four reserved zero words, lays every live block out
/// in preorder using the least fitting size class, has no free blocks, and is
/// accepted only after validation recovers the exact semantic input.
///
/// # Errors
///
/// Returns an error if the formula table exceeds fixed-word or host resource
/// bounds, or if the generated candidate fails its independent postcheck.
pub fn pack(sequents: &[Sequent]) -> Result<Checked, RuntimeError> {
    let mut checked = Checked {
        arena: Arena::new(vec![Word::ZERO; RESERVED_WORDS], Word::ZERO, Vec::new()),
    };
    for sequent in sequents {
        checked.prepare_owned(&sequent.premise)?;
        checked.prepare_owned(&sequent.conclusion)?;
        let premise = checked.build_owned(&sequent.premise)?;
        let conclusion = checked.build_owned(&sequent.conclusion)?;
        checked.arena.roots.push((premise, conclusion));
    }
    checked
        .arena
        .validate_graph()
        .map_err(|_| RuntimeError::PackerPostcheck)?;
    let mut expected = Vec::with_capacity(2 * sequents.len());
    for sequent in sequents.iter().rev() {
        expected.push(&sequent.conclusion);
        expected.push(&sequent.premise);
    }
    let mut actual = Expand::new(&checked.arena);
    while let Some(formula) = expected.pop() {
        let token = match formula {
            Formula::Literal { atom, negative } => Token {
                tag: 3,
                negative: *negative,
                value: *atom,
            },
            Formula::And { negative, children }
            | Formula::Or { negative, children }
            | Formula::Sat { negative, children } => {
                expected.extend(children.iter().rev());
                Token {
                    tag: formula.tag(),
                    negative: *negative,
                    value: u32::try_from(children.len()).map_err(|_| {
                        RuntimeError::ResourceBound {
                            reason: "child count does not fit token",
                        }
                    })?,
                }
            }
        };
        if actual.step()?.as_ref() != Some(&token) {
            return Err(RuntimeError::PackerPostcheck);
        }
    }
    if actual.step()?.is_some() {
        return Err(RuntimeError::PackerPostcheck);
    }
    Ok(checked)
}

pub(super) fn least_size_class(children: usize) -> Result<usize, RuntimeError> {
    let needed = children.checked_add(1).ok_or(RuntimeError::ResourceBound {
        reason: "child count overflow",
    })?;
    let mut size_class = 0_usize;
    let mut capacity = 4_usize;
    while needed >= capacity {
        size_class = size_class
            .checked_add(1)
            .ok_or(RuntimeError::ResourceBound {
                reason: "size class overflow",
            })?;
        capacity = capacity.checked_mul(2).ok_or(RuntimeError::ResourceBound {
            reason: "block capacity overflow",
        })?;
    }
    Ok(size_class)
}
use super::{Arena, Checked, Expand, Formula, RESERVED_WORDS, RuntimeError, Sequent, Token, Word};
