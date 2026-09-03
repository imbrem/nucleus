impl PartialEq for Theorem {
    fn eq(&self, other: &Self) -> bool {
        self.checked == other.checked
    }
}

impl Eq for Theorem {}

impl Hash for Theorem {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.checked.hash(state);
    }
}

pub(super) fn singleton(theorem: &Theorem) -> Result<Sequent, EditError> {
    let mut table = theorem.checked.decode_sequents()?;
    if table.len() != 1 {
        return Err(EditError::InapplicableRewrite {
            rule: "equivalence",
        });
    }
    table.pop().ok_or(EditError::InapplicableRewrite {
        rule: "equivalence",
    })
}

pub(super) fn evaluate(
    formula: &Formula,
    assignment: &std::collections::HashSet<u32>,
) -> Result<bool, EditError> {
    enum Task<'a> {
        Visit(&'a Formula),
        Finish {
            and: bool,
            negative: bool,
            children: usize,
        },
    }
    let mut tasks = vec![Task::Visit(formula)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(Formula::Literal { atom, negative }) => {
                values.push(assignment.contains(atom) ^ *negative);
            }
            Task::Visit(Formula::Sat { .. }) => return Err(EditError::NestedSat),
            Task::Visit(Formula::And { negative, children }) => {
                tasks.push(Task::Finish {
                    and: true,
                    negative: *negative,
                    children: children.len(),
                });
                tasks.extend(children.iter().rev().map(Task::Visit));
            }
            Task::Visit(Formula::Or { negative, children }) => {
                tasks.push(Task::Finish {
                    and: false,
                    negative: *negative,
                    children: children.len(),
                });
                tasks.extend(children.iter().rev().map(Task::Visit));
            }
            Task::Finish {
                and,
                negative,
                children,
            } => {
                let first = values
                    .len()
                    .checked_sub(children)
                    .ok_or(EditError::InvalidModel)?;
                let value = if and {
                    values[first..].iter().all(|value| *value)
                } else {
                    values[first..].iter().any(|value| *value)
                };
                values.truncate(first);
                values.push(value ^ negative);
            }
        }
    }
    values
        .pop()
        .filter(|_| values.is_empty())
        .ok_or(EditError::InvalidModel)
}

pub(super) fn positive_roots(sequent: &Sequent) -> Option<(Vec<Formula>, Vec<Formula>)> {
    let Formula::And {
        negative: false,
        children: premise,
    } = &sequent.premise
    else {
        return None;
    };
    let Formula::Or {
        negative: false,
        children: conclusion,
    } = &sequent.conclusion
    else {
        return None;
    };
    Some((premise.clone(), conclusion.clone()))
}

pub(super) fn erase_first(values: &mut Vec<Formula>, target: &Formula) -> Option<Formula> {
    let index = values.iter().position(|value| value == target)?;
    Some(values.remove(index))
}

pub(super) fn concatenate(mut left: Vec<Formula>, right: Vec<Formula>) -> Vec<Formula> {
    left.extend(right);
    left
}
use super::{EditError, Formula, Hash, Hasher, Sequent, Theorem};
