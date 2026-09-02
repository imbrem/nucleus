//! Strict Alethe command parsing.

use covalence_data_sexpr::{Atom, Expr, ExprKind, Repr, SpannedRepr, parse_smt};
use covalence_lib_error::snafu::Snafu;

/// One strictly parsed Alethe proof command.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AletheCommand {
    /// `(assume id term)`.
    Assume { id: String, term: Expr },
    /// `(step id (cl ...) :rule rule ...)`.
    Step {
        id: String,
        clause: Vec<Expr>,
        rule: String,
        premises: Vec<String>,
        args: Vec<Expr>,
        discharge: Vec<String>,
    },
    /// `(anchor :step id :args (...))`.
    Anchor { step: String, args: Vec<Expr> },
    /// A local definitional abbreviation.
    DefineFun {
        name: String,
        params: Vec<Expr>,
        sort: Expr,
        body: Expr,
    },
}

/// A sequence of Alethe commands in source order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AletheProof(Vec<AletheCommand>);

impl AletheProof {
    /// Returns the commands in source order.
    #[must_use]
    pub fn commands(&self) -> &[AletheCommand] {
        &self.0
    }
}

/// One strictly parsed SMT-LIB problem command.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SmtCommand {
    /// `(set-logic name)`.
    SetLogic(String),
    /// `(declare-sort name arity)`.
    DeclareSort { name: String, arity: u32 },
    /// `(declare-fun name (parameters...) result)`.
    DeclareFun {
        name: String,
        parameters: Vec<Expr>,
        result: Expr,
    },
    /// `(assert proposition)`.
    Assert(Expr),
}

/// Semantic commands from one SMT-LIB problem, in source order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SmtProblem(Vec<SmtCommand>);

impl SmtProblem {
    /// Returns the semantic commands in source order.
    #[must_use]
    pub fn commands(&self) -> &[SmtCommand] {
        &self.0
    }
}

/// Why Alethe input was rejected.
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ParseError {
    /// The underlying S-expression syntax was malformed.
    #[snafu(display("could not parse Alethe S-expression: {source}"))]
    Syntax {
        source: covalence_data_sexpr::ParseError,
    },
    /// A command or attribute is outside the supported Alethe grammar.
    #[snafu(display("unsupported Alethe syntax: {message}"))]
    Unsupported { message: String },
    /// A required field was absent or had the wrong shape.
    #[snafu(display("malformed Alethe command: {message}"))]
    Malformed { message: String },
}

fn list(expression: &Expr) -> Result<&[Expr], ParseError> {
    match expression.node() {
        ExprKind::List(node) => Ok(SpannedRepr::list_items(node)),
        ExprKind::Atom(_) => Err(ParseError::Malformed {
            message: "expected a list".to_owned(),
        }),
    }
}

fn symbol(expression: &Expr) -> Result<&str, ParseError> {
    match expression.node() {
        ExprKind::Atom(node) => match SpannedRepr::atom(node) {
            Atom::Symbol(value) => Ok(value),
            _ => Err(ParseError::Malformed {
                message: "expected a symbol".to_owned(),
            }),
        },
        ExprKind::List(_) => Err(ParseError::Malformed {
            message: "expected a symbol".to_owned(),
        }),
    }
}

fn keyword(expression: &Expr) -> Result<&str, ParseError> {
    match expression.node() {
        ExprKind::Atom(node) => match SpannedRepr::atom(node) {
            Atom::Keyword(value) => Ok(value),
            _ => Err(ParseError::Malformed {
                message: "expected an attribute".to_owned(),
            }),
        },
        ExprKind::List(_) => Err(ParseError::Malformed {
            message: "expected an attribute".to_owned(),
        }),
    }
}

fn number(expression: &Expr) -> Result<&str, ParseError> {
    match expression.node() {
        ExprKind::Atom(node) => match SpannedRepr::atom(node) {
            Atom::Number(value) => Ok(value),
            _ => Err(ParseError::Malformed {
                message: "expected a number".to_owned(),
            }),
        },
        ExprKind::List(_) => Err(ParseError::Malformed {
            message: "expected a number".to_owned(),
        }),
    }
}

fn symbols(expression: &Expr) -> Result<Vec<String>, ParseError> {
    list(expression)?
        .iter()
        .map(|value| symbol(value).map(str::to_owned))
        .collect()
}

/// Parses a complete Alethe proof and rejects unknown commands or attributes.
///
/// # Errors
///
/// Returns [`ParseError`] for malformed S-expressions, missing fields, unknown
/// commands, duplicate attributes, or unsupported attributes.
pub fn parse_alethe(input: &str) -> Result<AletheProof, ParseError> {
    let document = parse_smt(input).map_err(|source| ParseError::Syntax { source })?;
    let mut expressions = document.expressions();
    if let [expression] = expressions {
        if let ExprKind::List(node) = expression.node() {
            let items = SpannedRepr::list_items(node);
            if items
                .first()
                .is_some_and(|item| matches!(item.node(), ExprKind::List(_)))
            {
                expressions = items;
            }
        }
    }
    expressions
        .iter()
        .map(parse_command)
        .collect::<Result<Vec<_>, _>>()
        .map(AletheProof)
}

/// Parses the complete stdout emitted by cvc5 for an unsatisfiable problem.
///
/// The accepted envelope is the `unsat` status followed by the parenthesized
/// Alethe command sequence produced by `--dump-proofs`.
///
/// # Errors
///
/// Returns [`ParseError`] if cvc5 did not report `unsat` or if its proof is
/// malformed or outside the supported Alethe grammar.
pub fn parse_cvc5_output(input: &str) -> Result<AletheProof, ParseError> {
    let input = input.trim();
    let proof = input
        .strip_prefix("unsat")
        .filter(|rest| rest.starts_with(char::is_whitespace))
        .ok_or_else(|| ParseError::Malformed {
            message: "cvc5 output must begin with an unsat status".to_owned(),
        })?;
    parse_alethe(proof.trim())
}

/// Parses the strict QF_UF-facing subset of an SMT-LIB problem.
///
/// Metadata commands (`check-sat`, `get-proof`, and `exit`) are accepted and
/// discarded. Every other unknown command fails closed.
///
/// # Errors
///
/// Returns [`ParseError`] for malformed input, unsupported commands, invalid
/// arities, or extra fields.
pub fn parse_smtlib2(input: &str) -> Result<SmtProblem, ParseError> {
    let document = parse_smt(input).map_err(|source| ParseError::Syntax { source })?;
    let mut commands = Vec::new();
    for expression in document.expressions() {
        let items = list(expression)?;
        let head = items.first().ok_or_else(|| ParseError::Malformed {
            message: "empty SMT-LIB command".to_owned(),
        })?;
        match symbol(head)? {
            "set-logic" if items.len() == 2 => {
                commands.push(SmtCommand::SetLogic(symbol(&items[1])?.to_owned()));
            }
            "declare-sort" if items.len() == 3 => {
                let spelling = number(&items[2])?;
                let arity = spelling.parse().map_err(|_| ParseError::Malformed {
                    message: format!("invalid sort arity {spelling:?}"),
                })?;
                commands.push(SmtCommand::DeclareSort {
                    name: symbol(&items[1])?.to_owned(),
                    arity,
                });
            }
            "declare-fun" if items.len() == 4 => {
                commands.push(SmtCommand::DeclareFun {
                    name: symbol(&items[1])?.to_owned(),
                    parameters: list(&items[2])?.to_vec(),
                    result: items[3].clone(),
                });
            }
            "declare-const" if items.len() == 3 => {
                commands.push(SmtCommand::DeclareFun {
                    name: symbol(&items[1])?.to_owned(),
                    parameters: Vec::new(),
                    result: items[2].clone(),
                });
            }
            "assert" if items.len() == 2 => commands.push(SmtCommand::Assert(items[1].clone())),
            "check-sat" | "get-proof" | "exit" if items.len() == 1 => {}
            "set-info" | "set-option" => {}
            known @ ("set-logic" | "declare-sort" | "declare-fun" | "declare-const" | "assert"
            | "check-sat" | "get-proof" | "exit") => {
                return Err(ParseError::Malformed {
                    message: format!("wrong field count for {known}"),
                });
            }
            other => {
                return Err(ParseError::Unsupported {
                    message: format!("SMT-LIB command {other:?}"),
                });
            }
        }
    }
    Ok(SmtProblem(commands))
}

fn parse_command(expression: &Expr) -> Result<AletheCommand, ParseError> {
    let items = list(expression)?;
    let command = items.first().ok_or_else(|| ParseError::Malformed {
        message: "empty command".to_owned(),
    })?;
    match symbol(command)? {
        "assume" => {
            if items.len() != 3 {
                return Err(ParseError::Malformed {
                    message: "assume requires an ID and term".to_owned(),
                });
            }
            Ok(AletheCommand::Assume {
                id: symbol(&items[1])?.to_owned(),
                term: items[2].clone(),
            })
        }
        "step" => parse_step(items),
        "anchor" => parse_anchor(items),
        "define-fun" => {
            if items.len() != 5 {
                return Err(ParseError::Malformed {
                    message: "define-fun requires a name, parameters, sort, and body".to_owned(),
                });
            }
            Ok(AletheCommand::DefineFun {
                name: symbol(&items[1])?.to_owned(),
                params: list(&items[2])?.to_vec(),
                sort: items[3].clone(),
                body: items[4].clone(),
            })
        }
        other => Err(ParseError::Unsupported {
            message: format!("command {other:?}"),
        }),
    }
}

fn parse_step(items: &[Expr]) -> Result<AletheCommand, ParseError> {
    if items.len() < 5 || items.len().is_multiple_of(2) {
        return Err(ParseError::Malformed {
            message: "step requires an ID, clause, and attribute-value pairs".to_owned(),
        });
    }
    let clause_items = list(&items[2])?;
    if clause_items.first().map(symbol).transpose()? != Some("cl") {
        return Err(ParseError::Malformed {
            message: "step clause must begin with cl".to_owned(),
        });
    }
    let mut rule = None;
    let mut premises = None;
    let mut args = None;
    let mut discharge = None;
    for pair in items[3..].chunks_exact(2) {
        let slot = match keyword(&pair[0])? {
            "rule" => {
                if rule.replace(symbol(&pair[1])?.to_owned()).is_some() {
                    return duplicate("rule");
                }
                continue;
            }
            "premises" => &mut premises,
            "args" => {
                if args.replace(list(&pair[1])?.to_vec()).is_some() {
                    return duplicate("args");
                }
                continue;
            }
            "discharge" => &mut discharge,
            other => {
                return Err(ParseError::Unsupported {
                    message: format!("step attribute :{other}"),
                });
            }
        };
        if slot.replace(symbols(&pair[1])?).is_some() {
            return duplicate(keyword(&pair[0])?);
        }
    }
    Ok(AletheCommand::Step {
        id: symbol(&items[1])?.to_owned(),
        clause: clause_items[1..].to_vec(),
        rule: rule.ok_or_else(|| ParseError::Malformed {
            message: "step is missing :rule".to_owned(),
        })?,
        premises: premises.unwrap_or_default(),
        args: args.unwrap_or_default(),
        discharge: discharge.unwrap_or_default(),
    })
}

fn parse_anchor(items: &[Expr]) -> Result<AletheCommand, ParseError> {
    if items.len() < 3 || items.len().is_multiple_of(2) {
        return Err(ParseError::Malformed {
            message: "anchor requires attribute-value pairs".to_owned(),
        });
    }
    let mut step = None;
    let mut args = None;
    for pair in items[1..].chunks_exact(2) {
        match keyword(&pair[0])? {
            "step" if step.is_none() => step = Some(symbol(&pair[1])?.to_owned()),
            "args" if args.is_none() => args = Some(list(&pair[1])?.to_vec()),
            "step" | "args" => return duplicate(keyword(&pair[0])?),
            other => {
                return Err(ParseError::Unsupported {
                    message: format!("anchor attribute :{other}"),
                });
            }
        }
    }
    Ok(AletheCommand::Anchor {
        step: step.ok_or_else(|| ParseError::Malformed {
            message: "anchor is missing :step".to_owned(),
        })?,
        args: args.unwrap_or_default(),
    })
}

fn duplicate<T>(attribute: &str) -> Result<T, ParseError> {
    Err(ParseError::Malformed {
        message: format!("duplicate :{attribute} attribute"),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const QF_UF: &str =
        include_str!("../../../proof/alethe/tests/fixtures/cvc5-qf-uf/proof.alethe");

    #[test]
    fn parses_the_selected_cvc5_qf_uf_fixture() {
        let proof = parse_alethe(QF_UF).expect("fixture parses");
        assert_eq!(proof.commands().len(), 8);
        assert!(matches!(
            proof.commands().last(),
            Some(AletheCommand::Step { rule, clause, .. })
                if rule == "resolution" && clause.is_empty()
        ));
    }

    #[test]
    fn parses_cvc5_stdout_envelope() {
        let output = format!("unsat\n(\n{QF_UF}\n)\n");
        let proof = parse_cvc5_output(&output).expect("cvc5 output parses");
        assert_eq!(proof.commands().len(), 8);
        assert!(matches!(
            parse_cvc5_output("sat\n"),
            Err(ParseError::Malformed { .. })
        ));
    }

    #[test]
    fn unknown_commands_and_attributes_fail_closed() {
        assert!(matches!(
            parse_alethe("(magic h p)"),
            Err(ParseError::Unsupported { .. })
        ));
        assert!(matches!(
            parse_alethe("(step t (cl) :rule resolution :trusted true)"),
            Err(ParseError::Unsupported { .. })
        ));
    }

    #[test]
    fn duplicate_attributes_fail_closed() {
        assert!(matches!(
            parse_alethe("(step t (cl) :rule resolution :rule refl)"),
            Err(ParseError::Malformed { .. })
        ));
    }

    #[test]
    fn parses_the_selected_qf_uf_problem_and_rejects_unknown_commands() {
        let source = include_str!("../../../proof/alethe/tests/fixtures/cvc5-qf-uf/problem.smt2");
        let problem = parse_smtlib2(source).expect("problem parses");
        assert_eq!(problem.commands().len(), 8);
        assert!(matches!(
            parse_smtlib2("(push 1)"),
            Err(ParseError::Unsupported { .. })
        ));
    }
}
