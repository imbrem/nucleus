//! Compiler for the proof demo's deliberately tiny tactic language.

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Instruction {
    RewriteProposition(Direction),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Direction {
    Forward,
    Backward,
}

pub fn parse(source: &str) -> Result<Instruction, String> {
    let source = source.trim();
    let body = source
        .strip_prefix('(')
        .and_then(|source| source.strip_suffix(')'))
        .filter(|body| !body.contains(['(', ')']));
    let tokens: Vec<_> = body
        .map(str::split_whitespace)
        .into_iter()
        .flatten()
        .collect();
    match tokens.as_slice() {
        ["rewrite-proposition", "forward"] => {
            Ok(Instruction::RewriteProposition(Direction::Forward))
        }
        ["rewrite-proposition", "backward"] => {
            Ok(Instruction::RewriteProposition(Direction::Backward))
        }
        _ => Err(format!(
            "expected `(rewrite-proposition forward|backward)`, got {source:?}"
        )),
    }
}

/// Lowers the instruction to guest code which Rust then compiles into Wasm.
pub fn generate(instruction: Instruction) -> String {
    let direction = match instruction {
        Instruction::RewriteProposition(Direction::Forward) => "Forward",
        Instruction::RewriteProposition(Direction::Backward) => "Backward",
    };
    format!(
        r"
pub(crate) fn run(
    kernel: &Kernel,
    bool_type: u64,
    equality_theorem: u64,
    premise_theorem: u64,
) -> Result<RewriteResult, String> {{
    rewrite_proposition(
        kernel,
        bool_type,
        equality_theorem,
        premise_theorem,
        RewriteDirection::{direction},
    )
}}
"
    )
}
