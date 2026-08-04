//! Strict bounded JSON transport for inert local HOL proof recipes.

use std::error::Error as StdError;
use std::fmt;

use covalence_nucleus::{Connection, ContextId, Hol, Policy, TermId, TypeId};
use serde::{Deserialize, Serialize};

use super::{
    LocalHolProofOutput, LocalHolProofRef, LocalHolProofScriptError, LocalHolProofStep,
    LocalHolTermInstantiation, LocalHolTypeInstantiation, LocalReplError,
    run_local_hol_proof_script,
};

/// Maximum UTF-8 byte length accepted at the JSON transport boundary.
pub const MAX_LOCAL_HOL_PROOF_JSON_BYTES: usize = 1_048_576;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Request {
    version: u32,
    steps: Vec<WireStep>,
}

#[derive(Deserialize)]
#[serde(tag = "op", rename_all = "snake_case", deny_unknown_fields)]
enum WireStep {
    LoadTheorem {
        context: i64,
        conclusion: i64,
    },
    Hypothesis {
        context: i64,
        term: i64,
    },
    Truth {
        context: i64,
    },
    Reflexivity {
        context: i64,
        term: i64,
    },
    Beta {
        context: i64,
        abstraction: i64,
        argument: i64,
    },
    PersistTheorem {
        theorem: u32,
    },
    ConversionReflexivity {
        term: i64,
    },
    ConversionSymmetry {
        conversion: u32,
    },
    ConversionTransitivity {
        first: u32,
        second: u32,
    },
    ConversionApplication {
        function: u32,
        argument: u32,
    },
    ConversionLambda {
        parameter_type: i64,
        body: u32,
    },
    ConversionBeta {
        abstraction: i64,
        argument: i64,
    },
    ConversionEta {
        function: i64,
    },
    ConversionEquality {
        context: i64,
        conversion: u32,
    },
    ConvertTheorem {
        theorem: u32,
        conversion: u32,
    },
    ContextImplication {
        antecedent: i64,
        consequent: i64,
        witnesses: Vec<u32>,
    },
    LoadContextImplication {
        antecedent: i64,
        consequent: i64,
    },
    ContextImplicationPath {
        path: Vec<i64>,
    },
    PersistContextImplication {
        implication: u32,
    },
    Weaken {
        implication: u32,
        theorem: u32,
    },
    EqualityModusPonens {
        equality: u32,
        premise: u32,
    },
    EqualitySubstitution {
        equality: u32,
        predicate: i64,
        premise: u32,
    },
    DeductionAntisymmetry {
        first: u32,
        second: u32,
    },
    InstantiateTerms {
        theorem: u32,
        instantiations: Vec<WireInstantiation>,
    },
    InstantiateTypes {
        theorem: u32,
        instantiations: Vec<WireInstantiation>,
    },
    Abstraction {
        theorem: u32,
        variable: i64,
    },
    ContextUnion {
        left: i64,
        right: i64,
        result: i64,
    },
    LoadContextUnion {
        left: i64,
        right: i64,
    },
    ContextEquivalence {
        forward: u32,
        backward: u32,
    },
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireInstantiation {
    variable: i64,
    replacement: i64,
}

impl From<WireStep> for LocalHolProofStep {
    #[allow(clippy::too_many_lines)]
    fn from(step: WireStep) -> Self {
        let reference = LocalHolProofRef::from_u32;
        let context = ContextId::from_i64;
        let term = TermId::from_i64;
        match step {
            WireStep::LoadTheorem {
                context: c,
                conclusion,
            } => Self::LoadTheorem {
                context: context(c),
                conclusion: term(conclusion),
            },
            WireStep::Hypothesis {
                context: c,
                term: t,
            } => Self::Hypothesis {
                context: context(c),
                term: term(t),
            },
            WireStep::Truth { context: c } => Self::Truth {
                context: context(c),
            },
            WireStep::Reflexivity {
                context: c,
                term: t,
            } => Self::Reflexivity {
                context: context(c),
                term: term(t),
            },
            WireStep::Beta {
                context: c,
                abstraction,
                argument,
            } => Self::Beta {
                context: context(c),
                abstraction: term(abstraction),
                argument: term(argument),
            },
            WireStep::PersistTheorem { theorem } => Self::PersistTheorem {
                theorem: reference(theorem),
            },
            WireStep::ConversionReflexivity { term: t } => {
                Self::ConversionReflexivity { term: term(t) }
            }
            WireStep::ConversionSymmetry { conversion } => Self::ConversionSymmetry {
                conversion: reference(conversion),
            },
            WireStep::ConversionTransitivity { first, second } => Self::ConversionTransitivity {
                first: reference(first),
                second: reference(second),
            },
            WireStep::ConversionApplication { function, argument } => Self::ConversionApplication {
                function: reference(function),
                argument: reference(argument),
            },
            WireStep::ConversionLambda {
                parameter_type,
                body,
            } => Self::ConversionLambda {
                parameter_type: TypeId::from_i64(parameter_type),
                body: reference(body),
            },
            WireStep::ConversionBeta {
                abstraction,
                argument,
            } => Self::ConversionBeta {
                abstraction: term(abstraction),
                argument: term(argument),
            },
            WireStep::ConversionEta { function } => Self::ConversionEta {
                function: term(function),
            },
            WireStep::ConversionEquality {
                context: c,
                conversion,
            } => Self::ConversionEquality {
                context: context(c),
                conversion: reference(conversion),
            },
            WireStep::ConvertTheorem {
                theorem,
                conversion,
            } => Self::ConvertTheorem {
                theorem: reference(theorem),
                conversion: reference(conversion),
            },
            WireStep::ContextImplication {
                antecedent,
                consequent,
                witnesses,
            } => Self::ContextImplication {
                antecedent: context(antecedent),
                consequent: context(consequent),
                witnesses: witnesses.into_iter().map(reference).collect(),
            },
            WireStep::LoadContextImplication {
                antecedent,
                consequent,
            } => Self::LoadContextImplication {
                antecedent: context(antecedent),
                consequent: context(consequent),
            },
            WireStep::ContextImplicationPath { path } => Self::ContextImplicationPath {
                path: path.into_iter().map(context).collect(),
            },
            WireStep::PersistContextImplication { implication } => {
                Self::PersistContextImplication {
                    implication: reference(implication),
                }
            }
            WireStep::Weaken {
                implication,
                theorem,
            } => Self::Weaken {
                implication: reference(implication),
                theorem: reference(theorem),
            },
            WireStep::EqualityModusPonens { equality, premise } => Self::EqualityModusPonens {
                equality: reference(equality),
                premise: reference(premise),
            },
            WireStep::EqualitySubstitution {
                equality,
                predicate,
                premise,
            } => Self::EqualitySubstitution {
                equality: reference(equality),
                predicate: term(predicate),
                premise: reference(premise),
            },
            WireStep::DeductionAntisymmetry { first, second } => Self::DeductionAntisymmetry {
                first: reference(first),
                second: reference(second),
            },
            WireStep::InstantiateTerms {
                theorem,
                instantiations,
            } => Self::InstantiateTerms {
                theorem: reference(theorem),
                instantiations: instantiations
                    .into_iter()
                    .map(|item| LocalHolTermInstantiation {
                        variable: term(item.variable),
                        replacement: term(item.replacement),
                    })
                    .collect(),
            },
            WireStep::InstantiateTypes {
                theorem,
                instantiations,
            } => Self::InstantiateTypes {
                theorem: reference(theorem),
                instantiations: instantiations
                    .into_iter()
                    .map(|item| LocalHolTypeInstantiation {
                        variable: TypeId::from_i64(item.variable),
                        replacement: TypeId::from_i64(item.replacement),
                    })
                    .collect(),
            },
            WireStep::Abstraction { theorem, variable } => Self::Abstraction {
                theorem: reference(theorem),
                variable: term(variable),
            },
            WireStep::ContextUnion {
                left,
                right,
                result,
            } => Self::ContextUnion {
                left: context(left),
                right: context(right),
                result: context(result),
            },
            WireStep::LoadContextUnion { left, right } => Self::LoadContextUnion {
                left: context(left),
                right: context(right),
            },
            WireStep::ContextEquivalence { forward, backward } => Self::ContextEquivalence {
                forward: reference(forward),
                backward: reference(backward),
            },
        }
    }
}

#[derive(Serialize)]
struct Response {
    version: u32,
    outputs: Vec<WireOutput>,
}

#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum WireOutput {
    Theorem {
        context: i64,
        conclusion: i64,
    },
    Conversion {
        left: i64,
        right: i64,
        ty: i64,
        closed: bool,
    },
    ContextImplication {
        antecedent: i64,
        consequent: i64,
    },
    ContextUnion {
        left: i64,
        right: i64,
        result: i64,
    },
    ContextEquivalence {
        left: i64,
        right: i64,
    },
    MissingTheorem,
    MissingContextImplication,
    MissingContextUnion,
    Unit,
}

impl From<LocalHolProofOutput> for WireOutput {
    fn from(output: LocalHolProofOutput) -> Self {
        match output {
            LocalHolProofOutput::Theorem {
                context,
                conclusion,
            } => Self::Theorem {
                context: context.get(),
                conclusion: conclusion.get(),
            },
            LocalHolProofOutput::Conversion {
                left,
                right,
                ty,
                closed,
            } => Self::Conversion {
                left: left.get(),
                right: right.get(),
                ty: ty.get(),
                closed,
            },
            LocalHolProofOutput::ContextImplication {
                antecedent,
                consequent,
            } => Self::ContextImplication {
                antecedent: antecedent.get(),
                consequent: consequent.get(),
            },
            LocalHolProofOutput::ContextUnion {
                left,
                right,
                result,
            } => Self::ContextUnion {
                left: left.get(),
                right: right.get(),
                result: result.get(),
            },
            LocalHolProofOutput::ContextEquivalence { left, right } => Self::ContextEquivalence {
                left: left.get(),
                right: right.get(),
            },
            LocalHolProofOutput::MissingTheorem => Self::MissingTheorem,
            LocalHolProofOutput::MissingContextImplication => Self::MissingContextImplication,
            LocalHolProofOutput::MissingContextUnion => Self::MissingContextUnion,
            LocalHolProofOutput::Unit => Self::Unit,
        }
    }
}

/// Decodes and replays one versioned bounded JSON recipe through the shared proof engine.
///
/// # Errors
///
/// Returns an error before parsing if the UTF-8 document is over the fixed byte bound. Strict
/// decoding rejects every unknown field, operation, and version. Replay retains the existing
/// step, operand, reference, sort, and policy bounds.
pub fn run_local_hol_proof_script_json<P: Policy>(
    connection: &mut Connection<Hol<P>>,
    json: &str,
) -> Result<String, LocalHolProofJsonError> {
    if json.len() > MAX_LOCAL_HOL_PROOF_JSON_BYTES {
        return Err(LocalHolProofJsonError::TooManyBytes {
            count: json.len(),
            maximum: MAX_LOCAL_HOL_PROOF_JSON_BYTES,
        });
    }
    let request: Request = serde_json::from_str(json).map_err(LocalHolProofJsonError::Decode)?;
    if request.version != 1 {
        return Err(LocalHolProofJsonError::UnsupportedVersion(request.version));
    }
    let steps = request
        .steps
        .into_iter()
        .map(Into::into)
        .collect::<Vec<_>>();
    let outputs = run_local_hol_proof_script(connection, &steps)?
        .into_iter()
        .map(Into::into)
        .collect();
    serde_json::to_string(&Response {
        version: 1,
        outputs,
    })
    .map_err(LocalHolProofJsonError::Encode)
}

/// Failure at the bounded JSON recipe boundary or during checked replay.
#[derive(Debug)]
pub enum LocalHolProofJsonError {
    TooManyBytes { count: usize, maximum: usize },
    Decode(serde_json::Error),
    UnsupportedVersion(u32),
    Script(LocalHolProofScriptError),
    Connection(LocalReplError),
    Encode(serde_json::Error),
}

impl fmt::Display for LocalHolProofJsonError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TooManyBytes { count, maximum } => {
                write!(
                    formatter,
                    "HOL proof JSON has {count} bytes; maximum is {maximum}"
                )
            }
            Self::Decode(error) => write!(formatter, "invalid HOL proof JSON: {error}"),
            Self::UnsupportedVersion(version) => {
                write!(formatter, "unsupported HOL proof JSON version {version}")
            }
            Self::Script(error) => write!(formatter, "HOL proof recipe rejected: {error}"),
            Self::Connection(error) => write!(formatter, "HOL connection rejected: {error}"),
            Self::Encode(error) => write!(formatter, "could not encode HOL proof result: {error}"),
        }
    }
}

impl StdError for LocalHolProofJsonError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Decode(error) | Self::Encode(error) => Some(error),
            Self::Script(error) => Some(error),
            Self::Connection(error) => Some(error),
            Self::TooManyBytes { .. } | Self::UnsupportedVersion(_) => None,
        }
    }
}

impl From<LocalHolProofScriptError> for LocalHolProofJsonError {
    fn from(error: LocalHolProofScriptError) -> Self {
        Self::Script(error)
    }
}

#[cfg(test)]
mod tests {
    use covalence_nucleus::{AllowAll, Connection};

    use super::*;

    #[test]
    fn strict_json_replays_through_the_shared_engine() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let response = run_local_hol_proof_script_json(
            &mut connection,
            r#"{"version":1,"steps":[{"op":"truth","context":0},{"op":"persist_theorem","theorem":0}]}"#,
        )
        .unwrap();
        assert_eq!(
            response,
            r#"{"version":1,"outputs":[{"kind":"theorem","context":0,"conclusion":3},{"kind":"unit"}]}"#
        );
    }

    #[test]
    fn strict_json_replays_type_instantiation() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let alpha = connection.insert_free_type(800).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let x_alpha = connection.insert_free_term(801, alpha).unwrap();
        let x_bool = connection.insert_free_term(801, bool_type).unwrap();
        let expected = connection.insert_equality(x_bool, x_bool).unwrap();
        let request = format!(
            r#"{{"version":1,"steps":[{{"op":"reflexivity","context":0,"term":{}}},{{"op":"instantiate_types","theorem":0,"instantiations":[{{"variable":{},"replacement":{}}}]}}]}}"#,
            x_alpha.get(),
            alpha.get(),
            bool_type.get(),
        );

        let response = run_local_hol_proof_script_json(&mut connection, &request).unwrap();
        assert_eq!(
            response,
            format!(
                r#"{{"version":1,"outputs":[{{"kind":"theorem","context":0,"conclusion":{}}},{{"kind":"theorem","context":0,"conclusion":{}}}]}}"#,
                connection.insert_equality(x_alpha, x_alpha).unwrap().get(),
                expected.get(),
            )
        );
    }

    #[test]
    fn strict_json_rejects_unknown_fields_and_operations() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        for request in [
            r#"{"version":1,"extra":0,"steps":[]}"#,
            r#"{"version":1,"steps":[{"op":"truth","context":0,"extra":0}]}"#,
            r#"{"version":1,"steps":[{"op":"invent_theorem"}]}"#,
        ] {
            assert!(matches!(
                run_local_hol_proof_script_json(&mut connection, request),
                Err(LocalHolProofJsonError::Decode(_))
            ));
        }
    }

    #[test]
    fn json_transport_checks_bytes_before_decoding() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let oversized = " ".repeat(MAX_LOCAL_HOL_PROOF_JSON_BYTES + 1);
        assert!(matches!(
            run_local_hol_proof_script_json(&mut connection, &oversized),
            Err(LocalHolProofJsonError::TooManyBytes { .. })
        ));
    }

    #[test]
    fn json_transport_retains_the_shared_step_bound() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let steps = std::iter::repeat_n(r#"{"op":"truth","context":0}"#, 4_097)
            .collect::<Vec<_>>()
            .join(",");
        let request = format!(r#"{{"version":1,"steps":[{steps}]}}"#);
        assert!(matches!(
            run_local_hol_proof_script_json(&mut connection, &request),
            Err(LocalHolProofJsonError::Script(
                LocalHolProofScriptError::TooManySteps { .. }
            ))
        ));
    }
}
