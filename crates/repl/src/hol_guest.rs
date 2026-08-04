//! Native host for the bounded beta-only HOL proof component contract.

use std::collections::HashSet;
use std::error::Error as StdError;
use std::fmt;

use covalence_nucleus::{
    Connection, ContextId, ExportId, Hol, Kernel, NamespaceExport, NamespaceId, Operation, Policy,
    SignedHolSnapshot, TermId, Theorem, TypeId,
};
use covalence_proton::{
    WasmtimeComponentLimits, WasmtimeComponentRuntime, WasmtimeRuntimeError, WasmtimeStore,
    wasmtime,
};
use wasmtime::component::{HasSelf, Linker, Resource};

mod bindings {
    use covalence_proton::wasmtime;

    wasmtime::component::bindgen!({
        path: "../nucleus/protocol/hol-proof-guest.wit",
        world: "hol-proof-guest",
        wasmtime_crate: covalence_proton::wasmtime,
    });
}

use bindings::covalence::hol_proof_guest::host::{
    AppendError, ContextNode, Host, HostContextNode, HostNamespaceNode, HostProofPlan,
    HostTermNode, HostTheoremNode, HostTypeNode, NamespaceNode, ProofPlan, TermNode, TheoremNode,
    TypeNode,
};

const PLAN_REP: u32 = 1;
const MAX_NODES: usize = 128;
const MAX_NAME_BYTES: usize = 256;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Sort {
    Type,
    Term,
    Context,
    Theorem,
    Namespace,
}

#[derive(Debug)]
enum Recipe {
    BoolType,
    Bound {
        index: u32,
        ty: usize,
    },
    Lambda {
        parameter_type: usize,
        body: usize,
    },
    Bool(bool),
    EmptyContext,
    Beta {
        context: usize,
        abstraction: usize,
        argument: usize,
    },
    Persist {
        theorem: usize,
    },
    Namespace {
        name: Option<String>,
    },
    ExportTheorem {
        namespace: usize,
        export: i64,
        theorem: usize,
        name: Option<String>,
    },
    ExportContext {
        namespace: usize,
        export: i64,
        context: usize,
        name: Option<String>,
    },
}

struct GuestState {
    recipe: Vec<Recipe>,
    sorts: Vec<Sort>,
    persisted: HashSet<usize>,
    sealed: bool,
}

impl GuestState {
    fn new() -> Self {
        Self {
            recipe: Vec::new(),
            sorts: Vec::new(),
            persisted: HashSet::new(),
            sealed: false,
        }
    }

    fn plan(plan: &Resource<ProofPlan>) -> Result<(), AppendError> {
        if plan.rep() == PLAN_REP {
            Ok(())
        } else {
            Err(AppendError::InvalidResource)
        }
    }

    fn node<T>(&self, node: &Resource<T>, sort: Sort) -> Result<usize, AppendError> {
        let index = usize::try_from(node.rep())
            .ok()
            .and_then(|rep| rep.checked_sub(2))
            .ok_or(AppendError::InvalidResource)?;
        if self.sorts.get(index) == Some(&sort) {
            Ok(index)
        } else {
            Err(AppendError::InvalidDependency)
        }
    }

    fn append<T>(&mut self, recipe: Recipe, sort: Sort) -> Result<Resource<T>, AppendError> {
        if self.sealed {
            return Err(AppendError::Sealed);
        }
        if self.recipe.len() >= MAX_NODES {
            return Err(AppendError::ResourceLimit);
        }
        let rep = u32::try_from(self.recipe.len() + 2).map_err(|_| AppendError::ResourceLimit)?;
        self.recipe.push(recipe);
        self.sorts.push(sort);
        Ok(Resource::new_own(rep))
    }

    fn name(name: Option<String>) -> Result<Option<String>, AppendError> {
        if name
            .as_ref()
            .is_some_and(|name| name.len() > MAX_NAME_BYTES)
        {
            Err(AppendError::ResourceLimit)
        } else {
            Ok(name)
        }
    }
}

impl Host for GuestState {}

impl HostProofPlan for GuestState {
    fn bool_type(&mut self, plan: Resource<ProofPlan>) -> Result<Resource<TypeNode>, AppendError> {
        Self::plan(&plan).and_then(|()| self.append(Recipe::BoolType, Sort::Type))
    }
    fn bound_term(
        &mut self,
        plan: Resource<ProofPlan>,
        index: u32,
        ty: Resource<TypeNode>,
    ) -> Result<Resource<TermNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&ty, Sort::Type))
            .and_then(|ty| self.append(Recipe::Bound { index, ty }, Sort::Term))
    }
    fn lambda(
        &mut self,
        plan: Resource<ProofPlan>,
        parameter_type: Resource<TypeNode>,
        body: Resource<TermNode>,
    ) -> Result<Resource<TermNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&parameter_type, Sort::Type))
            .and_then(|parameter_type| {
                self.node(&body, Sort::Term)
                    .map(|body| (parameter_type, body))
            })
            .and_then(|(parameter_type, body)| {
                self.append(
                    Recipe::Lambda {
                        parameter_type,
                        body,
                    },
                    Sort::Term,
                )
            })
    }
    fn bool_term(
        &mut self,
        plan: Resource<ProofPlan>,
        value: bool,
    ) -> Result<Resource<TermNode>, AppendError> {
        Self::plan(&plan).and_then(|()| self.append(Recipe::Bool(value), Sort::Term))
    }
    fn empty_context(
        &mut self,
        plan: Resource<ProofPlan>,
    ) -> Result<Resource<ContextNode>, AppendError> {
        Self::plan(&plan).and_then(|()| self.append(Recipe::EmptyContext, Sort::Context))
    }
    fn prove_beta(
        &mut self,
        plan: Resource<ProofPlan>,
        context: Resource<ContextNode>,
        abstraction: Resource<TermNode>,
        argument: Resource<TermNode>,
    ) -> Result<Resource<TheoremNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&context, Sort::Context))
            .and_then(|context| {
                self.node(&abstraction, Sort::Term)
                    .map(|abstraction| (context, abstraction))
            })
            .and_then(|(context, abstraction)| {
                self.node(&argument, Sort::Term)
                    .map(|argument| (context, abstraction, argument))
            })
            .and_then(|(context, abstraction, argument)| {
                self.append(
                    Recipe::Beta {
                        context,
                        abstraction,
                        argument,
                    },
                    Sort::Theorem,
                )
            })
    }
    fn persist_theorem(
        &mut self,
        plan: Resource<ProofPlan>,
        theorem: Resource<TheoremNode>,
    ) -> Result<(), AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&theorem, Sort::Theorem))
            .and_then(|theorem| {
                if self.recipe.len() >= MAX_NODES {
                    return Err(AppendError::ResourceLimit);
                }
                self.persisted.insert(theorem);
                self.recipe.push(Recipe::Persist { theorem });
                self.sorts.push(Sort::Theorem);
                Ok(())
            })
    }
    fn root_child_namespace(
        &mut self,
        plan: Resource<ProofPlan>,
        name: Option<String>,
    ) -> Result<Resource<NamespaceNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| GuestState::name(name))
            .and_then(|name| self.append(Recipe::Namespace { name }, Sort::Namespace))
    }
    fn export_theorem_conclusion(
        &mut self,
        plan: Resource<ProofPlan>,
        namespace: Resource<NamespaceNode>,
        export_id: i64,
        theorem: Resource<TheoremNode>,
        name: Option<String>,
    ) -> Result<(), AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&namespace, Sort::Namespace))
            .and_then(|namespace| {
                self.node(&theorem, Sort::Theorem)
                    .map(|theorem| (namespace, theorem))
            })
            .and_then(|(namespace, theorem)| {
                if self.persisted.contains(&theorem) {
                    Ok((namespace, theorem))
                } else {
                    Err(AppendError::InvalidDependency)
                }
            })
            .and_then(|(namespace, theorem)| {
                GuestState::name(name).map(|name| (namespace, theorem, name))
            })
            .and_then(|(namespace, theorem, name)| {
                if self.recipe.len() >= MAX_NODES {
                    return Err(AppendError::ResourceLimit);
                }
                self.recipe.push(Recipe::ExportTheorem {
                    namespace,
                    export: export_id,
                    theorem,
                    name,
                });
                self.sorts.push(Sort::Theorem);
                Ok(())
            })
    }
    fn export_context(
        &mut self,
        plan: Resource<ProofPlan>,
        namespace: Resource<NamespaceNode>,
        export_id: i64,
        context: Resource<ContextNode>,
        name: Option<String>,
    ) -> Result<(), AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&namespace, Sort::Namespace))
            .and_then(|namespace| {
                self.node(&context, Sort::Context)
                    .map(|context| (namespace, context))
            })
            .and_then(|(namespace, context)| {
                GuestState::name(name).map(|name| (namespace, context, name))
            })
            .and_then(|(namespace, context, name)| {
                if self.recipe.len() >= MAX_NODES {
                    return Err(AppendError::ResourceLimit);
                }
                self.recipe.push(Recipe::ExportContext {
                    namespace,
                    export: export_id,
                    context,
                    name,
                });
                self.sorts.push(Sort::Context);
                Ok(())
            })
    }
    fn drop(&mut self, _rep: Resource<ProofPlan>) -> wasmtime::Result<()> {
        Ok(())
    }
}

macro_rules! drop_resource {
    ($trait:ident, $ty:ident) => {
        impl $trait for GuestState {
            fn drop(&mut self, _rep: Resource<$ty>) -> wasmtime::Result<()> {
                Ok(())
            }
        }
    };
}
drop_resource!(HostTypeNode, TypeNode);
drop_resource!(HostTermNode, TermNode);
drop_resource!(HostContextNode, ContextNode);
drop_resource!(HostTheoremNode, TheoremNode);
drop_resource!(HostNamespaceNode, NamespaceNode);

#[derive(Clone, Copy, Debug)]
struct BetaGuestPolicy;
impl Policy for BetaGuestPolicy {
    fn allows(&mut self, operation: Operation) -> bool {
        matches!(
            operation,
            Operation::InsertType
                | Operation::InsertTerm
                | Operation::ProveBeta
                | Operation::PersistJudgement
                | Operation::DefineNamespace
                | Operation::ExportNamespaceValue
                | Operation::ExportSignedSnapshot
        )
    }
}

enum Value {
    Type(TypeId),
    Term(TermId),
    Context(ContextId),
    Theorem {
        context: ContextId,
        conclusion: TermId,
    },
    Namespace(NamespaceId),
    Unit,
}

fn replay(kernel: &Kernel, recipe: &[Recipe]) -> Result<SignedHolSnapshot, HolGuestError> {
    let mut db: Connection<Hol<BetaGuestPolicy>> =
        kernel.open_hol(BetaGuestPolicy).map_err(replay_error)?;
    let mut values = Vec::with_capacity(recipe.len());
    for node in recipe {
        let value = match node {
            Recipe::BoolType => Value::Type(db.insert_bool_type().map_err(replay_error)?),
            Recipe::Bound { index, ty } => Value::Term(
                db.insert_bound_term(*index, type_at(&values, *ty)?)
                    .map_err(replay_error)?,
            ),
            Recipe::Lambda {
                parameter_type,
                body,
            } => Value::Term(
                db.insert_lambda(type_at(&values, *parameter_type)?, term_at(&values, *body)?)
                    .map_err(replay_error)?,
            ),
            Recipe::Bool(value) => Value::Term(db.insert_bool_term(*value).map_err(replay_error)?),
            Recipe::EmptyContext => Value::Context(ContextId::empty()),
            Recipe::Beta { .. }
            | Recipe::Persist { .. }
            | Recipe::ExportTheorem { .. }
            | Recipe::ExportContext { .. } => Value::Unit,
            Recipe::Namespace { name } => Value::Namespace(
                db.create_namespace(Some(NamespaceId::root()), name.as_deref())
                    .map_err(replay_error)?,
            ),
        };
        values.push(value);
    }
    db.with_proof_session(|mut proof| {
        let mut theorems: Vec<Option<Theorem<'_>>> = (0..recipe.len()).map(|_| None).collect();
        for (index, node) in recipe.iter().enumerate() {
            match node {
                Recipe::Beta {
                    context,
                    abstraction,
                    argument,
                } => {
                    let theorem = proof
                        .prove_beta(
                            context_at(&values, *context)?,
                            term_at(&values, *abstraction)?,
                            term_at(&values, *argument)?,
                        )
                        .map_err(replay_error)?;
                    values[index] = Value::Theorem {
                        context: theorem.context(),
                        conclusion: theorem.conclusion(),
                    };
                    theorems[index] = Some(theorem);
                }
                Recipe::Persist { theorem } => {
                    let theorem = theorems
                        .get(*theorem)
                        .and_then(Option::as_ref)
                        .ok_or_else(value_error)?;
                    proof.persist_theorem(theorem).map_err(replay_error)?;
                }
                _ => {}
            }
        }
        Ok::<_, HolGuestError>(())
    })?;
    for node in recipe {
        match node {
            Recipe::ExportTheorem {
                namespace,
                export,
                theorem,
                name,
            } => db
                .export_value(
                    namespace_at(&values, *namespace)?,
                    ExportId::from_i64(*export),
                    NamespaceExport::Term(theorem_at(&values, *theorem)?.1),
                    name.as_deref(),
                )
                .map_err(replay_error)?,
            Recipe::ExportContext {
                namespace,
                export,
                context,
                name,
            } => db
                .export_value(
                    namespace_at(&values, *namespace)?,
                    ExportId::from_i64(*export),
                    NamespaceExport::Context(context_at(&values, *context)?),
                    name.as_deref(),
                )
                .map_err(replay_error)?,
            _ => {}
        }
    }
    kernel.export_hol(&mut db).map_err(replay_error)
}

fn value_error() -> HolGuestError {
    HolGuestError::Replay("internally inconsistent recipe value".into())
}
fn replay_error(error: impl fmt::Display) -> HolGuestError {
    HolGuestError::Replay(error.to_string())
}
fn type_at(values: &[Value], index: usize) -> Result<TypeId, HolGuestError> {
    match values.get(index) {
        Some(Value::Type(value)) => Ok(*value),
        _ => Err(value_error()),
    }
}
fn term_at(values: &[Value], index: usize) -> Result<TermId, HolGuestError> {
    match values.get(index) {
        Some(Value::Term(value)) => Ok(*value),
        _ => Err(value_error()),
    }
}
fn context_at(values: &[Value], index: usize) -> Result<ContextId, HolGuestError> {
    match values.get(index) {
        Some(Value::Context(value)) => Ok(*value),
        _ => Err(value_error()),
    }
}
fn theorem_at(values: &[Value], index: usize) -> Result<(ContextId, TermId), HolGuestError> {
    match values.get(index) {
        Some(Value::Theorem {
            context,
            conclusion,
        }) => Ok((*context, *conclusion)),
        _ => Err(value_error()),
    }
}
fn namespace_at(values: &[Value], index: usize) -> Result<NamespaceId, HolGuestError> {
    match values.get(index) {
        Some(Value::Namespace(value)) => Ok(*value),
        _ => Err(value_error()),
    }
}

/// Executes one untrusted component, then replays and signs only its completely successful plan.
///
/// # Errors
///
/// Returns an error if the component is invalid, traps, aborts, exceeds a bound, appends an
/// invalid recipe, or Nucleus rejects any replay, export, or signing operation. No snapshot is
/// returned unless every phase succeeds.
pub fn run_hol_proof_component(
    kernel: &Kernel,
    bytes: &[u8],
    limits: WasmtimeComponentLimits,
) -> Result<SignedHolSnapshot, HolGuestError> {
    let runtime = WasmtimeComponentRuntime::new(limits).map_err(HolGuestError::Runtime)?;
    let component = runtime.component(bytes).map_err(HolGuestError::Runtime)?;
    let mut linker: Linker<WasmtimeStore<GuestState>> = Linker::new(runtime.engine());
    bindings::HolProofGuest::add_to_linker::<_, HasSelf<GuestState>>(&mut linker, |state| {
        &mut state.data
    })
    .map_err(HolGuestError::Wasmtime)?;
    let mut store = runtime
        .store(GuestState::new())
        .map_err(HolGuestError::Runtime)?;
    let guest = bindings::HolProofGuest::instantiate(&mut store, &component, &linker)
        .map_err(HolGuestError::Wasmtime)?;
    let result = guest
        .covalence_hol_proof_guest_guest()
        .call_build(&mut store, Resource::new_borrow(PLAN_REP))
        .map_err(HolGuestError::Wasmtime)?;
    result.map_err(|_| HolGuestError::GuestAborted)?;
    store.data_mut().data.sealed = true;
    replay(kernel, &store.data().data.recipe)
}

/// Failure before a signed HOL artifact exists.
#[derive(Debug)]
pub enum HolGuestError {
    Runtime(WasmtimeRuntimeError),
    Wasmtime(wasmtime::Error),
    GuestAborted,
    Replay(String),
}
impl fmt::Display for HolGuestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Runtime(e) => write!(f, "{e}"),
            Self::Wasmtime(e) => write!(f, "component failed: {e}"),
            Self::GuestAborted => f.write_str("guest aborted"),
            Self::Replay(e) => write!(f, "proof replay failed: {e}"),
        }
    }
}
impl StdError for HolGuestError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn export_before_persist_is_rejected_without_appending() {
        let mut state = GuestState::new();
        let plan = Resource::new_borrow(PLAN_REP);
        let context = state.empty_context(Resource::new_borrow(PLAN_REP)).unwrap();
        let ty = state.bool_type(Resource::new_borrow(PLAN_REP)).unwrap();
        let bound = state
            .bound_term(Resource::new_borrow(PLAN_REP), 0, ty)
            .unwrap();
        let ty = state.bool_type(Resource::new_borrow(PLAN_REP)).unwrap();
        let abstraction = state
            .lambda(Resource::new_borrow(PLAN_REP), ty, bound)
            .unwrap();
        let argument = state
            .bool_term(Resource::new_borrow(PLAN_REP), true)
            .unwrap();
        let theorem = state
            .prove_beta(
                Resource::new_borrow(PLAN_REP),
                context,
                abstraction,
                argument,
            )
            .unwrap();
        let namespace = state
            .root_child_namespace(Resource::new_borrow(PLAN_REP), Some("demo".into()))
            .unwrap();
        let before = state.recipe.len();
        assert_eq!(
            state.export_theorem_conclusion(plan, namespace, 0, theorem, None),
            Err(AppendError::InvalidDependency)
        );
        assert_eq!(state.recipe.len(), before);
    }

    #[test]
    fn invalid_component_never_returns_a_signed_snapshot() {
        let kernel = Kernel::ephemeral();
        assert!(
            run_hol_proof_component(
                &kernel,
                b"not a component",
                WasmtimeComponentLimits::default(),
            )
            .is_err()
        );
    }
}
