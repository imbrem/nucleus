//! Native host for the bounded beta-only HOL proof component contract.

use std::{collections::HashSet, error::Error as StdError, fmt};

use covalence_nucleus::{
    Connection, ContextId, ExportId, Hol, Kernel, NamespaceExport, NamespaceId, Operation, Policy,
    SignedHolSnapshot, TermId, Theorem, TypeId,
};
use covalence_proton::{
    WasmtimeComponentLimits, WasmtimeComponentRuntime, WasmtimeRuntimeError, WasmtimeStore,
    wasmtime,
};
use wasmtime::component::{HasSelf, Linker, Resource};

use crate::{
    ConnectionId, KernelId, LocalConnection, ReceivedHolSnapshot, Repl, SignedHolArtifact,
    authenticate_pinned_signed_hol_artifact, trust_and_receive_pinned_signed_hol_artifact,
};

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
        (plan.rep() == PLAN_REP)
            .then_some(())
            .ok_or(AppendError::InvalidResource)
    }

    fn node<T>(&self, node: &Resource<T>, sort: Sort) -> Result<usize, AppendError> {
        let index = usize::try_from(node.rep())
            .ok()
            .and_then(|rep| rep.checked_sub(2))
            .ok_or(AppendError::InvalidResource)?;
        let actual = self.sorts.get(index).ok_or(AppendError::InvalidResource)?;
        (*actual == sort)
            .then_some(index)
            .ok_or(AppendError::InvalidDependency)
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

    fn append_unit(&mut self, recipe: Recipe, sort: Sort) -> Result<(), AppendError> {
        if self.sealed {
            return Err(AppendError::Sealed);
        }
        if self.recipe.len() >= MAX_NODES {
            return Err(AppendError::ResourceLimit);
        }
        self.recipe.push(recipe);
        self.sorts.push(sort);
        Ok(())
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
                self.append_unit(Recipe::Persist { theorem }, Sort::Theorem)?;
                self.persisted.insert(theorem);
                Ok(())
            })
    }

    fn root_child_namespace(
        &mut self,
        plan: Resource<ProofPlan>,
        name: Option<String>,
    ) -> Result<Resource<NamespaceNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| Self::name(name))
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
                self.persisted
                    .contains(&theorem)
                    .then_some((namespace, theorem))
                    .ok_or(AppendError::InvalidDependency)
            })
            .and_then(|(namespace, theorem)| {
                Self::name(name).map(|name| (namespace, theorem, name))
            })
            .and_then(|(namespace, theorem, name)| {
                self.append_unit(
                    Recipe::ExportTheorem {
                        namespace,
                        export: export_id,
                        theorem,
                        name,
                    },
                    Sort::Theorem,
                )
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
                Self::name(name).map(|name| (namespace, context, name))
            })
            .and_then(|(namespace, context, name)| {
                self.append_unit(
                    Recipe::ExportContext {
                        namespace,
                        export: export_id,
                        context,
                        name,
                    },
                    Sort::Context,
                )
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
                | Operation::ProveConversionBeta
                | Operation::ProveConversionEquality
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

fn replay(
    kernel: &Kernel,
    recipe: &[Recipe],
    selected_namespace: usize,
) -> Result<SignedHolArtifact, HolGuestError> {
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
            Recipe::Namespace { name } => Value::Namespace(
                db.create_namespace(Some(NamespaceId::root()), name.as_deref())
                    .map_err(replay_error)?,
            ),
            Recipe::Beta { .. }
            | Recipe::Persist { .. }
            | Recipe::ExportTheorem { .. }
            | Recipe::ExportContext { .. } => Value::Unit,
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
                    let theorem = crate::hol_recipes::beta(
                        &mut proof,
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
    let namespace = namespace_at(&values, selected_namespace)?;
    let snapshot = kernel.export_hol(&mut db).map_err(replay_error)?;
    snapshot_artifact(namespace, &snapshot)
}

fn snapshot_artifact(
    namespace: NamespaceId,
    snapshot: &SignedHolSnapshot,
) -> Result<SignedHolArtifact, HolGuestError> {
    let image = snapshot.image().bytes();
    if image.len() > crate::MAX_IMAGE_BYTES {
        return Err(HolGuestError::ArtifactTooLarge {
            size: image.len(),
            maximum: crate::MAX_IMAGE_BYTES,
        });
    }
    let attestation = snapshot.attestation();
    let schema = attestation.schema();
    let image_hash = attestation.image();
    let signer = attestation.signer();
    let public_key = attestation.public_key().to_vec();
    let signature = attestation.signature().to_vec();
    Ok(SignedHolArtifact {
        namespace_id: namespace.get(),
        image: image.to_vec(),
        schema,
        image_hash,
        signer,
        public_key,
        signature,
    })
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

/// Executes one untrusted component, then replays and signs only its successful sealed plan.
///
/// The guest receives neither a database connection nor signing authority. A failed component,
/// plan, replay, persistence, namespace export, or signing step returns no snapshot.
///
/// # Errors
///
/// Returns an error if component validation or execution fails, the guest aborts, a resource
/// bound is exceeded, or checked replay/export/signing rejects the requested plan.
pub fn run_hol_proof_component(
    kernel: &Kernel,
    bytes: &[u8],
    limits: WasmtimeComponentLimits,
) -> Result<SignedHolArtifact, HolGuestError> {
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
    let selected_namespace = guest
        .covalence_hol_proof_guest_guest()
        .call_build(&mut store, Resource::new_borrow(PLAN_REP))
        .map_err(HolGuestError::Wasmtime)?
        .map_err(|_| HolGuestError::GuestAborted)?;
    let selected_namespace = store
        .data()
        .data
        .node(&selected_namespace, Sort::Namespace)
        .map_err(|_| HolGuestError::InvalidReturnedNamespace)?;
    store.data_mut().data.sealed = true;
    replay(kernel, &store.data().data.recipe, selected_namespace)
}

/// Signed guest output plus the receiver connection retained by a caller-owned REPL.
pub struct ManagedHolGuestResult {
    artifact: SignedHolArtifact,
    received: ReceivedHolSnapshot,
    connection: ConnectionId,
}

impl ManagedHolGuestResult {
    /// Returns the exact independently transportable signed snapshot.
    #[must_use]
    pub const fn artifact(&self) -> &SignedHolArtifact {
        &self.artifact
    }

    /// Returns the receiver-local imported coordinates.
    #[must_use]
    pub const fn received(&self) -> ReceivedHolSnapshot {
        self.received
    }

    /// Returns the live HOL connection retained in the caller's directory.
    #[must_use]
    pub const fn connection(&self) -> ConnectionId {
        self.connection
    }
}

/// Executes a guest and retains its authenticated import in caller-owned REPL state.
///
/// The directory's local endpoint key must describe `kernel`. Component execution
/// still occurs in a fresh disposable producer connection. Only after execution,
/// checked replay, signing, independent authentication, key pinning, and detached
/// validation succeed does this function open a receiver, import the snapshot, and
/// insert that live receiver into `directory`. The signed bytes and cryptographic
/// capabilities are never persisted in the raw REPL state database.
///
/// Existing active-connection selection is preserved. An empty directory selects
/// the newly inserted receiver through [`Repl::insert`]'s ordinary behavior.
///
/// # Errors
///
/// Returns the exact high-level phase which failed. No connection is inserted into
/// the caller's directory before all proof, signature, validation, and import work
/// has succeeded.
pub fn run_managed_hol_proof_component(
    kernel: &Kernel,
    directory: &mut Repl<LocalConnection>,
    bytes: &[u8],
    limits: WasmtimeComponentLimits,
) -> Result<ManagedHolGuestResult, ManagedHolGuestError> {
    let artifact = run_hol_proof_component(kernel, bytes, limits)
        .map_err(|error| ManagedHolGuestError::at("component-executed", error))?;
    retain_signed_hol_guest_artifact(kernel, directory, artifact)
}

/// Authenticates a completed guest artifact and retains its imported receiver.
///
/// This split form lets a caller durably present the signed bytes before it
/// mutates its REPL directory. The artifact is still treated as untrusted: it
/// is checked against the directory's independently recorded local key,
/// detached-validated, trusted explicitly, and imported through a fresh
/// receiver before that receiver is moved into caller-owned state.
///
/// # Errors
///
/// Returns the exact phase which failed. No receiver is inserted before the
/// complete authentication, validation, trust, and import sequence succeeds.
pub fn retain_signed_hol_guest_artifact(
    kernel: &Kernel,
    directory: &mut Repl<LocalConnection>,
    artifact: SignedHolArtifact,
) -> Result<ManagedHolGuestResult, ManagedHolGuestError> {
    let expected = directory
        .expected_kernel_identity(KernelId::LOCAL)
        .map_err(|error| ManagedHolGuestError::at("local-key-loaded", error))?;
    let pinned = authenticate_pinned_signed_hol_artifact(&expected, &artifact)
        .map_err(|error| ManagedHolGuestError::at("artifact-authenticated", error))?;
    let mut target = kernel
        .open_hol(covalence_nucleus::AllowAll)
        .map_err(|error| ManagedHolGuestError::at("receiver-opened", error))?;
    let received = trust_and_receive_pinned_signed_hol_artifact(&mut target, pinned)
        .map_err(|error| ManagedHolGuestError::at("artifact-imported", error))?;
    let retained = LocalConnection::Hol(target);
    let connection = directory
        .insert(retained.protocol(), retained)
        .map_err(|error| ManagedHolGuestError::at("receiver-retained", error))?;
    Ok(ManagedHolGuestResult {
        artifact,
        received,
        connection,
    })
}

/// Failure of one explicit managed guest boundary.
#[derive(Debug)]
pub struct ManagedHolGuestError {
    phase: &'static str,
    message: String,
}

impl ManagedHolGuestError {
    fn at(phase: &'static str, error: impl fmt::Display) -> Self {
        Self {
            phase,
            message: error.to_string(),
        }
    }

    /// Returns the first boundary which rejected the operation.
    #[must_use]
    pub const fn phase(&self) -> &'static str {
        self.phase
    }
}

impl fmt::Display for ManagedHolGuestError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.phase, self.message)
    }
}

impl StdError for ManagedHolGuestError {}

/// Failure before a signed HOL snapshot exists.
#[derive(Debug)]
pub enum HolGuestError {
    Runtime(WasmtimeRuntimeError),
    Wasmtime(wasmtime::Error),
    GuestAborted,
    InvalidReturnedNamespace,
    ArtifactTooLarge { size: usize, maximum: usize },
    Replay(String),
}

impl fmt::Display for HolGuestError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Runtime(error) => write!(formatter, "{error}"),
            Self::Wasmtime(error) => write!(formatter, "component failed: {error}"),
            Self::GuestAborted => formatter.write_str("guest aborted"),
            Self::InvalidReturnedNamespace => {
                formatter.write_str("guest returned an invalid export namespace")
            }
            Self::ArtifactTooLarge { size, maximum } => {
                write!(
                    formatter,
                    "signed artifact is {size} bytes; maximum is {maximum}"
                )
            }
            Self::Replay(error) => write!(formatter, "proof replay failed: {error}"),
        }
    }
}

impl StdError for HolGuestError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn forged_or_wrong_sort_resource_representations_are_rejected() {
        let mut state = GuestState::new();
        let ty = state.bool_type(Resource::new_borrow(PLAN_REP)).unwrap();
        assert_eq!(
            state.node(&Resource::<TypeNode>::new_borrow(u32::MAX), Sort::Type),
            Err(AppendError::InvalidResource)
        );
        assert_eq!(
            state.node(&ty, Sort::Term),
            Err(AppendError::InvalidDependency)
        );
        assert_eq!(
            GuestState::plan(&Resource::new_borrow(PLAN_REP + 1)),
            Err(AppendError::InvalidResource)
        );
    }

    #[test]
    fn recipe_and_name_bounds_are_enforced_before_append() {
        assert_eq!(
            GuestState::name(Some("x".repeat(MAX_NAME_BYTES + 1))),
            Err(AppendError::ResourceLimit)
        );
        let mut state = GuestState::new();
        for _ in 0..MAX_NODES {
            state
                .append::<TypeNode>(Recipe::BoolType, Sort::Type)
                .unwrap();
        }
        let before = state.recipe.len();
        assert!(matches!(
            state.append::<TypeNode>(Recipe::BoolType, Sort::Type),
            Err(AppendError::ResourceLimit)
        ));
        assert_eq!(state.recipe.len(), before);
    }

    #[test]
    fn replayed_guest_artifact_uses_the_selected_receiver_contract() {
        let recipe = vec![
            Recipe::BoolType,
            Recipe::Bound { index: 0, ty: 0 },
            Recipe::Lambda {
                parameter_type: 0,
                body: 1,
            },
            Recipe::Bool(true),
            Recipe::EmptyContext,
            Recipe::Beta {
                context: 4,
                abstraction: 2,
                argument: 3,
            },
            Recipe::Persist { theorem: 5 },
            Recipe::Namespace {
                name: Some("demo".into()),
            },
            Recipe::ExportContext {
                namespace: 7,
                export: 0,
                context: 4,
                name: Some("empty_context".into()),
            },
            Recipe::ExportTheorem {
                namespace: 7,
                export: 1,
                theorem: 5,
                name: Some("identity_true_beta".into()),
            },
        ];
        let producer = Kernel::ephemeral();
        let artifact = replay(&producer, &recipe, 7).unwrap();
        assert_eq!(artifact.namespace_id(), 1);
        assert!(artifact.image().len() <= crate::MAX_IMAGE_BYTES);

        let expected = crate::ExpectedKernelIdentity::from_public_key(
            crate::KernelId::from_u32(7),
            producer.verifying_key().as_bytes(),
        )
        .unwrap();
        let pinned = crate::authenticate_pinned_signed_hol_artifact(&expected, &artifact).unwrap();
        let receiver = Kernel::ephemeral();
        let mut target = receiver.open_hol(covalence_nucleus::AllowAll).unwrap();
        let accepted =
            crate::trust_and_receive_pinned_signed_hol_artifact(&mut target, pinned).unwrap();
        assert_eq!(accepted.context_id(), 0);
        assert_eq!(accepted.conclusion_id(), 8);
    }

    #[test]
    fn export_before_persist_is_rejected_without_appending() {
        let mut state = GuestState::new();
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
            state.export_theorem_conclusion(
                Resource::new_borrow(PLAN_REP),
                namespace,
                0,
                theorem,
                None,
            ),
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

    #[test]
    fn managed_success_retains_an_inspectable_receiver_not_authority() {
        let recipe = vec![
            Recipe::BoolType,
            Recipe::Bound { index: 0, ty: 0 },
            Recipe::Lambda {
                parameter_type: 0,
                body: 1,
            },
            Recipe::Bool(true),
            Recipe::EmptyContext,
            Recipe::Beta {
                context: 4,
                abstraction: 2,
                argument: 3,
            },
            Recipe::Persist { theorem: 5 },
            Recipe::Namespace { name: None },
            Recipe::ExportContext {
                namespace: 7,
                export: 0,
                context: 4,
                name: None,
            },
            Recipe::ExportTheorem {
                namespace: 7,
                export: 1,
                theorem: 5,
                name: None,
            },
        ];
        let kernel = Kernel::ephemeral();
        let artifact = replay(&kernel, &recipe, 7).unwrap();
        let mut directory = Repl::new(kernel.verifying_key().as_bytes()).unwrap();
        let managed = retain_signed_hol_guest_artifact(&kernel, &mut directory, artifact).unwrap();

        assert_eq!(directory.active().unwrap(), Some(managed.connection()));
        assert_eq!(managed.received().context_id(), 0);
        assert_eq!(managed.received().conclusion_id(), 8);
        assert!(
            directory
                .get_mut(managed.connection())
                .unwrap()
                .hol_mut()
                .is_ok()
        );
        let state = directory
            .inspect_state("SELECT kernel_id, protocol, remote_connection_id FROM repl_connection")
            .unwrap();
        assert_eq!(
            state.rows,
            vec![vec![
                crate::Value::Integer(0),
                crate::Value::Text("nucleus/hol".into()),
                crate::Value::Null,
            ]]
        );
        let columns = directory
            .inspect_state("SELECT name FROM pragma_table_info('repl_connection') ORDER BY cid")
            .unwrap();
        assert!(!columns.rows.iter().flatten().any(|value| {
            matches!(value, crate::Value::Text(name) if matches!(name.as_str(), "image" | "signature" | "private_key" | "session"))
        }));
    }

    #[test]
    fn managed_component_failure_does_not_change_caller_state() {
        let kernel = Kernel::ephemeral();
        let mut directory = Repl::new(kernel.verifying_key().as_bytes()).unwrap();
        let error = run_managed_hol_proof_component(
            &kernel,
            &mut directory,
            b"not a component",
            WasmtimeComponentLimits::default(),
        )
        .err()
        .unwrap();
        assert_eq!(error.phase(), "component-executed");
        assert!(directory.connections().unwrap().is_empty());
    }
}
