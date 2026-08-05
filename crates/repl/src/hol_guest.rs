//! Native host for the bounded HOL proof component contract.

use std::{
    collections::{HashMap, HashSet},
    error::Error as StdError,
    fmt,
};

use covalence_lib_hash::O256;
use covalence_nucleus::Kernel;
use covalence_proton::{
    WasmtimeComponentLimits, WasmtimeComponentRuntime, WasmtimeRuntimeError, WasmtimeStore,
    wasmtime,
};
use wasmtime::component::{Component, HasSelf, Linker, Resource};

use crate::hol_guest_plan::{
    MAX_RECIPE_NAME_BYTES, MAX_RECIPE_NODES, RecipeNode as Recipe, RecipeSort as Sort,
    SealedHolProofRecipe,
};
use crate::{
    ConnectionId, HolProofComponentExecutor, KernelId, LocalConnection, ReceivedHolSnapshot, Repl,
    SignedHolArtifact, Value as SqlValue, authenticate_pinned_signed_hol_artifact,
    trust_and_receive_pinned_signed_hol_artifact,
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
        if self.recipe.len() >= MAX_RECIPE_NODES {
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
        if self.recipe.len() >= MAX_RECIPE_NODES {
            return Err(AppendError::ResourceLimit);
        }
        self.recipe.push(recipe);
        self.sorts.push(sort);
        Ok(())
    }

    fn name(name: Option<String>) -> Result<Option<String>, AppendError> {
        if name
            .as_ref()
            .is_some_and(|name| name.len() > MAX_RECIPE_NAME_BYTES)
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

    fn prove_eta(
        &mut self,
        plan: Resource<ProofPlan>,
        context: Resource<ContextNode>,
        function: Resource<TermNode>,
    ) -> Result<Resource<TheoremNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&context, Sort::Context))
            .and_then(|context| {
                self.node(&function, Sort::Term)
                    .map(|function| (context, function))
            })
            .and_then(|(context, function)| {
                self.append(Recipe::Eta { context, function }, Sort::Theorem)
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

/// Executes one untrusted component and returns only its bounded sealed plan.
///
/// The returned value contains no theorem, database, signer, or kernel
/// capability and can be transported through an untrusted executor boundary.
///
/// # Errors
///
/// Returns an error if component validation or execution fails, the guest
/// aborts, a resource bound is exceeded, or its returned namespace is invalid.
fn collect_hol_proof_component(
    bytes: &[u8],
    limits: WasmtimeComponentLimits,
) -> Result<SealedHolProofRecipe, HolGuestError> {
    let runtime = WasmtimeComponentRuntime::new(limits).map_err(HolGuestError::Runtime)?;
    let component = runtime.component(bytes).map_err(HolGuestError::Runtime)?;
    collect_prepared_hol_proof_component(&runtime, &component)
}

fn collect_prepared_hol_proof_component(
    runtime: &WasmtimeComponentRuntime,
    component: &wasmtime::component::Component,
) -> Result<SealedHolProofRecipe, HolGuestError> {
    let mut linker: Linker<WasmtimeStore<GuestState>> = Linker::new(runtime.engine());
    bindings::HolProofGuest::add_to_linker::<_, HasSelf<GuestState>>(&mut linker, |state| {
        &mut state.data
    })
    .map_err(HolGuestError::Wasmtime)?;
    let mut store = runtime
        .store(GuestState::new())
        .map_err(HolGuestError::Runtime)?;
    let guest = bindings::HolProofGuest::instantiate(&mut store, component, &linker)
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
    SealedHolProofRecipe::seal(store.data().data.recipe.clone(), selected_namespace)
        .map_err(|error| HolGuestError::Replay(error.to_string()))
}

/// A locally bounded and compiled HOL proof component.
///
/// Preparation is the only operation which accepts component bytes. Repeated
/// collection instantiates the already compiled component in fresh bounded
/// stores and yields only authority-free sealed recipes.
pub struct PreparedHolProofComponent {
    digest: O256,
    runtime: WasmtimeComponentRuntime,
    component: Component,
}

impl PreparedHolProofComponent {
    /// Validates and compiles exact component bytes under explicit limits.
    ///
    /// # Errors
    ///
    /// Returns an error if the byte bound, Wasmtime configuration, validation,
    /// or compilation fails.
    pub fn prepare(
        expected: O256,
        bytes: &[u8],
        limits: WasmtimeComponentLimits,
    ) -> Result<Self, HolGuestError> {
        let actual = O256::from_bytes(bytes);
        if actual != expected {
            return Err(HolGuestError::ComponentHashMismatch { expected, actual });
        }
        let runtime = WasmtimeComponentRuntime::new(limits).map_err(HolGuestError::Runtime)?;
        let component = runtime.component(bytes).map_err(HolGuestError::Runtime)?;
        Ok(Self {
            digest: actual,
            runtime,
            component,
        })
    }

    /// Returns the exact content digest remote signed commands may select.
    #[must_use]
    pub const fn digest(&self) -> O256 {
        self.digest
    }

    /// Runs this precompiled component in a fresh bounded store and returns its
    /// untrusted sealed recipe without replay or signing authority.
    ///
    /// # Errors
    ///
    /// Returns an error for instantiation, execution, guest, or recipe failure.
    pub fn collect(&self) -> Result<SealedHolProofRecipe, HolGuestError> {
        collect_prepared_hol_proof_component(&self.runtime, &self.component)
    }
}

/// In-process native prototype mapping exact digests to precompiled guests.
///
/// This is deliberately an upper-layer convenience, not an isolation boundary:
/// Wasmtime and its JIT still share the key-holding process. The executor API
/// is authority-free so a later subprocess or Worker can replace this type
/// without changing signed service semantics or checked replay.
#[derive(Default)]
pub struct PrecompiledHolProofComponentExecutor {
    components: HashMap<O256, PreparedHolProofComponent>,
}

impl PrecompiledHolProofComponentExecutor {
    /// Creates an empty local allowlist.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds one already validated and compiled component before serving.
    ///
    /// # Errors
    ///
    /// Rejects a duplicate digest instead of silently replacing executable
    /// configuration.
    pub fn insert(&mut self, component: PreparedHolProofComponent) -> Result<O256, HolGuestError> {
        let digest = component.digest();
        if self.components.contains_key(&digest) {
            return Err(HolGuestError::DuplicateComponent(digest));
        }
        self.components.insert(digest, component);
        Ok(digest)
    }

    /// Returns the number of locally provisioned exact components.
    #[must_use]
    pub fn len(&self) -> usize {
        self.components.len()
    }

    /// Reports whether no component has been provisioned.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.components.is_empty()
    }
}

impl HolProofComponentExecutor for PrecompiledHolProofComponentExecutor {
    fn contains(&self, component: O256) -> bool {
        self.components.contains_key(&component)
    }

    fn execute(&mut self, component: O256) -> Result<SealedHolProofRecipe, String> {
        self.components
            .get(&component)
            .ok_or_else(|| "HOL proof component is not provisioned".to_owned())?
            .collect()
            .map_err(|error| error.to_string())
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
    collect_hol_proof_component(bytes, limits)?
        .replay(kernel)
        .map_err(|error| HolGuestError::Replay(error.to_string()))
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

    /// Returns receiver-local coordinates for the imported snapshot.
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
/// Component execution occurs in a fresh disposable producer connection. Only after checked
/// replay, signing, key matching, detached validation, trust, and import succeed is the fresh
/// receiver inserted into `directory`. The directory's existing selection is preserved unless
/// it was empty, in which case ordinary [`Repl::insert`] behavior selects the receiver.
///
/// # Errors
///
/// Returns the first high-level boundary which failed. The caller's directory is not mutated
/// before the complete receive path succeeds.
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
/// This split form lets a caller durably present the signed bytes before mutating its REPL
/// directory. Both the caller-provided kernel key and the independently recorded local endpoint
/// key must match the signed artifact before the ordinary authenticate/validate/trust/import
/// path runs against a disposable receiver.
///
/// # Errors
///
/// Returns the first high-level boundary which failed. No receiver is inserted until the full
/// receive path succeeds.
pub fn retain_signed_hol_guest_artifact(
    kernel: &Kernel,
    directory: &mut Repl<LocalConnection>,
    artifact: SignedHolArtifact,
) -> Result<ManagedHolGuestResult, ManagedHolGuestError> {
    let verifying_key = kernel.verifying_key();
    let expected = verifying_key.as_bytes();
    if artifact.public_key() != expected {
        return Err(ManagedHolGuestError::invalid(
            "artifact-authenticated",
            "artifact signer does not match the caller-provided kernel",
        ));
    }
    let recorded = directory
        .inspect_state("SELECT public_key FROM repl_kernel WHERE kernel_id = 0")
        .map_err(|error| ManagedHolGuestError::at("local-key-loaded", error))?;
    if recorded.rows.as_slice() != [vec![SqlValue::Blob(expected.to_vec())]] {
        return Err(ManagedHolGuestError::invalid(
            "local-key-loaded",
            "REPL local endpoint key does not match the caller-provided kernel",
        ));
    }

    let expected_identity = directory
        .expected_kernel_identity(KernelId::LOCAL)
        .map_err(|error| ManagedHolGuestError::at("local-key-loaded", error))?;
    let pinned = authenticate_pinned_signed_hol_artifact(&expected_identity, &artifact)
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

    fn invalid(phase: &'static str, message: &'static str) -> Self {
        Self {
            phase,
            message: message.to_owned(),
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
    ComponentHashMismatch { expected: O256, actual: O256 },
    DuplicateComponent(O256),
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
            Self::ComponentHashMismatch { expected, actual } => {
                write!(
                    formatter,
                    "component hash {actual} does not match configured {expected}"
                )
            }
            Self::DuplicateComponent(component) => {
                write!(
                    formatter,
                    "HOL proof component {component} is already provisioned"
                )
            }
        }
    }
}

impl StdError for HolGuestError {}

#[cfg(test)]
mod tests {
    use super::*;

    fn closed_beta_recipe() -> Vec<Recipe> {
        vec![
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
        ]
    }

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
        let context = state.empty_context(Resource::new_borrow(PLAN_REP)).unwrap();
        assert!(matches!(
            state.prove_eta(
                Resource::new_borrow(PLAN_REP),
                Resource::new_borrow(context.rep()),
                Resource::new_borrow(context.rep()),
            ),
            Err(AppendError::InvalidDependency)
        ));
    }

    #[test]
    fn recipe_and_name_bounds_are_enforced_before_append() {
        assert_eq!(
            GuestState::name(Some("x".repeat(MAX_RECIPE_NAME_BYTES + 1))),
            Err(AppendError::ResourceLimit)
        );
        let mut state = GuestState::new();
        for _ in 0..MAX_RECIPE_NODES {
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
        let recipe = closed_beta_recipe();
        let producer = Kernel::ephemeral();
        let artifact = SealedHolProofRecipe::seal(recipe, 7)
            .unwrap()
            .replay(&producer)
            .unwrap();
        assert_eq!(artifact.namespace_id(), 1);
        assert!(artifact.image().len() <= crate::MAX_IMAGE_BYTES);

        let receiver = Kernel::ephemeral();
        let mut target = receiver.open_hol(covalence_nucleus::AllowAll).unwrap();
        let expected = crate::ExpectedKernelIdentity::from_public_key(
            crate::KernelId::LOCAL,
            producer.verifying_key().as_bytes(),
        )
        .unwrap();
        let pinned = crate::authenticate_pinned_signed_hol_artifact(&expected, &artifact).unwrap();
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
    #[allow(clippy::too_many_lines)]
    fn configured_real_eta_component_exports_the_named_eta_graph() {
        let Some(component) = std::env::var_os("COVALENCE_HOL_ETA_GUEST_COMPONENT") else {
            return;
        };
        let bytes = std::fs::read(component).unwrap();
        let artifact = run_hol_proof_component(
            &Kernel::ephemeral(),
            &bytes,
            WasmtimeComponentLimits::default(),
        )
        .unwrap();
        let image_bytes = covalence_neutron::Bytes::copy_from_slice(artifact.image());
        let image = covalence_neutron::Connection::deserialize(&image_bytes).unwrap();
        let sqlite = image.sqlite();
        let namespace = artifact.namespace_id();

        assert_eq!(
            sqlite
                .query_row(
                    "SELECT parent_namespace_id, name FROM hol_namespace WHERE namespace_id = ?1",
                    [namespace],
                    |row| Ok((row.get::<_, i64>(0)?, row.get::<_, String>(1)?)),
                )
                .unwrap(),
            (0, "eta-demo".to_owned())
        );
        let (context, context_sort, context_name) = sqlite
            .query_row(
                "SELECT local_id, sort, name FROM hol_namespace_export
                 WHERE namespace_id = ?1 AND export_id = 0",
                [namespace],
                |row| {
                    Ok((
                        row.get::<_, i64>(0)?,
                        row.get::<_, String>(1)?,
                        row.get::<_, String>(2)?,
                    ))
                },
            )
            .unwrap();
        assert_eq!(
            (context, context_sort.as_str(), context_name.as_str()),
            (0, "context", "empty_context")
        );
        let (conclusion, conclusion_sort, conclusion_name) = sqlite
            .query_row(
                "SELECT local_id, sort, name FROM hol_namespace_export
                 WHERE namespace_id = ?1 AND export_id = 1",
                [namespace],
                |row| {
                    Ok((
                        row.get::<_, i64>(0)?,
                        row.get::<_, String>(1)?,
                        row.get::<_, String>(2)?,
                    ))
                },
            )
            .unwrap();
        assert_eq!(
            (conclusion_sort.as_str(), conclusion_name.as_str()),
            ("term", "identity_eta")
        );
        assert!(
            sqlite
                .query_row(
                    "SELECT EXISTS(SELECT 1 FROM hol_judgement WHERE ctx_id = ?1 AND term_id = ?2)",
                    [context, conclusion],
                    |row| row.get::<_, bool>(0),
                )
                .unwrap()
        );

        let (equality_tag, eta_lambda, identity) = sqlite
            .query_row(
                "SELECT tag, lhs, rhs FROM hol_node WHERE node_id = ?1",
                [conclusion],
                |row| {
                    Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, i64>(2)?,
                    ))
                },
            )
            .unwrap();
        assert_eq!(equality_tag, "MEQ");
        let (eta_tag, parameter_type, application, eta_type) = sqlite
            .query_row(
                "SELECT tag, lhs, rhs, ty FROM hol_node WHERE node_id = ?1",
                [eta_lambda],
                |row| {
                    Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, i64>(2)?,
                        row.get::<_, i64>(3)?,
                    ))
                },
            )
            .unwrap();
        assert_eq!(eta_tag, "MLAM");
        let (application_tag, application_function, application_argument) = sqlite
            .query_row(
                "SELECT tag, lhs, rhs FROM hol_node WHERE node_id = ?1",
                [application],
                |row| {
                    Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, i64>(2)?,
                    ))
                },
            )
            .unwrap();
        assert_eq!(
            (application_tag.as_str(), application_function),
            ("MAPP", identity)
        );
        let (argument_tag, argument_index, argument_type) = sqlite
            .query_row(
                "SELECT tag, lhs, ty FROM hol_node WHERE node_id = ?1",
                [application_argument],
                |row| {
                    Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, i64>(2)?,
                    ))
                },
            )
            .unwrap();
        assert_eq!(
            (argument_tag.as_str(), argument_index, argument_type),
            ("MBV", 0, parameter_type)
        );
        let (identity_tag, identity_parameter_type, identity_body, identity_type) = sqlite
            .query_row(
                "SELECT tag, lhs, rhs, ty FROM hol_node WHERE node_id = ?1",
                [identity],
                |row| {
                    Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, i64>(2)?,
                        row.get::<_, i64>(3)?,
                    ))
                },
            )
            .unwrap();
        assert_eq!(
            (
                identity_tag.as_str(),
                identity_parameter_type,
                identity_type
            ),
            ("MLAM", parameter_type, eta_type)
        );
        let (body_tag, body_index, body_type) = sqlite
            .query_row(
                "SELECT tag, lhs, ty FROM hol_node WHERE node_id = ?1",
                [identity_body],
                |row| {
                    Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, i64>(2)?,
                    ))
                },
            )
            .unwrap();
        assert_eq!(
            (body_tag.as_str(), body_index, body_type),
            ("MBV", 0, parameter_type)
        );
    }

    #[test]
    fn preparation_rejects_hash_mismatch_invalid_and_oversized_before_serving() {
        let invalid = b"not a component";
        let actual = O256::from_bytes(invalid);
        let expected = O256::from_bytes(b"configured component");
        assert!(matches!(
            PreparedHolProofComponent::prepare(
                expected,
                invalid,
                WasmtimeComponentLimits::default(),
            ),
            Err(HolGuestError::ComponentHashMismatch {
                expected: rejected_expected,
                actual: rejected_actual,
            }) if rejected_expected == expected && rejected_actual == actual
        ));
        assert!(matches!(
            PreparedHolProofComponent::prepare(actual, invalid, WasmtimeComponentLimits::default(),),
            Err(HolGuestError::Runtime(WasmtimeRuntimeError::Component(_)))
        ));

        let limits = WasmtimeComponentLimits {
            component_bytes: 8,
            ..WasmtimeComponentLimits::default()
        };
        let oversized = [0; 9];
        assert!(matches!(
            PreparedHolProofComponent::prepare(O256::from_bytes(oversized), &oversized, limits),
            Err(HolGuestError::Runtime(
                WasmtimeRuntimeError::ComponentTooLarge {
                    size: 9,
                    maximum: 8,
                }
            ))
        ));
    }

    #[test]
    fn managed_success_retains_a_live_receiver_for_post_return_reread() {
        let recipe = closed_beta_recipe();
        let kernel = Kernel::ephemeral();
        let artifact = SealedHolProofRecipe::seal(recipe, 7)
            .unwrap()
            .replay(&kernel)
            .unwrap();
        let mut directory = Repl::new(kernel.verifying_key().as_bytes()).unwrap();
        let managed = retain_signed_hol_guest_artifact(&kernel, &mut directory, artifact).unwrap();

        assert_eq!(directory.active().unwrap(), Some(managed.connection()));
        let expected = directory
            .expected_kernel_identity(crate::KernelId::LOCAL)
            .unwrap();
        let pinned =
            crate::authenticate_pinned_signed_hol_artifact(&expected, managed.artifact()).unwrap();
        let target = directory
            .get_mut(managed.connection())
            .unwrap()
            .hol_mut()
            .unwrap();
        let reread = crate::trust_and_receive_pinned_signed_hol_artifact(target, pinned).unwrap();
        assert_eq!(reread.context_id(), managed.received().context_id());
        assert_eq!(reread.conclusion_id(), managed.received().conclusion_id());
    }

    #[test]
    fn managed_failure_does_not_mutate_the_caller_directory() {
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
        assert!(
            directory
                .inspect_state("SELECT connection_id FROM repl_connection")
                .unwrap()
                .rows
                .is_empty()
        );
    }

    #[test]
    fn managed_receive_requires_the_directory_local_key() {
        let recipe = closed_beta_recipe();
        let kernel = Kernel::ephemeral();
        let artifact = SealedHolProofRecipe::seal(recipe, 7)
            .unwrap()
            .replay(&kernel)
            .unwrap();
        let other = Kernel::ephemeral();
        let mut directory = Repl::new(other.verifying_key().as_bytes()).unwrap();

        let error = retain_signed_hol_guest_artifact(&kernel, &mut directory, artifact)
            .err()
            .unwrap();
        assert_eq!(error.phase(), "local-key-loaded");
        assert!(
            directory
                .inspect_state("SELECT connection_id FROM repl_connection")
                .unwrap()
                .rows
                .is_empty()
        );
    }
}
