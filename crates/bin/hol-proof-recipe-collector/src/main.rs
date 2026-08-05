//! Authority-free Wasmtime host which emits one bounded HOL proof recipe frame.

#[cfg(not(target_arch = "wasm32"))]
mod native {

    use std::collections::HashSet;
    use std::error::Error;
    use std::io::{self, Read, Write};

    use covalence_lib_hash::O256;
    use covalence_proton::{
        WasmtimeComponentLimits, WasmtimeComponentRuntime, WasmtimeStore, wasmtime,
    };
    use wasmtime::component::{HasSelf, Linker, Resource};

    const INPUT_MAGIC: &[u8; 8] = b"CVHPIN01";
    const OUTPUT_MAGIC: &[u8; 8] = b"CVHPOU01";
    const RECIPE_VERSION: u8 = 0;
    const MAX_RECIPE_BYTES: usize = 64 * 1024;
    const MAX_RECIPE_NODES: usize = 128;
    const MAX_RECIPE_NAME_BYTES: usize = 256;
    const MAX_DIAGNOSTIC_BYTES: usize = 1024;
    const PLAN_REP: u32 = 1;

    mod bindings {
        use covalence_proton::wasmtime;

        wasmtime::component::bindgen!({
            path: "../../nucleus/protocol/hol-proof-guest.wit",
            world: "hol-proof-guest",
            wasmtime_crate: covalence_proton::wasmtime,
        });
    }

    use bindings::covalence::hol_proof_guest::host::{
        AppendError, ContextNode, Host, HostContextNode, HostNamespaceNode, HostProofPlan,
        HostTermNode, HostTheoremNode, HostTypeNode, NamespaceNode, ProofPlan, TermNode,
        TheoremNode, TypeNode,
    };

    #[derive(Clone, Copy, Eq, PartialEq)]
    enum Sort {
        Type,
        Term,
        Context,
        Theorem,
        Namespace,
    }

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
            (self.sorts.get(index) == Some(&sort))
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
            let rep =
                u32::try_from(self.recipe.len() + 2).map_err(|_| AppendError::ResourceLimit)?;
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
        fn bool_type(
            &mut self,
            plan: Resource<ProofPlan>,
        ) -> Result<Resource<TypeNode>, AppendError> {
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

    fn encode_index(bytes: &mut Vec<u8>, index: usize) -> Result<(), Box<dyn Error>> {
        bytes.extend_from_slice(&u16::try_from(index)?.to_be_bytes());
        Ok(())
    }

    fn encode_name(bytes: &mut Vec<u8>, name: Option<&str>) -> Result<(), Box<dyn Error>> {
        match name {
            None => bytes.push(0),
            Some(name) => {
                if name.len() > MAX_RECIPE_NAME_BYTES {
                    return Err("recipe name exceeds byte limit".into());
                }
                bytes.push(1);
                bytes.extend_from_slice(&u16::try_from(name.len())?.to_be_bytes());
                bytes.extend_from_slice(name.as_bytes());
            }
        }
        Ok(())
    }

    fn encode_recipe(
        nodes: &[Recipe],
        selected_namespace: usize,
    ) -> Result<Vec<u8>, Box<dyn Error>> {
        let mut bytes = Vec::new();
        bytes.push(RECIPE_VERSION);
        bytes.extend_from_slice(&u16::try_from(nodes.len())?.to_be_bytes());
        bytes.extend_from_slice(&u16::try_from(selected_namespace)?.to_be_bytes());
        for node in nodes {
            match node {
                Recipe::BoolType => bytes.push(0),
                Recipe::Bound { index, ty } => {
                    bytes.push(1);
                    bytes.extend_from_slice(&index.to_be_bytes());
                    encode_index(&mut bytes, *ty)?;
                }
                Recipe::Lambda {
                    parameter_type,
                    body,
                } => {
                    bytes.push(2);
                    encode_index(&mut bytes, *parameter_type)?;
                    encode_index(&mut bytes, *body)?;
                }
                Recipe::Bool(value) => {
                    bytes.push(3);
                    bytes.push(u8::from(*value));
                }
                Recipe::EmptyContext => bytes.push(4),
                Recipe::Beta {
                    context,
                    abstraction,
                    argument,
                } => {
                    bytes.push(5);
                    encode_index(&mut bytes, *context)?;
                    encode_index(&mut bytes, *abstraction)?;
                    encode_index(&mut bytes, *argument)?;
                }
                Recipe::Persist { theorem } => {
                    bytes.push(6);
                    encode_index(&mut bytes, *theorem)?;
                }
                Recipe::Namespace { name } => {
                    bytes.push(7);
                    encode_name(&mut bytes, name.as_deref())?;
                }
                Recipe::ExportTheorem {
                    namespace,
                    export,
                    theorem,
                    name,
                } => {
                    bytes.push(8);
                    encode_index(&mut bytes, *namespace)?;
                    bytes.extend_from_slice(&export.to_be_bytes());
                    encode_index(&mut bytes, *theorem)?;
                    encode_name(&mut bytes, name.as_deref())?;
                }
                Recipe::ExportContext {
                    namespace,
                    export,
                    context,
                    name,
                } => {
                    bytes.push(9);
                    encode_index(&mut bytes, *namespace)?;
                    bytes.extend_from_slice(&export.to_be_bytes());
                    encode_index(&mut bytes, *context)?;
                    encode_name(&mut bytes, name.as_deref())?;
                }
            }
            if bytes.len() > MAX_RECIPE_BYTES {
                return Err("sealed recipe exceeds byte limit".into());
            }
        }
        Ok(bytes)
    }

    fn collect(
        component: &[u8],
        limits: WasmtimeComponentLimits,
    ) -> Result<Vec<u8>, Box<dyn Error>> {
        let runtime = WasmtimeComponentRuntime::new(limits)?;
        let component = runtime.component(component)?;
        let mut linker: Linker<WasmtimeStore<GuestState>> = Linker::new(runtime.engine());
        bindings::HolProofGuest::add_to_linker::<_, HasSelf<GuestState>>(&mut linker, |state| {
            &mut state.data
        })?;
        let mut store = runtime.store(GuestState::new())?;
        let guest = bindings::HolProofGuest::instantiate(&mut store, &component, &linker)?;
        let selected = guest
            .covalence_hol_proof_guest_guest()
            .call_build(&mut store, Resource::new_borrow(PLAN_REP))?
            .map_err(|_| "proof guest aborted")?;
        let selected = store
            .data()
            .data
            .node(&selected, Sort::Namespace)
            .map_err(|_| "proof guest returned an invalid namespace")?;
        store.data_mut().data.sealed = true;
        encode_recipe(&store.data().data.recipe, selected)
    }

    fn decode_input<'a>(
        bytes: &'a [u8],
        limits: &WasmtimeComponentLimits,
    ) -> Result<&'a [u8], Box<dyn Error>> {
        let maximum = 8 + 32 + 4 + limits.component_bytes;
        if bytes.len() > maximum {
            return Err("collector input exceeds byte limit".into());
        }
        if bytes.get(..8) != Some(INPUT_MAGIC) {
            return Err("invalid collector input magic".into());
        }
        let expected: &[u8; 32] = bytes
            .get(8..40)
            .ok_or("truncated collector digest")?
            .try_into()
            .expect("exact digest width");
        let length = u32::from_be_bytes(
            bytes
                .get(40..44)
                .ok_or("truncated collector length")?
                .try_into()
                .expect("exact length width"),
        );
        let length = usize::try_from(length)?;
        if length > limits.component_bytes {
            return Err("component exceeds collector byte limit".into());
        }
        let component = bytes.get(44..).ok_or("truncated collector component")?;
        if component.len() != length {
            return Err("collector input length is not exact".into());
        }
        if O256::from_bytes(component).as_ref() != expected {
            return Err("component hash does not match collector input".into());
        }
        Ok(component)
    }

    fn read_input() -> Result<Vec<u8>, Box<dyn Error>> {
        let limits = WasmtimeComponentLimits::default();
        let maximum = 8 + 32 + 4 + limits.component_bytes;
        let mut bytes = Vec::new();
        io::stdin()
            .lock()
            .take(u64::try_from(maximum + 1)?)
            .read_to_end(&mut bytes)?;
        let component = decode_input(&bytes, &limits)?;
        collect(component, limits)
    }

    fn write_success(recipe: &[u8]) -> io::Result<()> {
        let mut output = io::stdout().lock();
        output.write_all(OUTPUT_MAGIC)?;
        output.write_all(&[0])?;
        output.write_all(
            &u32::try_from(recipe.len())
                .expect("bounded recipe")
                .to_be_bytes(),
        )?;
        output.write_all(recipe)?;
        output.flush()
    }

    fn write_error(error: &dyn Error) -> io::Result<()> {
        let diagnostic = error.to_string();
        let diagnostic = diagnostic.as_bytes();
        let diagnostic = &diagnostic[..diagnostic.len().min(MAX_DIAGNOSTIC_BYTES)];
        let mut output = io::stdout().lock();
        output.write_all(OUTPUT_MAGIC)?;
        output.write_all(&[1])?;
        output.write_all(
            &u32::try_from(diagnostic.len())
                .expect("bounded diagnostic")
                .to_be_bytes(),
        )?;
        output.write_all(diagnostic)?;
        output.flush()
    }

    pub fn main() {
        match read_input() {
            Ok(recipe) => {
                if write_success(&recipe).is_err() {
                    std::process::exit(2);
                }
            }
            Err(error) => {
                if write_error(error.as_ref()).is_err() {
                    std::process::exit(2);
                }
                std::process::exit(1);
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        fn input(component: &[u8]) -> Vec<u8> {
            let mut bytes = Vec::new();
            bytes.extend_from_slice(INPUT_MAGIC);
            bytes.extend_from_slice(O256::from_bytes(component).as_ref());
            bytes.extend_from_slice(&u32::try_from(component.len()).unwrap().to_be_bytes());
            bytes.extend_from_slice(component);
            bytes
        }

        #[test]
        fn input_frame_binds_an_exact_bounded_component() {
            let limits = WasmtimeComponentLimits {
                component_bytes: 16,
                ..WasmtimeComponentLimits::default()
            };
            let bytes = input(b"component");
            assert_eq!(decode_input(&bytes, &limits).unwrap(), b"component");

            let mut trailing = bytes.clone();
            trailing.push(0);
            assert!(decode_input(&trailing, &limits).is_err());
            let mut wrong_hash = bytes.clone();
            wrong_hash[8] ^= 1;
            assert!(decode_input(&wrong_hash, &limits).is_err());
            assert!(decode_input(&input(&[0; 17]), &limits).is_err());
        }

        #[test]
        fn closed_beta_recipe_encoding_is_stable() {
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
                Recipe::ExportTheorem {
                    namespace: 7,
                    export: 0,
                    theorem: 5,
                    name: None,
                },
                Recipe::ExportContext {
                    namespace: 7,
                    export: 1,
                    context: 4,
                    name: None,
                },
            ];
            assert_eq!(
                encode_recipe(&recipe, 7).unwrap(),
                [
                    0, 0, 10, 0, 7, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 3, 1, 4, 5, 0, 4, 0, 2,
                    0, 3, 6, 0, 5, 7, 0, 8, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 9, 0, 7, 0, 0,
                    0, 0, 0, 0, 0, 1, 0, 4, 0,
                ]
            );
        }

        #[test]
        fn configured_real_component_collects_a_bounded_recipe() {
            let Some(component) = std::env::var_os("COVALENCE_HOL_GUEST_COMPONENT") else {
                return;
            };
            let bytes = std::fs::read(component).unwrap();
            let recipe = collect(&bytes, WasmtimeComponentLimits::default()).unwrap();
            assert!(!recipe.is_empty());
            assert!(recipe.len() <= MAX_RECIPE_BYTES);
            assert_eq!(recipe[0], RECIPE_VERSION);
        }
    }
}

#[cfg(not(target_arch = "wasm32"))]
fn main() {
    native::main();
}

// The collector itself is a native process boundary. Keeping a no-op Wasm
// entry point lets workspace-wide target checks verify its portable dependencies.
#[cfg(target_arch = "wasm32")]
fn main() {}
