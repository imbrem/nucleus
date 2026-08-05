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
    MAX_CONTEXT_MEMBERS, MAX_RECIPE_NAME_BYTES, MAX_RECIPE_NODES, RecipeNode as Recipe,
    RecipeSort as Sort, SealedHolProofRecipe,
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
    AppendError, ContextEquivalenceNode, ContextImplicationNode, ContextNode, ContextPathNode,
    ContextUnionNode, ConversionNode, Host, HostContextEquivalenceNode, HostContextImplicationNode,
    HostContextNode, HostContextPathNode, HostContextUnionNode, HostConversionNode,
    HostNamespaceNode, HostProofPlan, HostTermInstantiationMapNode, HostTermNode, HostTheoremNode,
    HostTheoremWitnessListNode, HostTypeInstantiationMapNode, HostTypeNode, NamespaceNode,
    ProofPlan, TermInstantiationMapNode, TermNode, TheoremNode, TheoremWitnessListNode,
    TypeInstantiationMapNode, TypeNode,
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

    fn term_map_contains(&self, mut map: usize, variable: usize) -> bool {
        loop {
            match self.recipe.get(map) {
                Some(Recipe::ExtendTermInstantiationMap {
                    base,
                    variable: key,
                    ..
                }) => {
                    if *key == variable {
                        return true;
                    }
                    map = *base;
                }
                _ => return false,
            }
        }
    }

    fn type_map_contains(&self, mut map: usize, variable: usize) -> bool {
        loop {
            match self.recipe.get(map) {
                Some(Recipe::ExtendTypeInstantiationMap {
                    base,
                    variable: key,
                    ..
                }) => {
                    if *key == variable {
                        return true;
                    }
                    map = *base;
                }
                _ => return false,
            }
        }
    }

    fn context_depth(&self, mut context: usize) -> usize {
        let mut depth = 0;
        while let Some(Recipe::ExtendContext { base, .. }) = self.recipe.get(context) {
            depth += 1;
            context = *base;
        }
        depth
    }

    fn theorem_witness_list_depth(&self, mut list: usize) -> usize {
        let mut depth = 0;
        while let Some(Recipe::ExtendTheoremWitnessList { base, .. }) = self.recipe.get(list) {
            depth += 1;
            list = *base;
        }
        depth
    }

    fn context_path_depth(&self, mut path: usize) -> usize {
        let mut depth = 1;
        while let Some(Recipe::ExtendContextPath { base, .. }) = self.recipe.get(path) {
            depth += 1;
            path = *base;
        }
        depth
    }
}

impl Host for GuestState {}

impl HostProofPlan for GuestState {
    fn bool_type(&mut self, plan: Resource<ProofPlan>) -> Result<Resource<TypeNode>, AppendError> {
        Self::plan(&plan).and_then(|()| self.append(Recipe::BoolType, Sort::Type))
    }

    fn free_type(
        &mut self,
        plan: Resource<ProofPlan>,
        symbol: i64,
    ) -> Result<Resource<TypeNode>, AppendError> {
        Self::plan(&plan).and_then(|()| self.append(Recipe::FreeType { symbol }, Sort::Type))
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

    fn free_term(
        &mut self,
        plan: Resource<ProofPlan>,
        symbol: i64,
        ty: Resource<TypeNode>,
    ) -> Result<Resource<TermNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&ty, Sort::Type))
            .and_then(|ty| self.append(Recipe::FreeTerm { symbol, ty }, Sort::Term))
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

    fn application(
        &mut self,
        plan: Resource<ProofPlan>,
        function: Resource<TermNode>,
        argument: Resource<TermNode>,
    ) -> Result<Resource<TermNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&function, Sort::Term))
            .and_then(|function| {
                self.node(&argument, Sort::Term)
                    .map(|argument| (function, argument))
            })
            .and_then(|(function, argument)| {
                self.append(Recipe::Application { function, argument }, Sort::Term)
            })
    }

    fn epsilon(
        &mut self,
        plan: Resource<ProofPlan>,
        predicate: Resource<TermNode>,
    ) -> Result<Resource<TermNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&predicate, Sort::Term))
            .and_then(|predicate| self.append(Recipe::Epsilon { predicate }, Sort::Term))
    }

    fn empty_context(
        &mut self,
        plan: Resource<ProofPlan>,
    ) -> Result<Resource<ContextNode>, AppendError> {
        Self::plan(&plan).and_then(|()| self.append(Recipe::EmptyContext, Sort::Context))
    }

    fn extend_context(
        &mut self,
        plan: Resource<ProofPlan>,
        base: Resource<ContextNode>,
        member: Resource<TermNode>,
    ) -> Result<Resource<ContextNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&base, Sort::Context))
            .and_then(|base| self.node(&member, Sort::Term).map(|member| (base, member)))
            .and_then(|(base, member)| {
                if self.context_depth(base) >= MAX_CONTEXT_MEMBERS {
                    return Err(AppendError::ResourceLimit);
                }
                self.append(Recipe::ExtendContext { base, member }, Sort::Context)
            })
    }

    fn prove_hypothesis(
        &mut self,
        plan: Resource<ProofPlan>,
        context: Resource<ContextNode>,
        term: Resource<TermNode>,
    ) -> Result<Resource<TheoremNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&context, Sort::Context))
            .and_then(|context| self.node(&term, Sort::Term).map(|term| (context, term)))
            .and_then(|(context, term)| {
                self.append(Recipe::Hypothesis { context, term }, Sort::Theorem)
            })
    }

    fn prove_truth(
        &mut self,
        plan: Resource<ProofPlan>,
        context: Resource<ContextNode>,
    ) -> Result<Resource<TheoremNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&context, Sort::Context))
            .and_then(|context| self.append(Recipe::Truth { context }, Sort::Theorem))
    }

    fn prove_reflexivity(
        &mut self,
        plan: Resource<ProofPlan>,
        context: Resource<ContextNode>,
        term: Resource<TermNode>,
    ) -> Result<Resource<TheoremNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&context, Sort::Context))
            .and_then(|context| self.node(&term, Sort::Term).map(|term| (context, term)))
            .and_then(|(context, term)| {
                self.append(Recipe::Reflexivity { context, term }, Sort::Theorem)
            })
    }

    fn prove_deduction_antisymmetry(
        &mut self,
        plan: Resource<ProofPlan>,
        first: Resource<TheoremNode>,
        second: Resource<TheoremNode>,
    ) -> Result<Resource<TheoremNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&first, Sort::Theorem))
            .and_then(|first| {
                self.node(&second, Sort::Theorem)
                    .map(|second| (first, second))
            })
            .and_then(|(first, second)| {
                self.append(
                    Recipe::DeductionAntisymmetry { first, second },
                    Sort::Theorem,
                )
            })
    }

    fn prove_equality_modus_ponens(
        &mut self,
        plan: Resource<ProofPlan>,
        equality: Resource<TheoremNode>,
        premise: Resource<TheoremNode>,
    ) -> Result<Resource<TheoremNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&equality, Sort::Theorem))
            .and_then(|equality| {
                self.node(&premise, Sort::Theorem)
                    .map(|premise| (equality, premise))
            })
            .and_then(|(equality, premise)| {
                self.append(
                    Recipe::EqualityModusPonens { equality, premise },
                    Sort::Theorem,
                )
            })
    }

    fn prove_equality_substitution(
        &mut self,
        plan: Resource<ProofPlan>,
        equality: Resource<TheoremNode>,
        predicate: Resource<TermNode>,
        premise: Resource<TheoremNode>,
    ) -> Result<Resource<TheoremNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&equality, Sort::Theorem))
            .and_then(|equality| {
                self.node(&predicate, Sort::Term)
                    .map(|predicate| (equality, predicate))
            })
            .and_then(|(equality, predicate)| {
                self.node(&premise, Sort::Theorem)
                    .map(|premise| (equality, predicate, premise))
            })
            .and_then(|(equality, predicate, premise)| {
                self.append(
                    Recipe::EqualitySubstitution {
                        equality,
                        predicate,
                        premise,
                    },
                    Sort::Theorem,
                )
            })
    }

    fn prove_choice(
        &mut self,
        plan: Resource<ProofPlan>,
        premise: Resource<TheoremNode>,
    ) -> Result<Resource<TheoremNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&premise, Sort::Theorem))
            .and_then(|premise| self.append(Recipe::Choice { premise }, Sort::Theorem))
    }

    fn empty_theorem_witness_list(
        &mut self,
        plan: Resource<ProofPlan>,
    ) -> Result<Resource<TheoremWitnessListNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.append(Recipe::EmptyTheoremWitnessList, Sort::TheoremWitnessList))
    }

    fn extend_theorem_witness_list(
        &mut self,
        plan: Resource<ProofPlan>,
        base: Resource<TheoremWitnessListNode>,
        witness: Resource<TheoremNode>,
    ) -> Result<Resource<TheoremWitnessListNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&base, Sort::TheoremWitnessList))
            .and_then(|base| {
                self.node(&witness, Sort::Theorem)
                    .map(|witness| (base, witness))
            })
            .and_then(|(base, witness)| {
                if self.theorem_witness_list_depth(base) >= MAX_CONTEXT_MEMBERS {
                    return Err(AppendError::ResourceLimit);
                }
                self.append(
                    Recipe::ExtendTheoremWitnessList { base, witness },
                    Sort::TheoremWitnessList,
                )
            })
    }

    fn prove_context_implication(
        &mut self,
        plan: Resource<ProofPlan>,
        antecedent: Resource<ContextNode>,
        consequent: Resource<ContextNode>,
        witnesses: Resource<TheoremWitnessListNode>,
    ) -> Result<Resource<ContextImplicationNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&antecedent, Sort::Context))
            .and_then(|antecedent| {
                self.node(&consequent, Sort::Context)
                    .map(|consequent| (antecedent, consequent))
            })
            .and_then(|(antecedent, consequent)| {
                self.node(&witnesses, Sort::TheoremWitnessList)
                    .map(|witnesses| (antecedent, consequent, witnesses))
            })
            .and_then(|(antecedent, consequent, witnesses)| {
                self.append(
                    Recipe::ContextImplication {
                        antecedent,
                        consequent,
                        witnesses,
                    },
                    Sort::ContextImplication,
                )
            })
    }

    fn persist_context_implication(
        &mut self,
        plan: Resource<ProofPlan>,
        implication: Resource<ContextImplicationNode>,
    ) -> Result<(), AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&implication, Sort::ContextImplication))
            .and_then(|implication| {
                self.append_unit(
                    Recipe::PersistContextImplication { implication },
                    Sort::Unit,
                )
            })
    }

    fn singleton_context_path(
        &mut self,
        plan: Resource<ProofPlan>,
        context: Resource<ContextNode>,
    ) -> Result<Resource<ContextPathNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&context, Sort::Context))
            .and_then(|context| {
                self.append(Recipe::SingletonContextPath { context }, Sort::ContextPath)
            })
    }

    fn extend_context_path(
        &mut self,
        plan: Resource<ProofPlan>,
        base: Resource<ContextPathNode>,
        context: Resource<ContextNode>,
    ) -> Result<Resource<ContextPathNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&base, Sort::ContextPath))
            .and_then(|base| {
                self.node(&context, Sort::Context)
                    .map(|context| (base, context))
            })
            .and_then(|(base, context)| {
                if self.context_path_depth(base) >= MAX_CONTEXT_MEMBERS {
                    return Err(AppendError::ResourceLimit);
                }
                self.append(
                    Recipe::ExtendContextPath { base, context },
                    Sort::ContextPath,
                )
            })
    }

    fn prove_context_implication_path(
        &mut self,
        plan: Resource<ProofPlan>,
        path: Resource<ContextPathNode>,
    ) -> Result<Resource<ContextImplicationNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&path, Sort::ContextPath))
            .and_then(|path| {
                self.append(
                    Recipe::ContextImplicationPath { path },
                    Sort::ContextImplication,
                )
            })
    }

    fn prove_weakening(
        &mut self,
        plan: Resource<ProofPlan>,
        implication: Resource<ContextImplicationNode>,
        theorem: Resource<TheoremNode>,
    ) -> Result<Resource<TheoremNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&implication, Sort::ContextImplication))
            .and_then(|implication| {
                self.node(&theorem, Sort::Theorem)
                    .map(|theorem| (implication, theorem))
            })
            .and_then(|(implication, theorem)| {
                self.append(
                    Recipe::Weakening {
                        implication,
                        theorem,
                    },
                    Sort::Theorem,
                )
            })
    }

    fn prove_context_union(
        &mut self,
        plan: Resource<ProofPlan>,
        left: Resource<ContextNode>,
        right: Resource<ContextNode>,
        result_context: Resource<ContextNode>,
    ) -> Result<Resource<ContextUnionNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&left, Sort::Context))
            .and_then(|left| self.node(&right, Sort::Context).map(|right| (left, right)))
            .and_then(|(left, right)| {
                self.node(&result_context, Sort::Context)
                    .map(|result| (left, right, result))
            })
            .and_then(|(left, right, result)| {
                self.append(
                    Recipe::ContextUnion {
                        left,
                        right,
                        result,
                    },
                    Sort::ContextUnion,
                )
            })
    }

    fn prove_context_equivalence(
        &mut self,
        plan: Resource<ProofPlan>,
        forward: Resource<ContextImplicationNode>,
        backward: Resource<ContextImplicationNode>,
    ) -> Result<Resource<ContextEquivalenceNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&forward, Sort::ContextImplication))
            .and_then(|forward| {
                self.node(&backward, Sort::ContextImplication)
                    .map(|backward| (forward, backward))
            })
            .and_then(|(forward, backward)| {
                self.append(
                    Recipe::ContextEquivalence { forward, backward },
                    Sort::ContextEquivalence,
                )
            })
    }

    fn conversion_reflexivity(
        &mut self,
        plan: Resource<ProofPlan>,
        term: Resource<TermNode>,
    ) -> Result<Resource<ConversionNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&term, Sort::Term))
            .and_then(|term| self.append(Recipe::ConversionReflexivity { term }, Sort::Conversion))
    }

    fn conversion_symmetry(
        &mut self,
        plan: Resource<ProofPlan>,
        conversion: Resource<ConversionNode>,
    ) -> Result<Resource<ConversionNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&conversion, Sort::Conversion))
            .and_then(|conversion| {
                self.append(Recipe::ConversionSymmetry { conversion }, Sort::Conversion)
            })
    }

    fn conversion_transitivity(
        &mut self,
        plan: Resource<ProofPlan>,
        first: Resource<ConversionNode>,
        second: Resource<ConversionNode>,
    ) -> Result<Resource<ConversionNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&first, Sort::Conversion))
            .and_then(|first| {
                self.node(&second, Sort::Conversion)
                    .map(|second| (first, second))
            })
            .and_then(|(first, second)| {
                self.append(
                    Recipe::ConversionTransitivity { first, second },
                    Sort::Conversion,
                )
            })
    }

    fn conversion_application(
        &mut self,
        plan: Resource<ProofPlan>,
        function: Resource<ConversionNode>,
        argument: Resource<ConversionNode>,
    ) -> Result<Resource<ConversionNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&function, Sort::Conversion))
            .and_then(|function| {
                self.node(&argument, Sort::Conversion)
                    .map(|argument| (function, argument))
            })
            .and_then(|(function, argument)| {
                self.append(
                    Recipe::ConversionApplication { function, argument },
                    Sort::Conversion,
                )
            })
    }

    fn conversion_lambda(
        &mut self,
        plan: Resource<ProofPlan>,
        parameter_type: Resource<TypeNode>,
        body: Resource<ConversionNode>,
    ) -> Result<Resource<ConversionNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&parameter_type, Sort::Type))
            .and_then(|parameter_type| {
                self.node(&body, Sort::Conversion)
                    .map(|body| (parameter_type, body))
            })
            .and_then(|(parameter_type, body)| {
                self.append(
                    Recipe::ConversionLambda {
                        parameter_type,
                        body,
                    },
                    Sort::Conversion,
                )
            })
    }

    fn conversion_beta(
        &mut self,
        plan: Resource<ProofPlan>,
        abstraction: Resource<TermNode>,
        argument: Resource<TermNode>,
    ) -> Result<Resource<ConversionNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&abstraction, Sort::Term))
            .and_then(|abstraction| {
                self.node(&argument, Sort::Term)
                    .map(|argument| (abstraction, argument))
            })
            .and_then(|(abstraction, argument)| {
                self.append(
                    Recipe::ConversionBeta {
                        abstraction,
                        argument,
                    },
                    Sort::Conversion,
                )
            })
    }

    fn conversion_eta(
        &mut self,
        plan: Resource<ProofPlan>,
        function: Resource<TermNode>,
    ) -> Result<Resource<ConversionNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&function, Sort::Term))
            .and_then(|function| self.append(Recipe::ConversionEta { function }, Sort::Conversion))
    }

    fn conversion_epsilon(
        &mut self,
        plan: Resource<ProofPlan>,
        predicate: Resource<ConversionNode>,
    ) -> Result<Resource<ConversionNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&predicate, Sort::Conversion))
            .and_then(|predicate| {
                self.append(Recipe::ConversionEpsilon { predicate }, Sort::Conversion)
            })
    }

    fn prove_conversion_equality(
        &mut self,
        plan: Resource<ProofPlan>,
        context: Resource<ContextNode>,
        conversion: Resource<ConversionNode>,
    ) -> Result<Resource<TheoremNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&context, Sort::Context))
            .and_then(|context| {
                self.node(&conversion, Sort::Conversion)
                    .map(|conversion| (context, conversion))
            })
            .and_then(|(context, conversion)| {
                self.append(
                    Recipe::ConversionEquality {
                        context,
                        conversion,
                    },
                    Sort::Theorem,
                )
            })
    }

    fn convert_theorem(
        &mut self,
        plan: Resource<ProofPlan>,
        theorem: Resource<TheoremNode>,
        conversion: Resource<ConversionNode>,
    ) -> Result<Resource<TheoremNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&theorem, Sort::Theorem))
            .and_then(|theorem| {
                self.node(&conversion, Sort::Conversion)
                    .map(|conversion| (theorem, conversion))
            })
            .and_then(|(theorem, conversion)| {
                self.append(
                    Recipe::ConvertTheorem {
                        theorem,
                        conversion,
                    },
                    Sort::Theorem,
                )
            })
    }

    fn empty_term_instantiation_map(
        &mut self,
        plan: Resource<ProofPlan>,
    ) -> Result<Resource<TermInstantiationMapNode>, AppendError> {
        Self::plan(&plan).and_then(|()| {
            self.append(
                Recipe::EmptyTermInstantiationMap,
                Sort::TermInstantiationMap,
            )
        })
    }

    fn extend_term_instantiation_map(
        &mut self,
        plan: Resource<ProofPlan>,
        base: Resource<TermInstantiationMapNode>,
        variable: Resource<TermNode>,
        replacement: Resource<TermNode>,
    ) -> Result<Resource<TermInstantiationMapNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&base, Sort::TermInstantiationMap))
            .and_then(|base| {
                self.node(&variable, Sort::Term)
                    .map(|variable| (base, variable))
            })
            .and_then(|(base, variable)| {
                self.node(&replacement, Sort::Term)
                    .map(|replacement| (base, variable, replacement))
            })
            .and_then(|(base, variable, replacement)| {
                (!self.term_map_contains(base, variable))
                    .then_some((base, variable, replacement))
                    .ok_or(AppendError::InvalidDependency)
            })
            .and_then(|(base, variable, replacement)| {
                self.append(
                    Recipe::ExtendTermInstantiationMap {
                        base,
                        variable,
                        replacement,
                    },
                    Sort::TermInstantiationMap,
                )
            })
    }

    fn prove_term_instantiation(
        &mut self,
        plan: Resource<ProofPlan>,
        theorem: Resource<TheoremNode>,
        instantiations: Resource<TermInstantiationMapNode>,
    ) -> Result<Resource<TheoremNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&theorem, Sort::Theorem))
            .and_then(|theorem| {
                self.node(&instantiations, Sort::TermInstantiationMap)
                    .map(|instantiations| (theorem, instantiations))
            })
            .and_then(|(theorem, instantiations)| {
                self.append(
                    Recipe::TermInstantiation {
                        theorem,
                        instantiations,
                    },
                    Sort::Theorem,
                )
            })
    }

    fn empty_type_instantiation_map(
        &mut self,
        plan: Resource<ProofPlan>,
    ) -> Result<Resource<TypeInstantiationMapNode>, AppendError> {
        Self::plan(&plan).and_then(|()| {
            self.append(
                Recipe::EmptyTypeInstantiationMap,
                Sort::TypeInstantiationMap,
            )
        })
    }

    fn extend_type_instantiation_map(
        &mut self,
        plan: Resource<ProofPlan>,
        base: Resource<TypeInstantiationMapNode>,
        variable: Resource<TypeNode>,
        replacement: Resource<TypeNode>,
    ) -> Result<Resource<TypeInstantiationMapNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&base, Sort::TypeInstantiationMap))
            .and_then(|base| {
                self.node(&variable, Sort::Type)
                    .map(|variable| (base, variable))
            })
            .and_then(|(base, variable)| {
                self.node(&replacement, Sort::Type)
                    .map(|replacement| (base, variable, replacement))
            })
            .and_then(|(base, variable, replacement)| {
                (!self.type_map_contains(base, variable))
                    .then_some((base, variable, replacement))
                    .ok_or(AppendError::InvalidDependency)
            })
            .and_then(|(base, variable, replacement)| {
                self.append(
                    Recipe::ExtendTypeInstantiationMap {
                        base,
                        variable,
                        replacement,
                    },
                    Sort::TypeInstantiationMap,
                )
            })
    }

    fn prove_type_instantiation(
        &mut self,
        plan: Resource<ProofPlan>,
        theorem: Resource<TheoremNode>,
        instantiations: Resource<TypeInstantiationMapNode>,
    ) -> Result<Resource<TheoremNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&theorem, Sort::Theorem))
            .and_then(|theorem| {
                self.node(&instantiations, Sort::TypeInstantiationMap)
                    .map(|instantiations| (theorem, instantiations))
            })
            .and_then(|(theorem, instantiations)| {
                self.append(
                    Recipe::TypeInstantiation {
                        theorem,
                        instantiations,
                    },
                    Sort::Theorem,
                )
            })
    }

    fn prove_abstraction(
        &mut self,
        plan: Resource<ProofPlan>,
        theorem: Resource<TheoremNode>,
        variable: Resource<TermNode>,
    ) -> Result<Resource<TheoremNode>, AppendError> {
        Self::plan(&plan)
            .and_then(|()| self.node(&theorem, Sort::Theorem))
            .and_then(|theorem| {
                self.node(&variable, Sort::Term)
                    .map(|variable| (theorem, variable))
            })
            .and_then(|(theorem, variable)| {
                self.append(Recipe::Abstraction { theorem, variable }, Sort::Theorem)
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
drop_resource!(HostConversionNode, ConversionNode);
drop_resource!(HostTheoremNode, TheoremNode);
drop_resource!(HostTheoremWitnessListNode, TheoremWitnessListNode);
drop_resource!(HostContextImplicationNode, ContextImplicationNode);
drop_resource!(HostContextPathNode, ContextPathNode);
drop_resource!(HostContextUnionNode, ContextUnionNode);
drop_resource!(HostContextEquivalenceNode, ContextEquivalenceNode);
drop_resource!(HostNamespaceNode, NamespaceNode);
drop_resource!(HostTermInstantiationMapNode, TermInstantiationMapNode);
drop_resource!(HostTypeInstantiationMapNode, TypeInstantiationMapNode);

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

    #[test]
    fn guest_builder_rejects_the_65th_witness_and_path_entry() {
        let plan = || Resource::new_borrow(PLAN_REP);
        let mut witnesses = GuestState::new();
        let context = witnesses.empty_context(plan()).unwrap().rep();
        let theorem = witnesses
            .prove_truth(plan(), Resource::new_borrow(context))
            .unwrap()
            .rep();
        let mut list = witnesses.empty_theorem_witness_list(plan()).unwrap().rep();
        for _ in 0..MAX_CONTEXT_MEMBERS {
            list = witnesses
                .extend_theorem_witness_list(
                    plan(),
                    Resource::new_borrow(list),
                    Resource::new_borrow(theorem),
                )
                .unwrap()
                .rep();
        }
        assert!(matches!(
            witnesses.extend_theorem_witness_list(
                plan(),
                Resource::new_borrow(list),
                Resource::new_borrow(theorem),
            ),
            Err(AppendError::ResourceLimit)
        ));

        let mut paths = GuestState::new();
        let context = paths.empty_context(plan()).unwrap().rep();
        let mut path = paths
            .singleton_context_path(plan(), Resource::new_borrow(context))
            .unwrap()
            .rep();
        for _ in 1..MAX_CONTEXT_MEMBERS {
            path = paths
                .extend_context_path(
                    plan(),
                    Resource::new_borrow(path),
                    Resource::new_borrow(context),
                )
                .unwrap()
                .rep();
        }
        assert!(matches!(
            paths.extend_context_path(
                plan(),
                Resource::new_borrow(path),
                Resource::new_borrow(context),
            ),
            Err(AppendError::ResourceLimit)
        ));
    }

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
            Recipe::ConversionBeta {
                abstraction: 2,
                argument: 3,
            },
            Recipe::ConversionEquality {
                context: 4,
                conversion: 5,
            },
            Recipe::Persist { theorem: 6 },
            Recipe::Namespace {
                name: Some("demo".into()),
            },
            Recipe::ExportContext {
                namespace: 8,
                export: 0,
                context: 4,
                name: Some("empty_context".into()),
            },
            Recipe::ExportTheorem {
                namespace: 8,
                export: 1,
                theorem: 6,
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
            state.conversion_eta(
                Resource::new_borrow(PLAN_REP),
                Resource::new_borrow(context.rep()),
            ),
            Err(AppendError::InvalidDependency)
        ));
        assert!(matches!(
            state.conversion_symmetry(
                Resource::new_borrow(PLAN_REP),
                Resource::new_borrow(context.rep()),
            ),
            Err(AppendError::InvalidDependency)
        ));
    }

    #[test]
    fn conversion_and_theorem_transport_resources_are_typed_recipe_nodes() {
        let mut state = GuestState::new();
        let truth = state
            .bool_term(Resource::new_borrow(PLAN_REP), true)
            .unwrap();
        let context = state.empty_context(Resource::new_borrow(PLAN_REP)).unwrap();
        let conversion = state
            .conversion_reflexivity(
                Resource::new_borrow(PLAN_REP),
                Resource::new_borrow(truth.rep()),
            )
            .unwrap();
        let theorem = state
            .prove_conversion_equality(
                Resource::new_borrow(PLAN_REP),
                Resource::new_borrow(context.rep()),
                Resource::new_borrow(conversion.rep()),
            )
            .unwrap();
        let transported = state
            .convert_theorem(
                Resource::new_borrow(PLAN_REP),
                Resource::new_borrow(theorem.rep()),
                Resource::new_borrow(conversion.rep()),
            )
            .unwrap();
        assert_eq!(state.node(&conversion, Sort::Conversion), Ok(2));
        assert_eq!(state.node(&transported, Sort::Theorem), Ok(4));
        assert!(matches!(
            state.recipe.last(),
            Some(Recipe::ConvertTheorem {
                theorem: 3,
                conversion: 2
            })
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
    fn instantiation_maps_are_immutable_typed_and_reject_duplicate_recipe_keys() {
        let mut state = GuestState::new();
        let plan = || Resource::new_borrow(PLAN_REP);
        let alpha = state.free_type(plan(), 0).unwrap();
        let x = state
            .free_term(plan(), 0, Resource::new_borrow(alpha.rep()))
            .unwrap();
        let y = state
            .free_term(plan(), 1, Resource::new_borrow(alpha.rep()))
            .unwrap();
        let empty = state.empty_term_instantiation_map(plan()).unwrap();
        let one = state
            .extend_term_instantiation_map(
                plan(),
                Resource::new_borrow(empty.rep()),
                Resource::new_borrow(x.rep()),
                Resource::new_borrow(y.rep()),
            )
            .unwrap();
        assert!(matches!(
            state.extend_term_instantiation_map(
                plan(),
                Resource::new_borrow(one.rep()),
                Resource::new_borrow(x.rep()),
                Resource::new_borrow(y.rep()),
            ),
            Err(AppendError::InvalidDependency)
        ));
        assert_eq!(
            state.node(&one, Sort::TypeInstantiationMap),
            Err(AppendError::InvalidDependency)
        );
        assert!(matches!(
            state.recipe[usize::try_from(empty.rep()).unwrap() - 2],
            Recipe::EmptyTermInstantiationMap
        ));
    }

    #[test]
    fn replayed_guest_artifact_uses_the_selected_receiver_contract() {
        let recipe = closed_beta_recipe();
        let producer = Kernel::ephemeral();
        let artifact = SealedHolProofRecipe::seal(recipe, 8)
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
        let conversion = state
            .conversion_beta(Resource::new_borrow(PLAN_REP), abstraction, argument)
            .unwrap();
        let theorem = state
            .prove_conversion_equality(Resource::new_borrow(PLAN_REP), context, conversion)
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
    fn adapter_appends_context_truth_reflexivity_and_substitution_nodes() {
        let plan = || Resource::new_borrow(PLAN_REP);
        let mut state = GuestState::new();
        let ty = state.bool_type(plan()).unwrap().rep();
        let bound = state
            .bound_term(plan(), 0, Resource::new_borrow(ty))
            .unwrap()
            .rep();
        let identity = state
            .lambda(
                plan(),
                Resource::new_borrow(ty),
                Resource::new_borrow(bound),
            )
            .unwrap()
            .rep();
        let truth = state.bool_term(plan(), true).unwrap().rep();
        let application = state
            .application(
                plan(),
                Resource::new_borrow(identity),
                Resource::new_borrow(truth),
            )
            .unwrap()
            .rep();
        let empty = state.empty_context(plan()).unwrap().rep();
        let context = state
            .extend_context(
                plan(),
                Resource::new_borrow(empty),
                Resource::new_borrow(application),
            )
            .unwrap()
            .rep();
        let reflexivity = state
            .prove_reflexivity(
                plan(),
                Resource::new_borrow(context),
                Resource::new_borrow(truth),
            )
            .unwrap()
            .rep();
        let premise = state
            .prove_hypothesis(
                plan(),
                Resource::new_borrow(context),
                Resource::new_borrow(application),
            )
            .unwrap()
            .rep();
        state
            .prove_equality_substitution(
                plan(),
                Resource::new_borrow(reflexivity),
                Resource::new_borrow(identity),
                Resource::new_borrow(premise),
            )
            .unwrap();
        let truth_theorem = state
            .prove_truth(plan(), Resource::new_borrow(empty))
            .unwrap();
        state
            .prove_choice(plan(), Resource::new_borrow(truth_theorem.rep()))
            .unwrap();

        assert!(matches!(
            state.recipe[state.recipe.len() - 3],
            Recipe::EqualitySubstitution { .. }
        ));
        assert!(matches!(
            state.recipe[state.recipe.len() - 2],
            Recipe::Truth { .. }
        ));
        assert!(matches!(state.recipe.last(), Some(Recipe::Choice { .. })));
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
    fn configured_real_eta_component_exports_the_named_eta_graph() {
        assert_configured_binding_component(
            "COVALENCE_HOL_ETA_GUEST_COMPONENT",
            "eta-demo",
            "identity_eta",
            None,
        );
    }

    #[test]
    fn configured_real_schematic_component_exports_the_named_binding_graph() {
        assert_configured_binding_component(
            "COVALENCE_HOL_SCHEMATIC_GUEST_COMPONENT",
            "schematic-binding-demo",
            "schematic_identity_binding",
            Some(crate::hol_guest_plan::SCHEMATIC_BINDING_WIRE),
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn configured_real_conversion_component_exports_the_nested_identity_graph() {
        let Some(component) = std::env::var_os("COVALENCE_HOL_CONVERSION_GUEST_COMPONENT") else {
            return;
        };
        let bytes = std::fs::read(component).unwrap();
        let recipe =
            collect_hol_proof_component(&bytes, WasmtimeComponentLimits::default()).unwrap();
        assert_eq!(
            recipe.as_bytes(),
            crate::hol_guest_plan::nested_identity_conversion_test_recipe().as_bytes()
        );
        let artifact = recipe.replay(&Kernel::ephemeral()).unwrap();
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
            (0, "conversion-demo".to_owned())
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
            ("term", "nested_identity_beta")
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

        let (tag, outer, truth) = sqlite
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
        assert_eq!(tag, "MEQ");
        let (outer_tag, identity, inner) = sqlite
            .query_row(
                "SELECT tag, lhs, rhs FROM hol_node WHERE node_id = ?1",
                [outer],
                |row| {
                    Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, i64>(2)?,
                    ))
                },
            )
            .unwrap();
        assert_eq!(outer_tag, "MAPP");
        assert_eq!(
            sqlite
                .query_row(
                    "SELECT tag, lhs, rhs FROM hol_node WHERE node_id = ?1",
                    [inner],
                    |row| Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, i64>(2)?
                    )),
                )
                .unwrap(),
            ("MAPP".to_owned(), identity, truth)
        );
        let (identity_tag, parameter_type, body) = sqlite
            .query_row(
                "SELECT tag, lhs, rhs FROM hol_node WHERE node_id = ?1",
                [identity],
                |row| {
                    Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, i64>(2)?,
                    ))
                },
            )
            .unwrap();
        assert_eq!(identity_tag, "MLAM");
        assert_eq!(
            sqlite
                .query_row(
                    "SELECT tag, lhs, ty FROM hol_node WHERE node_id = ?1",
                    [body],
                    |row| Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, i64>(2)?
                    )),
                )
                .unwrap(),
            ("MBV".to_owned(), 0, parameter_type)
        );
        assert_eq!(
            sqlite
                .query_row(
                    "SELECT tag, lhs FROM hol_node WHERE node_id = ?1",
                    [truth],
                    |row| Ok((row.get::<_, String>(0)?, row.get::<_, i64>(1)?)),
                )
                .unwrap(),
            ("MBOOL".to_owned(), 1)
        );
    }

    #[test]
    fn configured_real_assumptions_component_exports_exact_context_and_truth() {
        let Some(component) = std::env::var_os("COVALENCE_HOL_ASSUMPTIONS_GUEST_COMPONENT") else {
            return;
        };
        let bytes = std::fs::read(component).unwrap();
        let recipe =
            collect_hol_proof_component(&bytes, WasmtimeComponentLimits::default()).unwrap();
        assert_eq!(
            recipe.as_bytes(),
            crate::hol_guest_plan::ASSUMPTIONS_EQUALITY_WIRE
        );
        let producer = Kernel::ephemeral();
        let artifact = recipe.replay(&producer).unwrap();
        let image_bytes = covalence_neutron::Bytes::copy_from_slice(artifact.image());
        let image = covalence_neutron::Connection::deserialize(&image_bytes).unwrap();
        let coordinates = assert_assumptions_exports(image.sqlite(), artifact.namespace_id());
        assert_assumptions_kernel_state(image.sqlite(), coordinates);
        assert_generic_theorem_receive(&producer, &artifact, coordinates);
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn configured_real_choice_component_exports_exact_identity_epsilon_graph() {
        let Some(component) = std::env::var_os("COVALENCE_HOL_CHOICE_GUEST_COMPONENT") else {
            return;
        };
        let bytes = std::fs::read(component).unwrap();
        let recipe =
            collect_hol_proof_component(&bytes, WasmtimeComponentLimits::default()).unwrap();
        assert_eq!(recipe.as_bytes(), crate::hol_guest_plan::CHOICE_WIRE);
        assert_eq!(
            recipe.as_bytes(),
            crate::hol_guest_plan::choice_test_recipe().as_bytes()
        );

        let producer = Kernel::ephemeral();
        let artifact = recipe.replay(&producer).unwrap();
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
            (0, "choice-demo".to_owned())
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
            ("term", "identity_epsilon")
        );
        assert_eq!(
            sqlite
                .query_row("SELECT count(*) FROM hol_judgement", [], |row| {
                    row.get::<_, i64>(0)
                })
                .unwrap(),
            1
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

        let (conclusion_tag, identity, epsilon, conclusion_ty) = sqlite
            .query_row(
                "SELECT tag, lhs, rhs, ty FROM hol_node WHERE node_id = ?1",
                [conclusion],
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
        assert_eq!(conclusion_tag, "MAPP");
        assert_eq!(
            sqlite
                .query_row(
                    "SELECT tag, lhs, rhs, ty FROM hol_node WHERE node_id = ?1",
                    [epsilon],
                    |row| Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, Option<i64>>(2)?,
                        row.get::<_, i64>(3)?,
                    )),
                )
                .unwrap(),
            ("MEPS".to_owned(), identity, None, conclusion_ty)
        );
        let (identity_tag, parameter_type, body, identity_type) = sqlite
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
        assert_eq!(identity_tag, "MLAM");
        assert_eq!(parameter_type, conclusion_ty);
        assert_eq!(
            sqlite
                .query_row(
                    "SELECT tag, lhs, rhs, ty FROM hol_node WHERE node_id = ?1",
                    [body],
                    |row| Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, Option<i64>>(2)?,
                        row.get::<_, i64>(3)?,
                    )),
                )
                .unwrap(),
            ("MBV".to_owned(), 0, None, parameter_type)
        );
        assert_eq!(
            sqlite
                .query_row(
                    "SELECT tag, lhs, rhs, ty FROM hol_node WHERE node_id = ?1",
                    [identity_type],
                    |row| Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, i64>(2)?,
                        row.get::<_, i64>(3)?,
                    )),
                )
                .unwrap(),
            ("TARR".to_owned(), parameter_type, parameter_type, 1)
        );
        assert_generic_theorem_receive(&producer, &artifact, (context, conclusion));
    }

    #[test]
    fn configured_real_context_capabilities_component_matches_fixed_wire_and_receives() {
        let Some(component) =
            std::env::var_os("COVALENCE_HOL_CONTEXT_CAPABILITIES_GUEST_COMPONENT")
        else {
            return;
        };
        let bytes = std::fs::read(component).unwrap();
        let recipe =
            collect_hol_proof_component(&bytes, WasmtimeComponentLimits::default()).unwrap();
        assert_eq!(
            recipe.as_bytes(),
            crate::hol_guest_plan::CONTEXT_CAPABILITIES_WIRE
        );
        assert_eq!(
            recipe.as_bytes(),
            crate::hol_guest_plan::context_capabilities_test_recipe().as_bytes()
        );
        let producer = Kernel::ephemeral();
        let artifact = recipe.replay(&producer).unwrap();
        let image_bytes = covalence_neutron::Bytes::copy_from_slice(artifact.image());
        let image = covalence_neutron::Connection::deserialize(&image_bytes).unwrap();
        let sqlite = image.sqlite();
        let namespace = artifact.namespace_id();
        let context = sqlite
            .query_row(
                "SELECT local_id FROM hol_namespace_export
                 WHERE namespace_id = ?1 AND export_id = 0
                   AND sort = 'context' AND name = 'combined_context'",
                [namespace],
                |row| row.get::<_, i64>(0),
            )
            .unwrap();
        let conclusion = sqlite
            .query_row(
                "SELECT local_id FROM hol_namespace_export
                 WHERE namespace_id = ?1 AND export_id = 1
                   AND sort = 'term' AND name = 'weakened_truth'",
                [namespace],
                |row| row.get::<_, i64>(0),
            )
            .unwrap();
        assert_generic_theorem_receive(&producer, &artifact, (context, conclusion));
    }

    fn assert_assumptions_exports(
        sqlite: &covalence_lib_sqlite::Connection,
        namespace: i64,
    ) -> (i64, i64) {
        assert_eq!(
            sqlite
                .query_row(
                    "SELECT parent_namespace_id, name FROM hol_namespace WHERE namespace_id = ?1",
                    [namespace],
                    |row| Ok((row.get::<_, i64>(0)?, row.get::<_, String>(1)?)),
                )
                .unwrap(),
            (0, "assumptions-demo".to_owned())
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
            (context_sort.as_str(), context_name.as_str()),
            ("context", "p_context")
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
            ("term", "truth_from_p")
        );
        (context, conclusion)
    }

    fn assert_assumptions_kernel_state(
        sqlite: &covalence_lib_sqlite::Connection,
        (context, conclusion): (i64, i64),
    ) {
        assert_eq!(
            sqlite
                .query_row(
                    "SELECT tag, lhs, rhs, ty FROM hol_node WHERE node_id = ?1",
                    [conclusion],
                    |row| Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, Option<i64>>(2)?,
                        row.get::<_, i64>(3)?,
                    )),
                )
                .unwrap(),
            ("MBOOL".to_owned(), 1, None, 2)
        );
        let member = sqlite
            .query_row(
                "SELECT term_id FROM hol_context_member WHERE ctx_id = ?1",
                [context],
                |row| row.get::<_, i64>(0),
            )
            .unwrap();
        assert_eq!(
            sqlite
                .query_row(
                    "SELECT tag, lhs, rhs, ty FROM hol_node WHERE node_id = ?1",
                    [member],
                    |row| Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, Option<i64>>(2)?,
                        row.get::<_, i64>(3)?,
                    )),
                )
                .unwrap(),
            ("MFV".to_owned(), 0, None, 2)
        );
        assert_eq!(
            sqlite
                .query_row(
                    "SELECT count(*) FROM hol_context_member WHERE ctx_id = ?1",
                    [context],
                    |row| row.get::<_, i64>(0),
                )
                .unwrap(),
            1
        );
        assert_eq!(
            sqlite
                .query_row("SELECT count(*) FROM hol_judgement", [], |row| {
                    row.get::<_, i64>(0)
                })
                .unwrap(),
            1
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
    }

    fn assert_generic_theorem_receive(
        producer: &Kernel,
        artifact: &SignedHolArtifact,
        expected_coordinates: (i64, i64),
    ) {
        let consumer = Kernel::ephemeral();
        let mut target = consumer.open_hol(covalence_nucleus::AllowAll).unwrap();
        let expected = crate::ExpectedKernelIdentity::from_public_key(
            crate::KernelId::LOCAL,
            producer.verifying_key().as_bytes(),
        )
        .unwrap();
        let pinned = crate::authenticate_pinned_signed_hol_artifact(&expected, artifact).unwrap();
        let receipt =
            crate::trust_and_receive_pinned_signed_hol_artifact(&mut target, pinned).unwrap();
        assert_eq!(
            (receipt.context_id(), receipt.conclusion_id()),
            expected_coordinates
        );
    }

    #[allow(clippy::too_many_lines)]
    fn assert_configured_binding_component(
        environment: &str,
        namespace_name: &str,
        conclusion_export_name: &str,
        expected_recipe: Option<&[u8]>,
    ) {
        let Some(component) = std::env::var_os(environment) else {
            return;
        };
        let bytes = std::fs::read(component).unwrap();
        let limits = WasmtimeComponentLimits::default();
        let recipe = collect_hol_proof_component(&bytes, limits).unwrap();
        if let Some(expected_recipe) = expected_recipe {
            assert_eq!(recipe.as_bytes(), expected_recipe);
        }
        let artifact = recipe.replay(&Kernel::ephemeral()).unwrap();
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
            (0, namespace_name.to_owned())
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
            ("term", conclusion_export_name)
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
        assert_eq!(
            sqlite
                .query_row(
                    "SELECT tag FROM hol_node WHERE node_id = ?1",
                    [parameter_type],
                    |row| row.get::<_, String>(0),
                )
                .unwrap(),
            "TBOOL"
        );
        assert_eq!(
            sqlite
                .query_row(
                    "SELECT tag, lhs, rhs FROM hol_node WHERE node_id = ?1",
                    [eta_type],
                    |row| {
                        Ok((
                            row.get::<_, String>(0)?,
                            row.get::<_, i64>(1)?,
                            row.get::<_, i64>(2)?,
                        ))
                    },
                )
                .unwrap(),
            ("TARR".to_owned(), parameter_type, parameter_type)
        );
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
        let artifact = SealedHolProofRecipe::seal(recipe, 8)
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
        let artifact = SealedHolProofRecipe::seal(recipe, 8)
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
