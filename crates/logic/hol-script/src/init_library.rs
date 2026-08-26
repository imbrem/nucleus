//! Reproducible userspace assembly of the standard checked init library.

use std::collections::BTreeMap;

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{
    AX_INF, AX_SUB, CheckedPrefix, InfinityAxiom, Kernel, KernelError, Lit, Ref, SubtypeAxiom,
    ThmId, init::Compiled as LogicalInit,
};
use covalence_logic_hol_derived::{
    ChosenModel, Infinity, InfinityDecl, InfinityError, ModelExt, NaturalArithmetic,
    NaturalArithmeticDecl, NaturalArithmeticExt, NaturalArithmeticProof, NaturalError, NaturalExt,
    NaturalRecGraphDecl, NaturalRecGraphProof, NaturalRecSchemas, NaturalRecursorDecl,
    NaturalRecursorProof, Naturals, NaturalsDecl, NaturalsProof, OpenedExists, OpenedExistsDecl,
    Subtype, SubtypeDecl, SubtypeError, SyntaxError, join_alpha_equivalent, join_alpha_equivalents,
    open_exists_at,
};

use crate::{
    CompiledTheory, INIT_SOURCE, LogicEncoding, TheoryError, TheoryOptions,
    compile_theory_with_init,
};

/// A standalone checked kernel and the untrusted metadata used to navigate it.
///
/// The source language, this assembly routine, and the dictionary carry no
/// proof authority. The kernel contains only rows admitted by its public
/// checked API, and remains usable if all three are discarded.
#[derive(Debug)]
pub struct InitLibrary {
    kernel: Kernel,
    symbols: BTreeMap<String, Ref>,
    naturals: Naturals,
    recursion_schemas: NaturalRecSchemas,
    arithmetic: NaturalArithmetic,
}

/// The minimal opcode-free init slice and its external userspace dictionary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InitSlice {
    prefix: CheckedPrefix,
    symbols: BTreeMap<String, Ref>,
    recursion_schemas: NaturalRecSchemas,
    naturals: NaturalsDecl,
    arithmetic: NaturalArithmeticDecl,
}

impl InitSlice {
    /// Borrows the exact opcode-free checked prefix.
    #[must_use]
    pub const fn prefix(&self) -> &CheckedPrefix {
        &self.prefix
    }

    /// Creates an independent kernel initialized from the complete slice.
    #[must_use]
    pub fn kernel(&self) -> Kernel {
        self.prefix.kernel()
    }

    /// Resolves one external init-library name.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<Ref> {
        self.symbols.get(name).copied()
    }

    /// Iterates all external names in lexical order.
    #[must_use]
    pub fn symbols(&self) -> impl ExactSizeIterator<Item = (&str, Ref)> {
        self.symbols
            .iter()
            .map(|(name, reference)| (name.as_str(), *reference))
    }

    /// Returns the exact arithmetic declaration resident in this slice.
    #[must_use]
    pub const fn arithmetic(&self) -> &NaturalArithmeticDecl {
        &self.arithmetic
    }

    /// Returns the exact natural-number declaration resident in this slice.
    #[must_use]
    pub const fn naturals(&self) -> &NaturalsDecl {
        &self.naturals
    }

    /// Returns the exact open recursion schemata resident in this slice.
    #[must_use]
    pub const fn recursion_schemas(&self) -> NaturalRecSchemas {
        self.recursion_schemas
    }

    /// Replays the foundational infinity proof against this slice's exact rows.
    ///
    /// Representation lowering, name lookup, and proof orchestration all stay
    /// in this userspace crate. The supplied kernel must be a fork of this
    /// slice; every resulting theorem is admitted by existing checked HOL and
    /// Gentzen rules and concludes an exact declaration reference.
    ///
    /// # Errors
    ///
    /// Returns an error if the logical prefix or declaration is mismatched, or
    /// if any checked construction, substitution, beta, conversion, or
    /// conjunction-projection step is rejected.
    pub fn prove_infinity(
        &self,
        init: &LogicalInit,
        kernel: &mut Kernel,
    ) -> Result<Infinity, InitLibraryError> {
        let mut staged = kernel.fork();
        let package = self.prove_infinity_inner(init, &mut staged)?;
        *kernel = staged;
        Ok(package)
    }

    fn prove_infinity_inner(
        &self,
        init: &LogicalInit,
        kernel: &mut Kernel,
    ) -> Result<Infinity, InitLibraryError> {
        let declaration = self.naturals.infinity;
        let roots = declaration.references().collect::<Vec<_>>();
        let aliases = kernel
            .compact_logical_trees(init, &roots)
            .map_err(|source| InitLibraryError::Kernel { source })?;
        let [
            axiom_alias,
            _,
            _,
            _,
            _,
            _,
            _,
            _,
            _,
            property_alias,
            reflects_alias,
            avoids_alias,
        ] = aliases.as_slice()
        else {
            unreachable!("InfinityDecl::references has a fixed field count")
        };
        let axiom = kernel
            .inf_exists_at(
                self.get("bool")
                    .ok_or(InitLibraryError::MissingSymbol { name: "bool" })?,
                declaration.axiom.base_name,
            )
            .map_err(|source| InitLibraryError::Kernel { source })?;
        join_alpha_equivalent(kernel, axiom.exists_type, axiom_alias.compact)
            .map_err(|source| InitLibraryError::Syntax { source })?;
        kernel
            .convert_theorem(
                axiom.theorem,
                axiom.exists_type,
                declaration.axiom.exists_type,
            )
            .map_err(|source| InitLibraryError::Kernel { source })?;

        let (model, map, missed) = open_infinity_structure(kernel, axiom.theorem, declaration)?;

        let [
            property_theorem,
            reflects_equality_theorem,
            avoids_missed_theorem,
        ] = prove_infinity_laws(
            kernel,
            model.theorem,
            model.specification,
            InfinityLawTargets {
                property: declaration.property,
                property_alias: property_alias.compact,
                reflects_equality: declaration.reflects_equality,
                reflects_alias: reflects_alias.compact,
                avoids_missed: declaration.avoids_missed,
                avoids_alias: avoids_alias.compact,
            },
        )
        .map_err(|source| InitLibraryError::Kernel { source })?;

        Ok(Infinity {
            axiom: InfinityAxiom {
                exists_type: declaration.axiom.exists_type,
                body: declaration.axiom.body,
                carrier_name: declaration.axiom.carrier_name,
                base_name: declaration.axiom.base_name,
                theorem: axiom.theorem,
            },
            model,
            carrier: declaration.carrier,
            map: declaration.map,
            missed_exists: declaration.missed_exists,
            missed: declaration.missed,
            property: declaration.property,
            reflects_equality: declaration.reflects_equality,
            avoids_missed: declaration.avoids_missed,
            theorem: property_theorem,
            reflects_equality_theorem,
            avoids_missed_theorem,
            map_beta: map.beta,
            missed_beta: missed.beta,
        })
    }

    /// Replays the guarded-subtype package against this slice's exact rows.
    ///
    /// As with [`prove_infinity`](Self::prove_infinity), all descriptor and
    /// representation work is untrusted userspace orchestration. The operation
    /// is transactional and every returned theorem concludes its exact frozen
    /// declaration row.
    ///
    /// # Errors
    ///
    /// Returns an error for a wrong prefix or malformed declaration, or when
    /// any existing checked subtype, model, beta, conversion, or Gentzen rule
    /// rejects the replay.
    pub fn prove_subtype(
        &self,
        init: &LogicalInit,
        kernel: &mut Kernel,
    ) -> Result<Subtype, InitLibraryError> {
        let mut staged = kernel.fork();
        let package = self.prove_subtype_inner(init, &mut staged)?;
        *kernel = staged;
        Ok(package)
    }

    fn prove_subtype_inner(
        &self,
        init: &LogicalInit,
        kernel: &mut Kernel,
    ) -> Result<Subtype, InitLibraryError> {
        let declaration = self.naturals.subtype;
        let axiom_decl = declaration
            .axiom
            .ok_or(InitLibraryError::MissingSubtypeAxiom)?;
        let roots = declaration.references().collect::<Vec<_>>();
        let aliases = kernel
            .compact_logical_trees(init, &roots)
            .map_err(|source| InitLibraryError::Kernel { source })?;
        let [
            _carrier_alias,
            _predicate_alias,
            _,
            _,
            _,
            _,
            _,
            _,
            abs_rep_alias,
            rep_abs_alias,
            rep_property_alias,
            rep_guarded_alias,
            property_alias,
            _axiom_alias,
            _,
            _,
            _,
            _,
        ] = aliases.as_slice()
        else {
            unreachable!("SubtypeDecl::references has a fixed field count")
        };
        let bool_ty = self
            .get("bool")
            .ok_or(InitLibraryError::MissingSymbol { name: "bool" })?;
        let axiom = kernel
            .sub_exists(bool_ty, declaration.carrier, declaration.predicate)
            .map_err(|source| InitLibraryError::Kernel { source })?;
        let raw_axiom = kernel
            .lower_logical_tree(init, axiom.exists_type)
            .map_err(|source| InitLibraryError::Kernel { source })?;
        join_alpha_equivalent(kernel, raw_axiom.raw, axiom_decl.exists_type)
            .map_err(|source| InitLibraryError::Syntax { source })?;
        kernel
            .convert_theorem(axiom.theorem, axiom.exists_type, axiom_decl.exists_type)
            .map_err(|source| InitLibraryError::Kernel { source })?;

        let (model, _representation, _abstraction) =
            open_subtype_structure(kernel, axiom.theorem, declaration)?;
        let [
            property_theorem,
            abs_rep_theorem,
            rep_abs_theorem,
            rep_guarded_theorem,
        ] = prove_subtype_laws(
            kernel,
            model.theorem,
            model.specification,
            SubtypeLawTargets {
                property: declaration.property,
                property_alias: property_alias.compact,
                abs_rep: declaration.abs_rep,
                abs_rep_alias: abs_rep_alias.compact,
                rep_property_alias: rep_property_alias.compact,
                rep_abs: declaration.rep_abs,
                rep_abs_alias: rep_abs_alias.compact,
                rep_guarded: declaration.rep_guarded,
                rep_guarded_alias: rep_guarded_alias.compact,
            },
        )
        .map_err(|source| InitLibraryError::Kernel { source })?;

        Ok(Subtype {
            carrier: declaration.carrier,
            predicate: declaration.predicate,
            sub: declaration.sub,
            rep: declaration.rep,
            abs_exists: declaration.abs_exists,
            abs: declaration.abs,
            rep_ty: declaration.rep_ty,
            abs_ty: declaration.abs_ty,
            abs_rep: declaration.abs_rep,
            rep_abs: declaration.rep_abs,
            rep_property: declaration.rep_property,
            rep_guarded: declaration.rep_guarded,
            property: declaration.property,
            axiom: Some(SubtypeAxiom {
                carrier: axiom_decl.carrier,
                predicate: axiom_decl.predicate,
                exists_type: axiom_decl.exists_type,
                package_body: axiom_decl.package_body,
                model_name: axiom_decl.model_name,
                base_name: axiom_decl.base_name,
                theorem: axiom.theorem,
            }),
            model: Some(model),
            property_theorem: Some(property_theorem),
            abs_rep_theorem: Some(abs_rep_theorem),
            rep_abs_theorem: Some(rep_abs_theorem),
            rep_guarded_theorem: Some(rep_guarded_theorem),
            base_name: declaration.base_name,
        })
    }

    /// Replays the complete frozen natural-number package.
    ///
    /// The source schema, package selection, and theorem transport are all
    /// userspace proof search. Returned handles conclude the exact opcode-free
    /// rows stored by this slice, independently of unrelated ambient syntax.
    ///
    /// # Errors
    ///
    /// Returns an error for a mismatched prefix, missing source schema, or any
    /// rejected infinity, subtype, natural-number, lowering, or conversion
    /// certificate. The supplied kernel is unchanged on failure.
    pub fn prove_naturals(
        &self,
        init: &LogicalInit,
        kernel: &mut Kernel,
    ) -> Result<Naturals, InitLibraryError> {
        let mut staged = kernel.fork();
        let package = self.prove_naturals_inner(init, &mut staged)?;
        *kernel = staged;
        Ok(package)
    }

    fn prove_naturals_inner(
        &self,
        init: &LogicalInit,
        kernel: &mut Kernel,
    ) -> Result<Naturals, InitLibraryError> {
        let declaration = self.naturals;
        let infinity = self.prove_infinity_inner(init, kernel)?;
        let subtype = self.prove_subtype_inner(init, kernel)?;
        let member = kernel
            .compact_logical_tree(init, declaration.member)
            .map_err(|source| InitLibraryError::Kernel { source })?;
        let mut working_subtype = subtype;
        let (working_subtype_abs_rep, working_abs_rep_theorem) = compact_theorem(
            init,
            kernel,
            subtype.abs_rep,
            subtype
                .abs_rep_theorem
                .ok_or(InitLibraryError::MissingSubtypeProof { law: "abs_rep" })?,
        )?;
        working_subtype.abs_rep = working_subtype_abs_rep;
        working_subtype.abs_rep_theorem = Some(working_abs_rep_theorem);
        let (working_subtype_rep_abs, working_rep_abs_theorem) = compact_theorem(
            init,
            kernel,
            subtype.rep_abs,
            subtype
                .rep_abs_theorem
                .ok_or(InitLibraryError::MissingSubtypeProof { law: "rep_abs" })?,
        )?;
        working_subtype.rep_abs = working_subtype_rep_abs;
        working_subtype.rep_abs_theorem = Some(working_rep_abs_theorem);
        let (working_subtype_rep_guarded, working_rep_guarded_theorem) = compact_theorem(
            init,
            kernel,
            subtype.rep_guarded,
            subtype
                .rep_guarded_theorem
                .ok_or(InitLibraryError::MissingSubtypeProof { law: "rep_guarded" })?,
        )?;
        working_subtype.rep_guarded = working_subtype_rep_guarded;
        working_subtype.rep_guarded_theorem = Some(working_rep_guarded_theorem);
        let generated = kernel
            .finish_naturals_from_packages(
                self.get("bool")
                    .ok_or(InitLibraryError::MissingSymbol { name: "bool" })?,
                infinity,
                working_subtype,
                member.compact,
            )
            .map_err(|source| InitLibraryError::Natural { source })?;

        for ((name, generated), (exact_name, exact)) in
            generated.symbols().zip(declaration.symbols())
        {
            debug_assert_eq!(name, exact_name);
            retarget_exact_syntax(init, kernel, generated, exact)?;
        }

        let mut retarget = |theorem, generated, exact| {
            retarget_exact_theorem(init, kernel, theorem, generated, exact)
        };
        let proof = NaturalsProof {
            infinity: infinity.proof(),
            subtype: subtype.proof(),
            zero_member: retarget(
                generated.proof.zero_member,
                generated.zero_member,
                declaration.zero_member,
            )?,
            member_inhabited: retarget(
                generated.proof.member_inhabited,
                generated.member_inhabited,
                declaration.member_inhabited,
            )?,
            rep_member: retarget(
                generated.proof.rep_member,
                generated.rep_member,
                declaration.rep_member,
            )?,
            member_succ: retarget(
                generated.proof.member_succ,
                generated.member_succ,
                declaration.member_succ,
            )?,
            induction: retarget(
                generated.proof.induction,
                generated.induction,
                declaration.induction,
            )?,
            succ_injective: retarget(
                generated.proof.succ_injective,
                generated.succ_injective,
                declaration.succ_injective,
            )?,
            zero_ne_succ: retarget(
                generated.proof.zero_ne_succ,
                generated.zero_ne_succ,
                declaration.zero_ne_succ,
            )?,
        };
        Ok(Naturals {
            declaration,
            proof,
            infinity,
            subtype,
        })
    }

    /// Replays primitive addition and multiplication over the frozen naturals.
    ///
    /// # Errors
    ///
    /// Returns an error if natural replay, recursion-schema compaction, or any
    /// checked primitive-recursion and exact-row transport step fails. The
    /// supplied kernel is unchanged on failure.
    pub fn prove_arithmetic(
        &self,
        init: &LogicalInit,
        kernel: &mut Kernel,
    ) -> Result<NaturalArithmetic, InitLibraryError> {
        let mut staged = kernel.fork();
        let naturals = self.prove_naturals_inner(init, &mut staged)?;
        let working_naturals = compact_natural_theorems(init, &mut staged, naturals)?;
        let schema_roots = self.recursion_schemas.references().collect::<Vec<_>>();
        let schema_aliases = staged
            .compact_logical_trees(init, &schema_roots)
            .map_err(|source| InitLibraryError::Kernel { source })?;
        let [
            graph,
            graph_natural,
            graph_codomain,
            specification,
            specification_natural,
            specification_codomain,
        ] = schema_aliases.as_slice()
        else {
            unreachable!("NaturalRecSchemas::references has a fixed field count")
        };
        let schemas = NaturalRecSchemas {
            graph: graph.compact,
            graph_natural: graph_natural.compact,
            graph_codomain: graph_codomain.compact,
            specification: specification.compact,
            specification_natural: specification_natural.compact,
            specification_codomain: specification_codomain.compact,
        };
        let generated = staged
            .natural_arithmetic_at(&working_naturals, schemas, self.arithmetic.base_name)
            .map_err(|source| InitLibraryError::Natural { source })?;
        let declaration = self.arithmetic;

        let reference_pairs = generated
            .declaration
            .references()
            .zip(declaration.references())
            .collect::<Vec<_>>();
        let generated_roots = reference_pairs
            .iter()
            .map(|&(generated, _)| generated)
            .collect::<Vec<_>>();
        let lowered = staged
            .lower_logical_trees(init, &generated_roots)
            .map_err(|source| InitLibraryError::Kernel { source })?;
        let alpha_pairs = lowered
            .iter()
            .zip(&reference_pairs)
            .map(|(lowered, &(_, exact))| (lowered.raw, exact))
            .collect::<Vec<_>>();
        join_alpha_equivalents(&mut staged, &alpha_pairs)
            .map_err(|source| InitLibraryError::Syntax { source })?;
        let proof = retarget_arithmetic_proof(
            init,
            &mut staged,
            generated.declaration,
            generated.proof,
            declaration,
        )?;
        *kernel = staged;
        Ok(NaturalArithmetic { declaration, proof })
    }
}

fn retarget_exact_theorem(
    init: &LogicalInit,
    kernel: &mut Kernel,
    theorem: ThmId,
    generated: Ref,
    exact: Ref,
) -> Result<ThmId, InitLibraryError> {
    if kernel.convert_theorem(theorem, generated, exact).is_ok() {
        return Ok(theorem);
    }
    retarget_exact_syntax(init, kernel, generated, exact)?;
    kernel
        .convert_theorem(theorem, generated, exact)
        .map_err(|source| InitLibraryError::Kernel { source })?;
    Ok(theorem)
}

fn retarget_arithmetic_proof(
    init: &LogicalInit,
    kernel: &mut Kernel,
    generated: NaturalArithmeticDecl,
    proof: NaturalArithmeticProof,
    exact: NaturalArithmeticDecl,
) -> Result<NaturalArithmeticProof, InitLibraryError> {
    Ok(NaturalArithmeticProof {
        add_rec: retarget_recursor_proof(
            init,
            kernel,
            generated.add_rec,
            proof.add_rec,
            exact.add_rec,
        )?,
        add_zero: retarget_exact_theorem(
            init,
            kernel,
            proof.add_zero,
            generated.add_zero,
            exact.add_zero,
        )?,
        add_successor: retarget_exact_theorem(
            init,
            kernel,
            proof.add_successor,
            generated.add_successor,
            exact.add_successor,
        )?,
        mul_rec: retarget_recursor_proof(
            init,
            kernel,
            generated.mul_rec,
            proof.mul_rec,
            exact.mul_rec,
        )?,
        mul_zero: retarget_exact_theorem(
            init,
            kernel,
            proof.mul_zero,
            generated.mul_zero,
            exact.mul_zero,
        )?,
        mul_successor: retarget_exact_theorem(
            init,
            kernel,
            proof.mul_successor,
            generated.mul_successor,
            exact.mul_successor,
        )?,
        one_plus_one: retarget_exact_theorem(
            init,
            kernel,
            proof.one_plus_one,
            generated.one_plus_one,
            exact.one_plus_one,
        )?,
    })
}

fn retarget_recursor_proof(
    init: &LogicalInit,
    kernel: &mut Kernel,
    generated: NaturalRecursorDecl,
    proof: NaturalRecursorProof,
    exact: NaturalRecursorDecl,
) -> Result<NaturalRecursorProof, InitLibraryError> {
    Ok(NaturalRecursorProof {
        graph: retarget_graph_proof(init, kernel, generated.graph, proof.graph, exact.graph)?,
        specification: retarget_exact_theorem(
            init,
            kernel,
            proof.specification,
            generated.specification,
            exact.specification,
        )?,
        unique: retarget_exact_theorem(init, kernel, proof.unique, generated.unique, exact.unique)?,
    })
}

fn retarget_graph_proof(
    init: &LogicalInit,
    kernel: &mut Kernel,
    generated: NaturalRecGraphDecl,
    proof: NaturalRecGraphProof,
    exact: NaturalRecGraphDecl,
) -> Result<NaturalRecGraphProof, InitLibraryError> {
    macro_rules! theorem {
        ($field:ident) => {
            retarget_exact_theorem(init, kernel, proof.$field, generated.$field, exact.$field)?
        };
    }
    Ok(NaturalRecGraphProof {
        base: theorem!(base),
        step: theorem!(step),
        total: theorem!(total),
        has_shape: theorem!(has_shape),
        zero_value: theorem!(zero_value),
        successor_value: theorem!(successor_value),
        zero_functional: theorem!(zero_functional),
        functional: theorem!(functional),
        rec_graph: theorem!(rec_graph),
        rec_zero: theorem!(rec_zero),
        rec_successor: theorem!(rec_successor),
    })
}

fn compact_theorem(
    init: &LogicalInit,
    kernel: &mut Kernel,
    proposition: Ref,
    theorem: ThmId,
) -> Result<(Ref, ThmId), InitLibraryError> {
    let alias = kernel
        .compact_logical_tree(init, proposition)
        .map_err(|source| InitLibraryError::Kernel { source })?;
    let theorem = kernel
        .copy_theorem(theorem)
        .map_err(|source| InitLibraryError::Kernel { source })?;
    kernel
        .convert_theorem(theorem, proposition, alias.compact)
        .map_err(|source| InitLibraryError::Kernel { source })?;
    Ok((alias.compact, theorem))
}

fn compact_natural_theorems(
    init: &LogicalInit,
    kernel: &mut Kernel,
    mut naturals: Naturals,
) -> Result<Naturals, InitLibraryError> {
    macro_rules! compact {
        ($statement:ident) => {{
            let (statement, theorem) = compact_theorem(
                init,
                kernel,
                naturals.declaration.$statement,
                naturals.proof.$statement,
            )?;
            naturals.declaration.$statement = statement;
            naturals.proof.$statement = theorem;
        }};
    }
    compact!(zero_member);
    compact!(member_inhabited);
    compact!(rep_member);
    compact!(member_succ);
    compact!(induction);
    compact!(succ_injective);
    compact!(zero_ne_succ);
    Ok(naturals)
}

fn retarget_exact_syntax(
    init: &LogicalInit,
    kernel: &mut Kernel,
    generated: Ref,
    exact: Ref,
) -> Result<(), InitLibraryError> {
    let raw = kernel
        .lower_logical_tree(init, generated)
        .map_err(|source| InitLibraryError::Kernel { source })?;
    join_alpha_equivalent(kernel, raw.raw, exact)
        .map_err(|source| InitLibraryError::Syntax { source })?;
    Ok(())
}

fn open_infinity_structure(
    kernel: &mut Kernel,
    axiom: ThmId,
    declaration: InfinityDecl,
) -> Result<(ChosenModel, OpenedExists, OpenedExists), InitLibraryError> {
    let model = kernel
        .choose_model_at(axiom, declaration.model)
        .map_err(|source| InitLibraryError::Infinity {
            source: source.into(),
        })?;
    let map = open_exists_at(
        kernel,
        model.specification,
        OpenedExistsDecl {
            witness: declaration.map,
            body: declaration.missed_exists,
        },
    )
    .map_err(|source| InitLibraryError::Infinity {
        source: source.into(),
    })?;
    let missed = open_exists_at(
        kernel,
        map.body,
        OpenedExistsDecl {
            witness: declaration.missed,
            body: declaration.property,
        },
    )
    .map_err(|source| InitLibraryError::Infinity {
        source: source.into(),
    })?;
    Ok((model, map, missed))
}

#[derive(Clone, Copy)]
struct InfinityLawTargets {
    property: Ref,
    property_alias: Ref,
    reflects_equality: Ref,
    reflects_alias: Ref,
    avoids_missed: Ref,
    avoids_alias: Ref,
}

fn prove_infinity_laws(
    kernel: &mut Kernel,
    model_theorem: ThmId,
    specification: Ref,
    targets: InfinityLawTargets,
) -> Result<[ThmId; 3], KernelError> {
    let property_theorem = kernel.copy_theorem(model_theorem)?;
    kernel.convert_theorem(property_theorem, specification, targets.property)?;
    kernel.convert_theorem(property_theorem, targets.property, targets.property_alias)?;
    let conjunction = Lit::positive(targets.property_alias.get());
    let reflects_equality_theorem =
        kernel.expand_conclusion(property_theorem, conjunction, Some(false))?;
    let avoids_missed_theorem =
        kernel.expand_conclusion(property_theorem, conjunction, Some(true))?;
    kernel.convert_theorem(
        reflects_equality_theorem,
        targets.reflects_alias,
        targets.reflects_equality,
    )?;
    kernel.convert_theorem(
        avoids_missed_theorem,
        targets.avoids_alias,
        targets.avoids_missed,
    )?;
    kernel.convert_theorem(property_theorem, targets.property_alias, targets.property)?;
    Ok([
        property_theorem,
        reflects_equality_theorem,
        avoids_missed_theorem,
    ])
}

fn open_subtype_structure(
    kernel: &mut Kernel,
    axiom: ThmId,
    declaration: SubtypeDecl,
) -> Result<(ChosenModel, OpenedExists, OpenedExists), InitLibraryError> {
    let model = kernel
        .choose_model_at(
            axiom,
            declaration
                .model
                .ok_or(InitLibraryError::MissingSubtypeModel)?,
        )
        .map_err(|source| InitLibraryError::Subtype {
            source: source.into(),
        })?;
    let representation = open_exists_at(
        kernel,
        model.specification,
        OpenedExistsDecl {
            witness: declaration.rep,
            body: declaration.abs_exists,
        },
    )
    .map_err(|source| InitLibraryError::Subtype {
        source: source.into(),
    })?;
    let abstraction = open_exists_at(
        kernel,
        representation.body,
        OpenedExistsDecl {
            witness: declaration.abs,
            body: declaration.property,
        },
    )
    .map_err(|source| InitLibraryError::Subtype {
        source: source.into(),
    })?;
    Ok((model, representation, abstraction))
}

#[derive(Clone, Copy)]
struct SubtypeLawTargets {
    property: Ref,
    property_alias: Ref,
    abs_rep: Ref,
    abs_rep_alias: Ref,
    rep_property_alias: Ref,
    rep_abs: Ref,
    rep_abs_alias: Ref,
    rep_guarded: Ref,
    rep_guarded_alias: Ref,
}

fn prove_subtype_laws(
    kernel: &mut Kernel,
    model_theorem: ThmId,
    specification: Ref,
    targets: SubtypeLawTargets,
) -> Result<[ThmId; 4], KernelError> {
    let property_theorem = kernel.copy_theorem(model_theorem)?;
    kernel.convert_theorem(property_theorem, specification, targets.property)?;
    kernel.convert_theorem(property_theorem, targets.property, targets.property_alias)?;
    let property = Lit::positive(targets.property_alias.get());
    let abs_rep_theorem = kernel.expand_conclusion(property_theorem, property, Some(false))?;
    let rep_property_theorem = kernel.expand_conclusion(property_theorem, property, Some(true))?;
    let rep_property = Lit::positive(targets.rep_property_alias.get());
    let rep_abs_theorem =
        kernel.expand_conclusion(rep_property_theorem, rep_property, Some(false))?;
    let rep_guarded_theorem =
        kernel.expand_conclusion(rep_property_theorem, rep_property, Some(true))?;
    for (theorem, alias, exact) in [
        (abs_rep_theorem, targets.abs_rep_alias, targets.abs_rep),
        (rep_abs_theorem, targets.rep_abs_alias, targets.rep_abs),
        (
            rep_guarded_theorem,
            targets.rep_guarded_alias,
            targets.rep_guarded,
        ),
        (property_theorem, targets.property_alias, targets.property),
    ] {
        kernel.convert_theorem(theorem, alias, exact)?;
    }
    Ok([
        property_theorem,
        abs_rep_theorem,
        rep_abs_theorem,
        rep_guarded_theorem,
    ])
}

impl InitLibrary {
    /// Borrows the fully assembled checked kernel.
    #[must_use]
    pub const fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// Resolves one external init-library name.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<Ref> {
        self.symbols.get(name).copied()
    }

    /// Iterates all external names in lexical order.
    #[must_use]
    pub fn symbols(&self) -> impl ExactSizeIterator<Item = (&str, Ref)> {
        self.symbols
            .iter()
            .map(|(name, reference)| (name.as_str(), *reference))
    }

    /// Returns the selected natural-number package descriptor.
    #[must_use]
    pub const fn naturals(&self) -> &Naturals {
        &self.naturals
    }

    /// Returns the checked open schemata used for primitive recursion.
    #[must_use]
    pub const fn recursion_schemas(&self) -> NaturalRecSchemas {
        self.recursion_schemas
    }

    /// Returns the derived natural arithmetic package descriptor.
    #[must_use]
    pub const fn arithmetic(&self) -> &NaturalArithmetic {
        &self.arithmetic
    }

    /// Splits the standalone kernel from its untrusted name dictionary.
    #[must_use]
    pub fn into_parts(self) -> (Kernel, BTreeMap<String, Ref>) {
        (self.kernel, self.symbols)
    }

    /// Projects public syntax into a fresh opcode-free checked prefix.
    ///
    /// Proof rows, caches, and private construction intermediates are omitted.
    /// Compact logical rows reachable beneath public roots are recursively
    /// replaced with applications of the caller's authoritative raw logical
    /// definitions. The external dictionary is remapped to the projected rows.
    ///
    /// # Errors
    ///
    /// Returns an error if `init` is not the construction kernel's exact
    /// prefix, a public root cannot be copied and lowered, or a dictionary
    /// reference is not in the resulting reachable closure.
    pub fn into_slice(self, init: &LogicalInit) -> Result<InitSlice, InitLibraryError> {
        let mut roots = self.symbols.values().copied().collect::<Vec<_>>();
        roots.extend(self.naturals.declaration.references());
        roots.extend(self.arithmetic.declaration.references());
        let mut projected = init.kernel();
        projected
            .add_axiom(AX_INF)
            .map_err(|source| InitLibraryError::Kernel { source })?;
        projected
            .add_axiom(AX_SUB)
            .map_err(|source| InitLibraryError::Kernel { source })?;
        let copied = projected
            .copy_objects_lowered_from(init, &self.kernel, &roots)
            .map_err(|source| InitLibraryError::Kernel { source })?;
        let naturals = self.naturals.declaration.try_map(|source| {
            copied
                .get(source)
                .ok_or(InitLibraryError::UnmappedReference { reference: source })
        })?;
        let recursion_schemas = self.recursion_schemas.try_map(|source| {
            copied
                .get(source)
                .ok_or(InitLibraryError::UnmappedReference { reference: source })
        })?;
        let arithmetic = self.arithmetic.declaration.try_map(|source| {
            copied
                .get(source)
                .ok_or(InitLibraryError::UnmappedReference { reference: source })
        })?;
        let symbols = self
            .symbols
            .into_iter()
            .map(|(name, source)| {
                copied
                    .get(source)
                    .map(|destination| (name.clone(), destination))
                    .ok_or(InitLibraryError::UnmappedSymbol { name })
            })
            .collect::<Result<_, _>>()?;
        Ok(InitSlice {
            prefix: projected.into_checked_prefix(),
            symbols,
            recursion_schemas,
            naturals,
            arithmetic,
        })
    }
}

/// Failure to assemble the standard userspace init library.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum InitLibraryError {
    /// The untrusted source compiler rejected the standard source module.
    #[snafu(display("could not compile init-library source: {source}"))]
    Theory {
        /// Source compilation failure.
        source: TheoryError,
    },
    /// A required public schema name was absent from the compiled dictionary.
    #[snafu(display("init-library source does not define {name:?}"))]
    MissingSymbol {
        /// Required external name.
        name: &'static str,
    },
    /// Two independently assembled packages claimed the same external name.
    #[snafu(display("duplicate init-library symbol {name:?}"))]
    DuplicateSymbol {
        /// Colliding external name.
        name: String,
    },
    /// A named row was absent from the completed projection map.
    #[snafu(display("init-library symbol {name:?} was not projected"))]
    UnmappedSymbol {
        /// External name whose reference could not be remapped.
        name: String,
    },
    /// A typed package descriptor named a row absent from the projection map.
    #[snafu(display("init-library reference {reference:?} was not projected"))]
    UnmappedReference {
        /// Source reference absent from the completed copy map.
        reference: Ref,
    },
    /// A checked kernel capability could not be installed.
    #[snafu(display("could not install init-library capability: {source}"))]
    Kernel {
        /// Checked kernel failure.
        source: KernelError,
    },
    /// A userspace natural-number derivation was rejected.
    #[snafu(display("could not derive init-library naturals: {source}"))]
    Natural {
        /// Derived construction failure.
        source: NaturalError,
    },
    /// Exact foundational replay was rejected.
    #[snafu(display("could not replay init-library infinity: {source}"))]
    Infinity {
        /// Userspace infinity derivation failure.
        source: InfinityError,
    },
    /// Checked syntax transport during exact replay was rejected.
    #[snafu(display("could not transport init-library syntax: {source}"))]
    Syntax {
        /// Userspace syntax-certificate failure.
        source: SyntaxError,
    },
    /// The frozen natural package omitted its subtype axiom descriptor.
    #[snafu(display("init-library subtype declaration has no axiom"))]
    MissingSubtypeAxiom,
    /// The frozen natural package omitted its chosen subtype model descriptor.
    #[snafu(display("init-library subtype declaration has no chosen model"))]
    MissingSubtypeModel,
    /// A frozen subtype package omitted a theorem needed downstream.
    #[snafu(display("init-library subtype has no proved {law} law"))]
    MissingSubtypeProof {
        /// Missing law name.
        law: &'static str,
    },
    /// Exact guarded-subtype replay was rejected.
    #[snafu(display("could not replay init-library subtype: {source}"))]
    Subtype {
        /// Userspace subtype derivation failure.
        source: SubtypeError,
    },
}

/// Compiles and assembles the standard checked init-library workspace.
///
/// The caller supplies the authoritative opcode-free logical prefix. This
/// routine compiles [`crate::INIT_SOURCE`] with compact logical macros for the
/// userspace proof automation, installs the two explicit HOL capabilities
/// needed by the standard model construction, and derives the natural-number
/// and primitive-arithmetic packages. It returns the checked construction
/// workspace; producing a minimal opcode-free distribution slice is a
/// separate lowering/export operation. All orchestration and names remain
/// outside the trusted kernel.
///
/// # Errors
///
/// Returns an error if the source is rejected, a required schema is missing,
/// package names collide, a capability cannot be installed, or any derived
/// proof is rejected by the checked kernel.
pub fn compile_init_library(init: &LogicalInit) -> Result<InitLibrary, InitLibraryError> {
    let compiled = compile_theory_with_init(
        INIT_SOURCE,
        TheoryOptions {
            logic: LogicEncoding::Compact,
        },
        init,
    )
    .map_err(|source| InitLibraryError::Theory { source })?;
    let bool_ty = compiled.bool_type();
    let member_parameter = required(&compiled, "NatMember/'a")?;
    let member_schema = required(&compiled, "NatMember")?;
    let recursion_schemas = NaturalRecSchemas {
        graph: required(&compiled, "NatRecGraph")?,
        graph_natural: required(&compiled, "NatRecGraph/'a")?,
        graph_codomain: required(&compiled, "NatRecGraph/'c")?,
        specification: required(&compiled, "NatRecSpec")?,
        specification_natural: required(&compiled, "NatRecSpec/'a")?,
        specification_codomain: required(&compiled, "NatRecSpec/'c")?,
    };
    let (mut kernel, source_symbols) = compiled.into_parts();

    kernel
        .add_axiom(AX_INF)
        .map_err(|source| InitLibraryError::Kernel { source })?;
    kernel
        .add_axiom(AX_SUB)
        .map_err(|source| InitLibraryError::Kernel { source })?;
    let naturals = kernel
        .choose_naturals_from_member_schema(bool_ty, member_parameter, member_schema)
        .map_err(|source| InitLibraryError::Natural { source })?;
    let arithmetic = kernel
        .natural_arithmetic(&naturals, recursion_schemas)
        .map_err(|source| InitLibraryError::Natural { source })?;

    let mut symbols = BTreeMap::new();
    extend_symbols(&mut symbols, init.names())?;
    extend_symbols(&mut symbols, source_symbols)?;
    extend_symbols(&mut symbols, naturals.symbols())?;
    extend_symbols(&mut symbols, arithmetic.symbols())?;

    Ok(InitLibrary {
        kernel,
        symbols,
        naturals,
        recursion_schemas,
        arithmetic,
    })
}

/// Assembles and projects the canonical opcode-free init slice.
///
/// This is a userspace composition of [`compile_init_library`] and
/// [`InitLibrary::into_slice`]. No parser, name, or projection decision is
/// trusted by the returned kernel prefix.
///
/// # Errors
///
/// Returns any source, derivation, collision, or projection error reported by
/// the two underlying userspace stages.
pub fn compile_init_slice(init: &LogicalInit) -> Result<InitSlice, InitLibraryError> {
    compile_init_library(init)?.into_slice(init)
}

fn required(compiled: &CompiledTheory, name: &'static str) -> Result<Ref, InitLibraryError> {
    compiled
        .get(name)
        .ok_or(InitLibraryError::MissingSymbol { name })
}

fn extend_symbols<K, I>(
    target: &mut BTreeMap<String, Ref>,
    symbols: I,
) -> Result<(), InitLibraryError>
where
    K: Into<String>,
    I: IntoIterator<Item = (K, Ref)>,
{
    for (name, reference) in symbols {
        let name = name.into();
        if target.insert(name.clone(), reference).is_some() {
            return Err(InitLibraryError::DuplicateSymbol { name });
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{InitLibraryError, extend_symbols};
    use covalence_logic_hol::Ref;
    use std::collections::BTreeMap;

    #[test]
    fn independently_owned_names_must_not_collide() {
        let reference = Ref::new(1).expect("reference");
        let mut symbols = BTreeMap::new();
        extend_symbols(&mut symbols, [("shared", reference)]).expect("first package");
        assert!(matches!(
            extend_symbols(&mut symbols, [("shared", reference)]),
            Err(InitLibraryError::DuplicateSymbol { name }) if name == "shared"
        ));
    }
}
