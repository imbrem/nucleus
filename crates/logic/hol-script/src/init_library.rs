//! Reproducible userspace assembly of the standard checked init library.

use std::collections::BTreeMap;

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{
    AX_INF, AX_SUB, Kernel, KernelError, Ref, init::Compiled as LogicalInit,
};
use covalence_logic_hol_derived::{
    NaturalArithmetic, NaturalArithmeticExt, NaturalError, NaturalExt, NaturalRecSchemas, Naturals,
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
