//! Backend-parametric streaming import driver.

use std::collections::BTreeMap;
use std::error::Error as StdError;
use std::io::BufRead;

use covalence_lib_error::snafu::Snafu;

use crate::decode::{self, Decoder, Event};
use crate::lean4export::Metadata;
use crate::stream::{self, ForEachError};
use crate::syntax::{LeanSyntax, Record, Tables};

/// Objects and derivations emitted while lowering one input record.
#[derive(Clone, Debug)]
pub struct Artifacts<O, T, D> {
    /// Correspondence from backend/HOL objects to source Lean syntax.
    pub objects: Vec<(O, LeanSyntax)>,
    /// Correspondence from backend theorem handles to derivations.
    pub theorems: Vec<(T, D)>,
}

/// Artifact bundle emitted by a particular backend.
pub type BackendArtifacts<B> =
    Artifacts<<B as Backend>::Object, <B as Backend>::Theorem, <B as Backend>::Derivation>;

impl<O, T, D> Default for Artifacts<O, T, D> {
    fn default() -> Self {
        Self {
            objects: Vec::new(),
            theorems: Vec::new(),
        }
    }
}

/// A lowering implementation driven by typed records in streaming order.
///
/// A backend may emit artifacts eagerly (as a deep embedding naturally does)
/// or defer expression lowering until a declaration supplies context and an
/// expected type (as direct lowering often must).
pub trait Backend {
    /// Stable object handle, normally [`covalence_logic_hol::Ref`].
    type Object: Copy + Ord;
    /// Stable theorem handle, normally [`covalence_logic_hol::ThmId`].
    type Theorem: Copy + Ord;
    /// Backend-owned account of the derivation represented by a theorem.
    type Derivation;
    /// A rejected lowering or derivation request.
    type Error: StdError + 'static;

    /// Initialize lowering after the required metadata record.
    ///
    /// The returned artifacts may include the implicit anonymous name and zero
    /// universe level, which have no physical records of their own.
    ///
    /// # Errors
    ///
    /// Returns a backend error if its HOL prelude or initial state cannot be
    /// established.
    fn begin(
        &mut self,
        metadata: &Metadata,
        tables: &Tables,
    ) -> Result<BackendArtifacts<Self>, Self::Error>;

    /// Lower one record using all typed backward-reference tables available at
    /// that point.
    ///
    /// # Errors
    ///
    /// Returns a backend error if the requested HOL construction or derivation
    /// does not succeed. Unsupported syntax is a backend error, not a parse
    /// failure.
    fn lower(
        &mut self,
        record: &Record,
        tables: &Tables,
    ) -> Result<BackendArtifacts<Self>, Self::Error>;
}

/// Successful import, including the backend state and both requested mappings.
#[derive(Debug)]
pub struct Imported<B: Backend> {
    backend: B,
    metadata: Metadata,
    tables: Tables,
    hol_to_lean: BTreeMap<B::Object, Vec<LeanSyntax>>,
    theorem_derivations: BTreeMap<B::Theorem, B::Derivation>,
}

impl<B: Backend> Imported<B> {
    /// Consume the result and recover the completed backend, including its
    /// kernel or other target state.
    #[must_use]
    pub fn into_backend(self) -> B {
        self.backend
    }

    /// Borrow the completed backend.
    #[must_use]
    pub const fn backend(&self) -> &B {
        &self.backend
    }

    /// Borrow pinned producer metadata.
    #[must_use]
    pub const fn metadata(&self) -> &Metadata {
        &self.metadata
    }

    /// Borrow every typed source table accumulated during streaming.
    #[must_use]
    pub const fn tables(&self) -> &Tables {
        &self.tables
    }

    /// Map backend/HOL objects back to the Lean syntax that produced them.
    #[must_use]
    pub const fn hol_to_lean(&self) -> &BTreeMap<B::Object, Vec<LeanSyntax>> {
        &self.hol_to_lean
    }

    /// Map retained theorem handles to their backend derivation accounts.
    ///
    /// Handles are scoped to [`Self::backend`]. A backend using reusable theorem
    /// slots must keep these slots resident for the lifetime of this result.
    #[must_use]
    pub const fn theorem_derivations(&self) -> &BTreeMap<B::Theorem, B::Derivation> {
        &self.theorem_derivations
    }
}

/// A framing, schema, backend, or correspondence failure.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ImportError<E: StdError + 'static> {
    /// Generic NDJSON framing failed.
    #[snafu(display("could not frame Lean export: {source}"))]
    Framing { source: stream::Error },
    /// A JSON record did not decode to pinned Lean syntax.
    #[snafu(display("could not decode Lean export: {source}"))]
    Decode { source: decode::Error },
    /// The selected backend rejected a construction or derivation.
    #[snafu(display("Lean lowering failed on line {line}: {source}"))]
    Backend { line: usize, source: E },
    /// One theorem handle was attributed to two derivations.
    #[snafu(display("backend emitted a duplicate theorem correspondence on line {line}"))]
    DuplicateTheorem { line: usize },
    /// The stream ended without its required metadata record.
    #[snafu(display("Lean export has no metadata record"))]
    MissingMetadata,
}

/// Stream a pinned export through an arbitrary lowering backend.
///
/// Parsing performs no declaration-safety filtering. Every decoded declaration,
/// including unsafe or partial definitions, is delivered to `backend`; only the
/// selected lowering rules determine whether it succeeds.
///
/// # Errors
///
/// Returns [`ImportError`] for malformed NDJSON/schema data, a backend failure,
/// or conflicting correspondence keys. The backend is consumed on error so a
/// partially mutated kernel cannot accidentally escape as a successful import.
pub fn import<R: BufRead, B: Backend>(
    reader: R,
    mut backend: B,
) -> Result<Imported<B>, ImportError<B::Error>> {
    let mut decoder = Decoder::new();
    let mut metadata = None;
    let mut hol_to_lean = BTreeMap::new();
    let mut theorem_derivations = BTreeMap::new();

    let result = stream::for_each(reader, |line, value| {
        let event = decoder.accept(line, &value).map_err(VisitError::Decode)?;
        let artifacts = match event {
            Event::Metadata(value) => {
                metadata = Some(value.clone());
                backend
                    .begin(&value, decoder.tables())
                    .map_err(|source| VisitError::backend(line, source))?
            }
            Event::Record(record) => backend
                .lower(&record, decoder.tables())
                .map_err(|source| VisitError::backend(line, source))?,
        };
        merge_artifacts::<B>(line, artifacts, &mut hol_to_lean, &mut theorem_derivations)
            .map_err(VisitError::Correspondence)
    });

    match result {
        Ok(()) => {}
        Err(ForEachError::Framing(source)) => return Err(ImportError::Framing { source }),
        Err(ForEachError::Visitor(VisitError::Decode(source))) => {
            return Err(ImportError::Decode { source });
        }
        Err(ForEachError::Visitor(VisitError::Backend { line, source })) => {
            return Err(ImportError::Backend { line, source });
        }
        Err(ForEachError::Visitor(VisitError::Correspondence(error))) => return Err(error),
    }
    let metadata = metadata.ok_or(ImportError::MissingMetadata)?;
    let tables = decoder
        .finish()
        .map_err(|source| ImportError::Decode { source })?;
    Ok(Imported {
        backend,
        metadata,
        tables,
        hol_to_lean,
        theorem_derivations,
    })
}

enum VisitError<E: StdError + 'static> {
    Decode(decode::Error),
    Backend { line: usize, source: E },
    Correspondence(ImportError<E>),
}

impl<E: StdError + 'static> VisitError<E> {
    fn backend(line: usize, source: E) -> Self {
        Self::Backend { line, source }
    }
}

fn merge_artifacts<B: Backend>(
    line: usize,
    artifacts: Artifacts<B::Object, B::Theorem, B::Derivation>,
    objects: &mut BTreeMap<B::Object, Vec<LeanSyntax>>,
    theorems: &mut BTreeMap<B::Theorem, B::Derivation>,
) -> Result<(), ImportError<B::Error>> {
    for (object, syntax) in artifacts.objects {
        objects.entry(object).or_default().push(syntax);
    }
    for (theorem, derivation) in artifacts.theorems {
        if theorems.insert(theorem, derivation).is_some() {
            return Err(ImportError::DuplicateTheorem { line });
        }
    }
    Ok(())
}
