//! Generic exhaustive lowering over selected coverage cases.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Debug,
};

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref, Sort};

use crate::{CoverageDisposition, CoveragePlan, KernelRoot};

/// One validated role-labelled root for a selected translation case.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SelectedRoot {
    role: String,
    reference: Ref,
    sort: Sort,
}

impl SelectedRoot {
    /// Returns the case-local root role.
    #[must_use]
    pub fn role(&self) -> &str {
        &self.role
    }

    /// Returns the exact resident arena row.
    #[must_use]
    pub const fn reference(&self) -> Ref {
        self.reference
    }

    /// Returns the checked syntactic category.
    #[must_use]
    pub const fn sort(&self) -> Sort {
        self.sort
    }
}

/// Transactional checked lowering whose required cases come from a plan.
#[derive(Debug)]
pub struct SelectedCompiler<Case> {
    kernel: Kernel,
    required: BTreeSet<Case>,
    completed: BTreeMap<Case, Vec<SelectedRoot>>,
}

impl<Case> SelectedCompiler<Case>
where
    Case: Copy + Debug + Ord,
{
    /// Creates a compiler for exactly the translated cases in `plan`.
    ///
    /// Explicit rejections require no callback. A translated case occurring
    /// under two selectors is rejected rather than silently sharing one
    /// lowering.
    ///
    /// # Errors
    ///
    /// Returns an error if a case occurs more than once in the plan.
    pub fn new<Reject, Source>(
        plan: &CoveragePlan<CoverageDisposition<Case, Reject, Source>>,
        kernel: Kernel,
    ) -> Result<Self, SelectedCompileError> {
        let mut required = BTreeSet::new();
        for disposition in plan
            .declarations()
            .iter()
            .map(|entry| &entry.disposition)
            .chain(plan.clauses().iter().map(|entry| &entry.disposition))
            .chain(plan.rules().iter().map(|entry| &entry.disposition))
        {
            if let CoverageDisposition::Translate { case, .. } = disposition
                && !required.insert(*case)
            {
                return Err(SelectedCompileError::DuplicateCase {
                    case: format!("{case:?}"),
                });
            }
        }
        Ok(Self {
            kernel,
            required,
            completed: BTreeMap::new(),
        })
    }

    /// Borrows the current checked state.
    #[must_use]
    pub const fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// Returns the number of translated cases required by the plan.
    #[must_use]
    pub fn required(&self) -> usize {
        self.required.len()
    }

    /// Returns the number of cases lowered exactly once so far.
    #[must_use]
    pub fn completed(&self) -> usize {
        self.completed.len()
    }

    /// Returns the validated roots already recorded for `case`.
    #[must_use]
    pub fn roots(&self, case: Case) -> Option<&[SelectedRoot]> {
        self.completed.get(&case).map(Vec::as_slice)
    }

    /// Lowers one selected case transactionally.
    ///
    /// # Errors
    ///
    /// Returns an error if the case was rejected or absent, was already
    /// lowered, the callback fails, or its roots are empty, ambiguously named,
    /// or absent from the staged checked kernel.
    pub fn lower<F>(&mut self, case: Case, operation: F) -> Result<(), SelectedCompileError>
    where
        F: FnOnce(&mut Kernel) -> Result<Vec<KernelRoot>, KernelError>,
    {
        let label = || format!("{case:?}");
        if !self.required.contains(&case) {
            return Err(SelectedCompileError::UnknownCase { case: label() });
        }
        if self.completed.contains_key(&case) {
            return Err(SelectedCompileError::AlreadyLowered { case: label() });
        }
        let mut staged = self.kernel.fork();
        let roots =
            operation(&mut staged).map_err(|source| SelectedCompileError::Kernel { source })?;
        if roots.is_empty() {
            return Err(SelectedCompileError::NoRoots { case: label() });
        }
        let mut roles = BTreeSet::new();
        let mut selected = Vec::with_capacity(roots.len());
        for root in roots {
            if root.role().is_empty() {
                return Err(SelectedCompileError::EmptyRole { case: label() });
            }
            if !roles.insert(root.role().to_owned()) {
                return Err(SelectedCompileError::DuplicateRole {
                    case: label(),
                    role: root.role().to_owned(),
                });
            }
            let sort = staged
                .category(root.reference())
                .map_err(|source| SelectedCompileError::Kernel { source })?;
            selected.push(SelectedRoot {
                role: root.role().to_owned(),
                reference: root.reference(),
                sort,
            });
        }
        self.kernel = staged;
        self.completed.insert(case, selected);
        Ok(())
    }

    /// Finishes only after every translated case has one checked lowering.
    ///
    /// # Errors
    ///
    /// Returns the first missing case in case order.
    pub fn finish(self) -> Result<SelectedKernel<Case>, SelectedCompileError> {
        if let Some(case) = self
            .required
            .iter()
            .find(|case| !self.completed.contains_key(case))
        {
            return Err(SelectedCompileError::MissingCase {
                case: format!("{case:?}"),
            });
        }
        Ok(SelectedKernel {
            kernel: self.kernel,
            roots: self.completed,
        })
    }
}

/// Complete checked state and roots for every translated case.
#[derive(Debug)]
pub struct SelectedKernel<Case> {
    kernel: Kernel,
    roots: BTreeMap<Case, Vec<SelectedRoot>>,
}

impl<Case: Ord> SelectedKernel<Case> {
    /// Borrows the complete checked state.
    #[must_use]
    pub const fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// Returns one completed case's roots.
    #[must_use]
    pub fn roots(&self, case: &Case) -> Option<&[SelectedRoot]> {
        self.roots.get(case).map(Vec::as_slice)
    }

    /// Decomposes the result without cloning the checked state or roots.
    #[must_use]
    pub fn into_parts(self) -> (Kernel, BTreeMap<Case, Vec<SelectedRoot>>) {
        (self.kernel, self.roots)
    }
}

/// Why selected-case lowering could not proceed or finish.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum SelectedCompileError {
    /// One case was selected by more than one source form.
    #[snafu(display("translation case {case} occurs more than once"))]
    DuplicateCase { case: String },
    /// A callback targeted an absent or explicitly rejected case.
    #[snafu(display("translation case {case} is not selected"))]
    UnknownCase { case: String },
    /// A selected case was lowered twice.
    #[snafu(display("translation case {case} was already lowered"))]
    AlreadyLowered { case: String },
    /// A selected case returned no correspondence roots.
    #[snafu(display("translation case {case} produced no kernel roots"))]
    NoRoots { case: String },
    /// A selected case returned an empty role.
    #[snafu(display("translation case {case} produced an empty root role"))]
    EmptyRole { case: String },
    /// A selected case repeated a role.
    #[snafu(display("translation case {case} repeated root role {role:?}"))]
    DuplicateRole { case: String, role: String },
    /// A checked kernel operation rejected a lowering.
    #[snafu(display("checked selected-case lowering failed: {source}"))]
    Kernel { source: KernelError },
    /// A selected case remained unlowered at finish time.
    #[snafu(display("translation case {case} has not been lowered"))]
    MissingCase { case: String },
}
