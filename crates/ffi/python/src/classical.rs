//! Tagged classical syntax at the Python boundary.

#![allow(clippy::needless_pass_by_value)]

use covalence_lib_python::exceptions::PyValueError;
use covalence_lib_python::prelude::*;
use covalence_logic_classical::{
    Checked, ClassicalKernel, Formula, FormulaKind, FormulaPath, ModelWitness, Sequent, Side,
    Theorem,
};

fn rejection(error: impl std::fmt::Display) -> PyErr {
    PyValueError::new_err(error.to_string())
}

/// An owned classical formula.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.classical",
    name = "ClassicalFormula"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone)]
pub struct PyFormula(Formula);

fn children(values: Vec<PyRef<'_, PyFormula>>) -> Vec<Formula> {
    values.iter().map(|value| value.0.clone()).collect()
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyFormula {
    #[staticmethod]
    #[pyo3(signature = (atom, negative = false))]
    fn literal(atom: u32, negative: bool) -> Self {
        Self(Formula::Literal { atom, negative })
    }

    #[staticmethod]
    #[pyo3(signature = (values, negative = false))]
    fn and_(values: Vec<PyRef<'_, Self>>, negative: bool) -> Self {
        Self(Formula::And {
            negative,
            children: children(values),
        })
    }

    #[staticmethod]
    #[pyo3(signature = (values, negative = false))]
    fn or_(values: Vec<PyRef<'_, Self>>, negative: bool) -> Self {
        Self(Formula::Or {
            negative,
            children: children(values),
        })
    }

    #[staticmethod]
    #[pyo3(signature = (values, negative = false))]
    fn sat(values: Vec<PyRef<'_, Self>>, negative: bool) -> Self {
        Self(Formula::Sat {
            negative,
            children: children(values),
        })
    }

    fn negated(&self) -> Self {
        Self(self.0.clone().negated())
    }

    #[getter]
    const fn kind(&self) -> &'static str {
        match self.0 {
            Formula::Literal { .. } => "literal",
            Formula::And { .. } => "and",
            Formula::Or { .. } => "or",
            Formula::Sat { .. } => "sat",
        }
    }

    #[getter]
    const fn negative(&self) -> bool {
        match &self.0 {
            Formula::Literal { negative, .. }
            | Formula::And { negative, .. }
            | Formula::Or { negative, .. }
            | Formula::Sat { negative, .. } => *negative,
        }
    }

    #[getter]
    const fn atom(&self) -> Option<u32> {
        match self.0 {
            Formula::Literal { atom, .. } => Some(atom),
            _ => None,
        }
    }

    #[getter]
    fn children(&self) -> Vec<Self> {
        match &self.0 {
            Formula::Literal { .. } => Vec::new(),
            Formula::And { children, .. }
            | Formula::Or { children, .. }
            | Formula::Sat { children, .. } => children.iter().cloned().map(Self).collect(),
        }
    }

    fn __eq__(&self, other: PyRef<'_, Self>) -> bool {
        self.0 == other.0
    }

    fn __repr__(&self) -> String {
        format!("{:?}", self.0)
    }
}

/// An owned classical implication.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.classical",
    name = "ClassicalSequent"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone)]
pub struct PySequent(pub(crate) Sequent);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PySequent {
    #[new]
    fn new(premise: PyRef<'_, PyFormula>, conclusion: PyRef<'_, PyFormula>) -> Self {
        Self(Sequent {
            premise: premise.0.clone(),
            conclusion: conclusion.0.clone(),
        })
    }

    #[getter]
    fn premise(&self) -> PyFormula {
        PyFormula(self.0.premise.clone())
    }

    #[getter]
    fn conclusion(&self) -> PyFormula {
        PyFormula(self.0.conclusion.clone())
    }
}

/// An unchecked collection of owned classical sequents.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.classical",
    name = "ClassicalArena"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone)]
pub struct PyArena {
    sequents: Vec<Sequent>,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyArena {
    #[new]
    fn new(values: Vec<PyRef<'_, PySequent>>) -> Self {
        Self {
            sequents: values.iter().map(|value| value.0.clone()).collect(),
        }
    }

    #[getter]
    fn sequents(&self) -> Vec<PySequent> {
        self.sequents.iter().cloned().map(PySequent).collect()
    }

    fn check(&self) -> PyResult<PyCheckedArena> {
        Checked::from_sequents(&self.sequents)
            .map(PyCheckedArena)
            .map_err(rejection)
    }
}

/// Validated classical arena syntax without theorem authority.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.classical",
    name = "ClassicalCheckedArena"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone)]
pub struct PyCheckedArena(Checked);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyCheckedArena {
    #[staticmethod]
    fn from_sequents(values: Vec<PyRef<'_, PySequent>>) -> PyResult<Self> {
        let sequents = values
            .iter()
            .map(|value| value.0.clone())
            .collect::<Vec<_>>();
        Checked::from_sequents(&sequents)
            .map(Self)
            .map_err(rejection)
    }

    fn to_arena(&self) -> PyResult<PyArena> {
        self.0
            .decode_sequents()
            .map(|sequents| PyArena { sequents })
            .map_err(rejection)
    }

    #[getter]
    fn sequents(&self) -> PyResult<Vec<PySequent>> {
        self.0
            .decode_sequents()
            .map(|values| values.into_iter().map(PySequent).collect())
            .map_err(rejection)
    }

    fn __len__(&self) -> usize {
        self.0.len()
    }

    fn sequent(slf: Py<Self>, index: usize, python: Python<'_>) -> PyResult<PySequentView> {
        if slf.bind(python).borrow().0.view(index).is_none() {
            return Err(PyValueError::new_err("sequent index is out of range"));
        }
        Ok(PySequentView { owner: slf, index })
    }

    fn formula(
        slf: Py<Self>,
        path: PyRef<'_, PyPath>,
        python: Python<'_>,
    ) -> PyResult<PyFormulaView> {
        let view = PyFormulaView {
            owner: slf,
            sequent: path.sequent,
            side: path.side,
            indices: path.indices.clone(),
        };
        if view.get(&view.owner.bind(python).borrow()).is_none() {
            return Err(PyValueError::new_err("formula path is out of range"));
        }
        Ok(view)
    }
}

/// A theorem fact constructible only through checked rules.
#[pyclass(
    skip_from_py_object,
    module = "covalence.logic.classical",
    name = "ClassicalTheorem"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone)]
pub struct PyTheorem(Theorem);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyTheorem {
    #[staticmethod]
    fn identity(formula: PyRef<'_, PyFormula>) -> PyResult<Self> {
        Theorem::identity(formula.0.clone())
            .map(Self)
            .map_err(rejection)
    }

    #[staticmethod]
    fn sat_intro(values: Vec<PyRef<'_, PyFormula>>) -> PyResult<Self> {
        Theorem::sat_intro(children(values))
            .map(Self)
            .map_err(rejection)
    }

    #[staticmethod]
    fn prove_sat(witness: PyRef<'_, PyModelWitness>) -> PyResult<Self> {
        Theorem::prove_sat(&witness.0).map(Self).map_err(rejection)
    }

    #[staticmethod]
    fn model_sat_implication(
        premise: PyRef<'_, PyModelWitness>,
        conclusion: PyRef<'_, PyModelWitness>,
    ) -> PyResult<Self> {
        Theorem::model_sat_implication(&premise.0, &conclusion.0)
            .map(Self)
            .map_err(rejection)
    }

    #[staticmethod]
    fn truth_intro(premise: PyRef<'_, PyFormula>) -> PyResult<Self> {
        Theorem::truth_intro(premise.0.clone())
            .map(Self)
            .map_err(rejection)
    }

    #[staticmethod]
    fn from_refutation(refutation: PyRef<'_, crate::lrat::PyRefutation>) -> PyResult<Self> {
        let mut kernel = ClassicalKernel::new();
        let id = kernel.copy_refutation(&refutation.0).map_err(rejection)?;
        kernel
            .theorem_fact(id)
            .cloned()
            .map(Self)
            .ok_or_else(|| rejection("checked refutation theorem is absent"))
    }

    #[getter]
    fn sequents(&self) -> PyResult<Vec<PySequent>> {
        self.0
            .checked()
            .decode_sequents()
            .map(|values| values.into_iter().map(PySequent).collect())
            .map_err(rejection)
    }

    fn push(&mut self, index: usize, side: &str, formula: PyRef<'_, PyFormula>) -> PyResult<()> {
        self.0
            .weaken_mut(index, parse_side(side)?, &formula.0)
            .map_err(rejection)
    }

    fn pop(&mut self, index: usize, side: &str) -> PyResult<()> {
        self.0
            .pop_weaken_mut(index, parse_side(side)?)
            .map_err(rejection)
    }

    fn cross(&mut self, index: usize, source: &str) -> PyResult<()> {
        self.0
            .cross_root_mut(index, parse_side(source)?)
            .map_err(rejection)
    }

    fn demorgan(&mut self, path: PyRef<'_, PyPath>) -> PyResult<()> {
        self.0.demorgan_mut(&path.value()).map_err(rejection)
    }

    fn contradiction_local(
        &mut self,
        path: PyRef<'_, PyPath>,
        first: usize,
        second: usize,
    ) -> PyResult<()> {
        self.0
            .contradiction_mut(&path.value(), first, second)
            .map_err(rejection)
    }

    fn flatten(&mut self, path: PyRef<'_, PyPath>, child: usize) -> PyResult<()> {
        self.0.flatten_mut(&path.value(), child).map_err(rejection)
    }

    fn permute(&mut self, path: PyRef<'_, PyPath>, order: Vec<usize>) -> PyResult<()> {
        self.0.permute_mut(&path.value(), &order).map_err(rejection)
    }

    fn dedup_local(
        &mut self,
        path: PyRef<'_, PyPath>,
        remove: usize,
        retain: usize,
    ) -> PyResult<()> {
        self.0
            .dedup_local_mut(&path.value(), remove, retain)
            .map_err(rejection)
    }

    fn rewrite_equivalent(
        &mut self,
        path: PyRef<'_, PyPath>,
        forward: PyRef<'_, Self>,
        backward: PyRef<'_, Self>,
    ) -> PyResult<()> {
        self.0 = self
            .0
            .rewrite_equivalent(&path.value(), &forward.0, &backward.0)
            .map_err(rejection)?;
        Ok(())
    }

    fn refutation_to_false(&mut self, index: usize) -> PyResult<()> {
        self.0 = self.0.refutation_to_false(index).map_err(rejection)?;
        Ok(())
    }
}

fn parse_side(side: &str) -> PyResult<Side> {
    match side {
        "left" => Ok(Side::Left),
        "right" => Ok(Side::Right),
        _ => Err(PyValueError::new_err("side must be 'left' or 'right'")),
    }
}

/// A view of one checked sequent without decoding its formula storage.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.classical",
    name = "ClassicalSequentView"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PySequentView {
    owner: Py<PyCheckedArena>,
    index: usize,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PySequentView {
    #[getter]
    fn premise(&self, python: Python<'_>) -> PyFormulaView {
        PyFormulaView {
            owner: self.owner.clone_ref(python),
            sequent: self.index,
            side: Side::Left,
            indices: Vec::new(),
        }
    }

    #[getter]
    fn conclusion(&self, python: Python<'_>) -> PyFormulaView {
        PyFormulaView {
            owner: self.owner.clone_ref(python),
            sequent: self.index,
            side: Side::Right,
            indices: Vec::new(),
        }
    }
}

/// A view of one formula without decoding its stored subtree.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.classical",
    name = "ClassicalFormulaView"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
pub struct PyFormulaView {
    owner: Py<PyCheckedArena>,
    sequent: usize,
    side: Side,
    indices: Vec<usize>,
}

impl PyFormulaView {
    fn get<'a>(
        &'a self,
        owner: &'a PyCheckedArena,
    ) -> Option<covalence_logic_classical::FormulaView<'a>> {
        let root = owner.0.view(self.sequent)?;
        let mut view = match self.side {
            Side::Left => root.premise,
            Side::Right => root.conclusion,
        };
        for index in &self.indices {
            view = view.child(*index)?;
        }
        Some(view)
    }

    fn with_view<T>(
        &self,
        python: Python<'_>,
        f: impl FnOnce(covalence_logic_classical::FormulaView<'_>) -> T,
    ) -> T {
        let owner = self.owner.bind(python).borrow();
        f(self
            .get(&owner)
            .expect("checked formula-view path remains valid"))
    }
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyFormulaView {
    #[getter]
    fn kind(&self, python: Python<'_>) -> &'static str {
        self.with_view(python, |view| match view.kind() {
            FormulaKind::And => "and",
            FormulaKind::Or => "or",
            FormulaKind::Sat => "sat",
            FormulaKind::Literal => "literal",
        })
    }

    #[getter]
    #[allow(clippy::redundant_closure_for_method_calls)]
    fn negative(&self, python: Python<'_>) -> bool {
        self.with_view(python, |view| view.is_negative())
    }

    #[getter]
    #[allow(clippy::redundant_closure_for_method_calls)]
    fn atom(&self, python: Python<'_>) -> Option<u32> {
        self.with_view(python, |view| view.atom())
    }

    #[allow(clippy::redundant_closure_for_method_calls)]
    fn __len__(&self, python: Python<'_>) -> usize {
        self.with_view(python, |view| view.len())
    }

    fn child(&self, index: usize, python: Python<'_>) -> PyResult<Self> {
        if self.with_view(python, |view| view.child(index).is_none()) {
            return Err(PyValueError::new_err("formula child index is out of range"));
        }
        let mut indices = self.indices.clone();
        indices.push(index);
        Ok(Self {
            owner: self.owner.clone_ref(python),
            sequent: self.sequent,
            side: self.side,
            indices,
        })
    }

    fn structurally_equal(&self, other: &Self, python: Python<'_>) -> bool {
        let left_owner = self.owner.bind(python).borrow();
        let right_owner = other.owner.bind(python).borrow();
        let Some(left) = self.get(&left_owner) else {
            return false;
        };
        let Some(right) = other.get(&right_owner) else {
            return false;
        };
        left.structural_eq(right)
    }
}

/// A stable route from a sequent root to a nested formula.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.classical",
    name = "ClassicalPath"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone)]
pub struct PyPath {
    sequent: usize,
    side: Side,
    indices: Vec<usize>,
}

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyPath {
    #[new]
    fn new(sequent: usize, side: &str, indices: Vec<usize>) -> PyResult<Self> {
        let side = parse_side(side)?;
        Ok(Self {
            sequent,
            side,
            indices,
        })
    }

    #[getter]
    const fn sequent(&self) -> usize {
        self.sequent
    }

    #[getter]
    const fn side(&self) -> &'static str {
        match self.side {
            Side::Left => "left",
            Side::Right => "right",
        }
    }

    #[getter]
    fn indices(&self) -> Vec<usize> {
        self.indices.clone()
    }

    fn child(&self, index: usize) -> Self {
        let mut path = self.clone();
        path.indices.push(index);
        path
    }
}

impl PyPath {
    fn value(&self) -> FormulaPath {
        FormulaPath::new(self.sequent, self.side, self.indices.clone())
    }
}

/// A conjunction validated under an explicit Boolean assignment.
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "covalence.logic.classical",
    name = "ClassicalModelWitness"
)]
#[pyo3(crate = "covalence_lib_python::pyo3")]
#[derive(Clone)]
pub struct PyModelWitness(ModelWitness);

#[pymethods]
#[pyo3(crate = "covalence_lib_python::pyo3")]
impl PyModelWitness {
    #[staticmethod]
    fn check(values: Vec<PyRef<'_, PyFormula>>, true_atoms: Vec<u32>) -> PyResult<Self> {
        ModelWitness::check(children(values), true_atoms)
            .map(Self)
            .map_err(rejection)
    }
}

pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyFormula>()?;
    module.add_class::<PySequent>()?;
    module.add_class::<PyArena>()?;
    module.add_class::<PyCheckedArena>()?;
    module.add_class::<PyTheorem>()?;
    module.add_class::<PySequentView>()?;
    module.add_class::<PyFormulaView>()?;
    module.add_class::<PyPath>()?;
    module.add_class::<PyModelWitness>()
}
