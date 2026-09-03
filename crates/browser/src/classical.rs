//! Userspace classical matrices and checked LRAT replay for WebAssembly.

use covalence_logic_classical::{
    ClassicalKernel as Kernel, Lit, LitVec, Matrix as NativeMatrix, Refutation as NativeRefutation,
    ThmId,
};
use covalence_logic_lrat::{
    Formula,
    parse::{parse_binary, parse_binary_dimacs, parse_dimacs, parse_text},
    replay,
};
use wasm_bindgen::prelude::*;

fn error(error: impl std::fmt::Display) -> JsError {
    JsError::new(&error.to_string())
}

fn parse_rows(text: &str) -> Result<Vec<LitVec>, JsError> {
    covalence_lib_json::from_str::<Vec<Vec<i32>>>(text)
        .map_err(error)?
        .into_iter()
        .map(|row| {
            row.into_iter()
                .map(|literal| Lit::try_new(literal).map_err(error))
                .collect()
        })
        .collect()
}

fn rows_json(rows: impl Iterator<Item = Vec<i32>>) -> Result<String, JsError> {
    covalence_lib_json::to_string(&rows.collect::<Vec<_>>()).map_err(error)
}

fn formula(cnf: &NativeMatrix) -> Result<Formula, JsError> {
    Formula::from_signed(
        cnf.rows()
            .map(|row| row.iter().map(|literal| i64::from(literal.get()))),
    )
    .map_err(error)
}

/// A non-normal CNF matrix preserving row and literal order.
#[wasm_bindgen]
pub struct Cnf(pub(crate) NativeMatrix);

#[wasm_bindgen]
impl Cnf {
    /// Constructs a CNF from a JSON array of signed-i32 rows.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed JSON or literals.
    #[wasm_bindgen(constructor)]
    pub fn new(rows: &str) -> Result<Self, JsError> {
        Ok(Self(NativeMatrix::new(parse_rows(rows)?)))
    }

    /// Parses a DIMACS CNF byte stream.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed DIMACS or values outside signed `i32`.
    #[wasm_bindgen(js_name = fromDimacs)]
    pub fn from_dimacs(bytes: &[u8]) -> Result<Self, JsError> {
        covalence_logic_lrat::load_cnf(&parse_dimacs(bytes).map_err(error)?)
            .map(Self)
            .map_err(error)
    }

    /// Parses compact binary DIMACS using LRAT-style signed varints.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed binary DIMACS or values outside signed `i32`.
    #[wasm_bindgen(js_name = fromBinaryDimacs)]
    pub fn from_binary_dimacs(bytes: &[u8]) -> Result<Self, JsError> {
        covalence_logic_lrat::load_cnf(&parse_binary_dimacs(bytes).map_err(error)?)
            .map(Self)
            .map_err(error)
    }

    /// Returns the non-normal rows as JSON.
    ///
    /// # Errors
    ///
    /// Returns an error if JSON serialization fails.
    #[wasm_bindgen(js_name = rowsJson)]
    pub fn rows_json(&self) -> Result<String, JsError> {
        rows_json(
            self.0
                .rows()
                .map(|row| row.iter().map(|literal| literal.get()).collect()),
        )
    }

    /// Sorts and deduplicates this CNF on demand.
    pub fn normalize(&mut self) {
        self.0.normalize();
    }
}

/// A non-normal DNF matrix preserving row and literal order.
#[wasm_bindgen]
pub struct Dnf(pub(crate) NativeMatrix);

#[wasm_bindgen]
impl Dnf {
    /// Constructs a DNF from a JSON array of signed-i32 rows.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed JSON or literals.
    #[wasm_bindgen(constructor)]
    pub fn new(rows: &str) -> Result<Self, JsError> {
        Ok(Self(NativeMatrix::new(parse_rows(rows)?)))
    }

    /// Returns the non-normal rows as JSON.
    ///
    /// # Errors
    ///
    /// Returns an error if JSON serialization fails.
    #[wasm_bindgen(js_name = rowsJson)]
    pub fn rows_json(&self) -> Result<String, JsError> {
        rows_json(
            self.0
                .rows()
                .map(|row| row.iter().map(|literal| literal.get()).collect()),
        )
    }

    /// Sorts and deduplicates this DNF on demand.
    pub fn normalize(&mut self) {
        self.0.normalize();
    }
}

/// A checked certificate that a CNF is universally unsatisfiable.
#[wasm_bindgen]
pub struct Refutation(pub(crate) NativeRefutation);

#[wasm_bindgen]
impl Refutation {
    /// Replays strict text LRAT against `cnf`.
    ///
    /// # Errors
    ///
    /// Returns the first parse or checked-replay rejection.
    #[wasm_bindgen(js_name = fromTextLrat)]
    pub fn from_text_lrat(cnf: &Cnf, proof: &str) -> Result<Self, JsError> {
        replay(&formula(&cnf.0)?, &parse_text(proof).map_err(error)?)
            .map(Self)
            .map_err(error)
    }

    /// Replays binary LRAT against `cnf`.
    ///
    /// # Errors
    ///
    /// Returns the first parse or checked-replay rejection.
    #[wasm_bindgen(js_name = fromBinaryLrat)]
    pub fn from_binary_lrat(cnf: &Cnf, proof: &[u8]) -> Result<Self, JsError> {
        replay(&formula(&cnf.0)?, &parse_binary(proof).map_err(error)?)
            .map(Self)
            .map_err(error)
    }

    /// Returns the certified CNF rows as JSON.
    ///
    /// # Errors
    ///
    /// Returns an error if JSON serialization fails.
    #[wasm_bindgen(js_name = cnfJson)]
    pub fn cnf_json(&self) -> Result<String, JsError> {
        rows_json(
            self.0
                .theorem()
                .lhs
                .rows()
                .map(|row| row.iter().map(|literal| literal.get()).collect()),
        )
    }
}

/// An LCF store containing only universally valid classical sequents.
#[wasm_bindgen]
pub struct ClassicalKernel(Kernel);

impl Default for ClassicalKernel {
    fn default() -> Self {
        Self::new()
    }
}

#[wasm_bindgen]
impl ClassicalKernel {
    #[wasm_bindgen(constructor)]
    #[must_use]
    pub fn new() -> Self {
        Self(Kernel::new())
    }

    /// Copies a checked refutation into a fresh theorem slot.
    ///
    /// # Errors
    ///
    /// Returns an error if theorem storage is exhausted.
    #[wasm_bindgen(js_name = copyRefutation)]
    pub fn copy_refutation(&mut self, refutation: &Refutation) -> Result<i32, JsError> {
        self.0
            .copy_refutation(&refutation.0)
            .map(ThmId::get)
            .map_err(error)
    }

    /// Returns one theorem as `[cnf, dnf]` JSON.
    ///
    /// # Errors
    ///
    /// Returns an error for an invalid/absent theorem or serialization failure.
    #[wasm_bindgen(js_name = theoremJson)]
    pub fn theorem_json(&self, theorem: i32) -> Result<String, JsError> {
        let id = ThmId::new(theorem)
            .ok_or_else(|| JsError::new("theorem IDs are positive i32 values"))?;
        let theorem = self
            .0
            .get(id)
            .or_else(|| self.0.refutation(id))
            .ok_or_else(|| JsError::new("theorem is absent"))?;
        let lhs = theorem
            .lhs
            .rows()
            .map(|row| row.iter().map(|literal| literal.get()).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        let rhs = theorem
            .rhs
            .rows()
            .map(|row| row.iter().map(|literal| literal.get()).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        covalence_lib_json::to_string(&(lhs, rhs)).map_err(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dimacs_text_and_binary_replay_reach_a_classical_kernel() {
        let cnf = Cnf::from_dimacs(b"p cnf 1 2\n1 0\n-1 0\n").unwrap();
        assert_eq!(
            Cnf::from_binary_dimacs(&[2, 0, 3, 0])
                .unwrap()
                .rows_json()
                .unwrap(),
            "[[1],[-1]]"
        );
        assert_eq!(cnf.rows_json().unwrap(), "[[1],[-1]]");
        let text = Refutation::from_text_lrat(&cnf, "3 0 1 2 0\n").unwrap();
        let binary = Refutation::from_binary_lrat(&cnf, &[b'a', 6, 0, 2, 4, 0]).unwrap();
        assert_eq!(text.cnf_json().unwrap(), binary.cnf_json().unwrap());
        let mut kernel = ClassicalKernel::new();
        let theorem = kernel.copy_refutation(&text).unwrap();
        assert_eq!(kernel.theorem_json(theorem).unwrap(), "[[[1],[-1]],[]]");
    }

    #[test]
    fn matrix_objects_preserve_then_normalize_explicitly() {
        let mut cnf = Cnf::new("[[2,1,2],[2,1,2]]").unwrap();
        let mut dnf = Dnf::new("[[-1,-2,-1]]").unwrap();
        assert_eq!(cnf.rows_json().unwrap(), "[[2,1,2],[2,1,2]]");
        cnf.normalize();
        dnf.normalize();
        assert_eq!(cnf.rows_json().unwrap(), "[[1,2]]");
        assert_eq!(dnf.rows_json().unwrap(), "[[-2,-1]]");
    }
}
