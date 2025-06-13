use nucleus_frontend::sexpr::{Sexpr, ws};
use pretty::RcDoc;
use wasm_bindgen::prelude::*;
use winnow::{
    LocatingSlice, Parser,
    combinator::{delimited, opt},
};

#[derive(Clone)]
#[wasm_bindgen]
pub struct Nucleus {}

#[wasm_bindgen]
impl Nucleus {
    /// Construct a new kernel instance
    #[wasm_bindgen(constructor)]
    pub fn new() -> Nucleus {
        Nucleus {}
    }

    pub fn handle_input(&mut self, input: String) -> String {
        let sexprs =
            match delimited(opt(ws), Sexpr::lsexprs, opt(ws)).parse(LocatingSlice::new(&input)) {
                Ok(sexprs) => sexprs,
                Err(err) => return format!("parse error: {err}"),
            };
        let doc = RcDoc::intersperse(sexprs.iter().map(|e| e.to_doc()), RcDoc::line());
        format!("{}", doc.pretty(80))
    }
}
