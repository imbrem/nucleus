use wasm_bindgen::prelude::*;

#[derive(Clone)]
#[wasm_bindgen]
pub struct WebNucleus {
}

#[wasm_bindgen]
impl WebNucleus {
    #[wasm_bindgen(constructor)]
    pub fn new() -> WebNucleus {
        WebNucleus {}
    }

    pub fn handle_input(&mut self, input: &str) -> String {
        return input.to_uppercase();
    }
}