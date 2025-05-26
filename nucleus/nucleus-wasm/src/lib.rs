use nucleus_kernel::Kernel;
use wasm_bindgen::prelude::*;

#[derive(Clone)]
#[wasm_bindgen]
pub struct Nucleus {
    kernel: Kernel,
}

#[wasm_bindgen]
impl Nucleus {
    /// Construct a new kernel instance
    #[wasm_bindgen(constructor)]
    pub fn new() -> Nucleus {
        Nucleus {
            kernel: Kernel::default(),
        }
    }

    /// Construct a new context
    pub fn new_ctx(&mut self, parent: Option<u32>) -> u32 {
        let parent = parent.map(|p| self.kernel.ctx_id(p).expect("invalid parent id"));
        self.kernel
            .new_ctx(parent)
            .expect("failed to create new context")
            .ix()
    }
}
