#![no_main]

use covalence_logic_sat::{Limits, parse_bounded};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|bytes: &[u8]| {
    let mut limits = Limits::default();
    limits.proof_bytes = 4096;
    limits.instructions = 128;
    limits.live_clauses = 128;
    limits.terms_per_instruction = 256;
    limits.total_terms = 4096;
    limits.work_units = 16_384;
    let _ = parse_bounded(bytes, limits);
});
