#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

cargo build --locked -p covalence-hol-proof-core-guest-beta --target wasm32-unknown-unknown
guest_path=$(realpath "${CARGO_TARGET_DIR:-target}/wasm32-unknown-unknown/debug/covalence_hol_proof_core_guest_beta.wasm")
wasm-tools validate "$guest_path"
COVALENCE_CORE_WASM_BETA_GUEST="$guest_path" \
    cargo test -p covalence-repl configured_real_core_wasm_beta_guest_exactly_decodes_and_replays --lib
