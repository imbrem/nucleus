#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
build_dir="$repo_root/target/wasm32-wasip1/c-proof-demo"
output="$repo_root/target/wasm32-wasip1/covalence_proof_c_demo.component.wasm"

if command -v wasm32-unknown-wasi-cc >/dev/null; then
  wasi_cc=wasm32-unknown-wasi-cc
elif command -v wasm32-unknown-wasip1-cc >/dev/null; then
  wasi_cc=wasm32-unknown-wasip1-cc
else
  echo "error: a WASI C compiler is required" >&2
  exit 1
fi

mkdir -p "$build_dir"
wit-bindgen c --world standard-proof --out-dir "$build_dir" \
  "$repo_root/wit/proof"

"$wasi_cc" \
  "$build_dir/standard_proof.c" \
  "$build_dir/standard_proof_component_type.o" \
  "$repo_root/crates/proof/c-demo/proof.c" \
  -I "$build_dir" \
  -mexec-model=reactor \
  -o "$build_dir/covalence_proof_c_demo.wasm"

wasm-tools component new \
  "$build_dir/covalence_proof_c_demo.wasm" \
  -o "$output"
wasm-tools validate --features cm-async "$output"
