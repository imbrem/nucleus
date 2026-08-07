{
  description = "Nucleus development environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    crane.url = "github:ipetkov/crane";
  };

  outputs = { self, nixpkgs, flake-utils, rust-overlay, crane }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs { inherit system overlays; };
        rust = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;
        wasiCC = pkgs.pkgsCross.wasi32.stdenv.cc;
        wasiTools = pkgs.runCommand "nucleus-wasi-tools" {} ''
          mkdir -p $out/bin
          ln -s ${pkgs.llvmPackages.clang-unwrapped}/bin/clang $out/bin/nucleus-wasm-clang
          ln -s ${wasiCC}/bin/wasm32-unknown-wasi-cc $out/bin/
          ln -s ${wasiCC}/bin/wasm32-unknown-wasi-ar $out/bin/
        '';
        rustPlatform = pkgs.makeRustPlatform {
          cargo = rust;
          rustc = rust;
        };
        craneLib = (crane.mkLib pkgs).overrideToolchain rust;
        gluArgs = {
          pname = "glu";
          version = "0.0.0";
          src = ./tools/glu;
          strictDeps = true;
        };
        gluCargoArtifacts = craneLib.buildDepsOnly gluArgs;
        glu = craneLib.buildPackage (gluArgs // {
          cargoArtifacts = gluCargoArtifacts;
        });
        native-check = rustPlatform.buildRustPackage {
          pname = "nucleus-native-check";
          version = "0.0.0";
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;
          cargoBuildFlags = [ "--workspace" "--all-targets" ];
          cargoTestFlags = [ "--workspace" ];
          installPhase = "mkdir -p $out";
        };
        tools = with pkgs; [
          buck2
          cargo-component
          caddy
          clang
          chromium
          devcontainer
          git
          glu
          nodejs_24
          pnpm
          python3
          rust
          scc
          wasm-bindgen-cli
          wasm-tools
          wasmtime
          wasiTools
          xdg-utils
        ];
      in {
        packages = {
          inherit glu;
          default = glu;
        };

        apps.default = {
          type = "app";
          program = "${glu}/bin/glu";
          meta.description = "Run Nucleus repository tasks";
        };
        checks = {
          inherit glu native-check;
        };

        devShells.default = pkgs.mkShell {
          packages = tools;
          shellHook = ''
            export CHROMIUM_PATH="${pkgs.chromium}/bin/chromium"
            export CC_wasm32_unknown_unknown=nucleus-wasm-clang
            export CC_wasm32_wasip1=wasm32-unknown-wasi-cc
            export CC_wasm32_wasip2=wasm32-unknown-wasi-cc
            mkdir -p .direnv/bin
            # `glu buck configure` only writes .buckconfig.local, and resolves
            # to the Nix glu because .direnv/bin is not on PATH yet. Nothing
            # here starts Buck, so nothing survives to hold direnv's
            # environment pipe open; the shim builds glu at first use instead.
            glu buck configure >/dev/null 2>&1
            ln -sfn "$PWD/tools/glu/glu-shim" .direnv/bin/glu
            export PATH="$PWD/.direnv/bin:$PATH"
          '';
        };
      });
}
