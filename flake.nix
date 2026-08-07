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
            # direnv collects the environment through file descriptor 3 and
            # blocks until every writer closes it. Buck's daemon and forkserver
            # outlive the build and inherit fd 3, so a fresh `direnv allow`
            # hangs after the build finishes unless everything that can start
            # them runs with fd 3 closed. Keep new Buck calls inside this group.
            {
              glu buck configure >/dev/null 2>&1
              buck_environment="$(command -v rustc):$(rustc --print sysroot):$(command -v clang):$(command -v cargo-component):$(command -v nucleus-wasm-clang):$(command -v wasm32-unknown-wasi-cc)"
              if [ ! -f .direnv/buck-environment ] ||
                 [ "$(cat .direnv/buck-environment)" != "$buck_environment" ]; then
                buck2 kill >/dev/null 2>&1 || true
                printf '%s\n' "$buck_environment" > .direnv/buck-environment
              fi
              if glu_output="$(buck2 build //tools/glu:glu --show-full-simple-output)"; then
                ln -sf "$glu_output" .direnv/bin/glu
              else
                echo "error: Buck could not build glu" >&2
                exit 1
              fi
            } 3>&-
            export PATH="$PWD/.direnv/bin:$PATH"
          '';
        };
      });
}
