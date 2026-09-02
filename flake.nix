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
        wasiTools = pkgs.runCommand "nucleus-wasi-tools" {
          nativeBuildInputs = [ pkgs.makeWrapper ];
        } ''
          mkdir -p $out/bin
          ln -s ${pkgs.llvmPackages.clang-unwrapped}/bin/clang $out/bin/nucleus-wasm-clang
          makeWrapper ${wasiCC}/bin/wasm32-unknown-wasi-cc $out/bin/wasm32-unknown-wasi-cc \
            --add-flags "-fuse-ld=${pkgs.llvmPackages.lld}/bin/wasm-ld"
          ln -s ${wasiCC}/bin/wasm32-unknown-wasi-ar $out/bin/
        '';
        rustPlatform = pkgs.makeRustPlatform {
          cargo = rust;
          rustc = rust;
        };
        # The interpreter the Python bindings are built against and tested
        # under. One environment for both: PyO3 links whichever interpreter it
        # is compiled against, so building with one and testing under another
        # is how ABI mismatches get in.
        #
        # Third-party packages the Python suite needs belong here, where
        # flake.lock pins them — NumPy and SAT solvers are the ones coming.
        # Anything nixpkgs does not carry can go in a local virtual environment
        # created with `--system-site-packages`; `glu` runs whichever `python3`
        # is on PATH, so an activated one layers on top of this without any
        # further configuration.
        python = pkgs.python3.withPackages (packages: with packages; [
          pytest
        ]);
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
          nativeBuildInputs = [ pkgs.git pkgs.makeWrapper ];
          postFixup = ''
            wrapProgram $out/bin/glu --prefix PATH : ${pkgs.lib.makeBinPath [ pkgs.git ]}
          '';
        });
        native-check = rustPlatform.buildRustPackage {
          pname = "nucleus-native-check";
          version = "0.0.0";
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;
          cargoBuildFlags = [ "--workspace" "--all-targets" ];
          cargoTestFlags = [ "--workspace" ];
          # `pyo3-build-config` interrogates an interpreter to decide how to
          # link, and the test binaries then embed the one it found. Both
          # phases need it, so it is a build input as well as a native one.
          nativeBuildInputs = [ python pkgs.cvc5 ];
          buildInputs = [ python ];
          installPhase = "mkdir -p $out";
        };
        tools = with pkgs; [
          buck2
          cargo-component
          caddy
          cvc5
          clang
          chromium
          devcontainer
          # Lean toolchain manager. elan reads each development's
          # lean-toolchain file, so the pinned version is the one that runs.
          # Only `glu lean` needs it; nothing in `glu build` does.
          elan
          git
          glu
          nodejs_24
          pnpm
          python
          # Builds the wheel and the editable install. `glu` does not use it —
          # it stages the package itself, so CI needs no packaging tool — but
          # it is how a developer installs Covalence into their own environment.
          maturin
          # Formatter and linter for the Python sources, driven by `glu fmt`
          # and `glu lint`.
          ruff
          rust
          scc
          wasm-bindgen-cli
          wasm-tools
          wasmtime
          wasiTools
          wit-bindgen
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
            export FONTCONFIG_FILE="${pkgs.makeFontsConf { fontDirectories = [ pkgs.dejavu_fonts ]; }}"
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
              buck_environment="$(command -v rustc):$(rustc --print sysroot):$(command -v clang):$(command -v cargo-component):$(command -v nucleus-wasm-clang):$(command -v wasm32-unknown-wasi-cc):$(command -v wasm-tools):$(command -v wit-bindgen)"
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
