# Cross-language artifact graph. Cargo owns package topology; globs own asset trees.
# `glu artifact ...` commands implement these actions and are internal to Buck.

load("//buck:defs.bzl", "named_sources", "with_environment")

_DOCS_BASE_PATH = read_config("docs", "base_path", "")
_DOCS_COMMIT = read_config("docs", "commit", "unknown")
_DOCS_DIRTY = read_config("docs", "dirty", "true")

_DOCS_SOURCES = glob(
    ["apps/docs/**"],
    exclude = [
        "apps/docs/.svelte-kit/**",
        "apps/docs/build/**",
    ],
)

# The `notes/` corpus is compiled into the site by `apps/docs`, so it is a
# documentation input rather than a source tree of its own.
_NOTES_SOURCES = glob(["notes/**/*.md"])

_NUCLEUS_PACKAGE_SOURCES = glob(
    ["packages/nucleus/**"],
    exclude = [
        "packages/nucleus/component/**",
        "packages/nucleus/dist/**",
        "packages/nucleus/generated/**",
    ],
)

_REPOSITORY_SOURCES = glob([
    ".devcontainer/**",
    "buck/**",
    "*.json",
    "*.nix",
    "*.toml",
    "*.yaml",
    "*.yml",
])

genrule(
    name = "loc",
    srcs = with_environment(
        _DOCS_SOURCES +
        _NUCLEUS_PACKAGE_SOURCES +
        _REPOSITORY_SOURCES +
        [
            ":rustdoc",
            ":wasm",
            "//tools/glu:glu",
        ],
    ),
    out = "loc.json",
    cmd = "$(exe //tools/glu:glu) artifact loc --out $OUT",
    labels = ["uses_undeclared_inputs"],
)

genrule(
    name = "rustdoc",
    srcs = with_environment({
        "Cargo.lock": "Cargo.lock",
        "Cargo.toml": "Cargo.toml",
        "bin-nucleus": "//crates/bin/nucleus:package_files",
        "data-basic": "//crates/data/basic:package_files",
        "lib-hash": "//crates/lib/hash:package_files",
        "lib-rand": "//crates/lib/rand:package_files",
        "lib-sqlite": "//crates/lib/sqlite:package_files",
        "neutron": "//crates/neutron:package_files",
        "nucleus": "//crates/nucleus:package_files",
        "proton": "//crates/proton:package_files",
    }),
    out = "rustdoc",
    cmd = "mkdir -p $OUT && $(exe //tools/glu:glu) artifact rustdoc --out $OUT",
    labels = ["uses_undeclared_inputs"],
)

genrule(
    name = "wasm",
    srcs = named_sources(
        {
            "lib-sqlite": "//crates/lib/sqlite:package_files",
            "nucleus": "//crates/nucleus:package_files",
        },
        _NUCLEUS_PACKAGE_SOURCES +
        [
            "Cargo.lock",
            "Cargo.toml",
            "package.json",
            "pnpm-lock.yaml",
            "pnpm-workspace.yaml",
        ],
    ),
    out = "wasm",
    cmd = "mkdir -p $OUT && $(exe //tools/glu:glu) artifact wasm --out $OUT",
    labels = ["uses_undeclared_inputs"],
)

genrule(
    name = "component",
    srcs = with_environment({
        "Cargo.lock": "Cargo.lock",
        "Cargo.toml": "Cargo.toml",
        "lib-sqlite": "//crates/lib/sqlite:package_files",
        "nucleus": "//crates/nucleus:package_files",
    }),
    out = "nucleus-component.wasm",
    cmd = "$(exe //tools/glu:glu) artifact component --out $OUT",
    labels = ["uses_undeclared_inputs"],
)

# JavaScript for the same component `:component` produces, so the browser and
# Node can call it without going through wasm-bindgen. jco comes from the pnpm
# workspace, so the manifests that pin it are inputs.
genrule(
    name = "component-js",
    srcs = named_sources(
        {"component": ":component"},
        [
            "package.json",
            "packages/nucleus/package.json",
            "pnpm-lock.yaml",
            "pnpm-workspace.yaml",
        ],
    ),
    out = "component-js",
    cmd = "mkdir -p $OUT && $(exe //tools/glu:glu) artifact component-js --component $(location :component) --out $OUT",
    labels = ["uses_undeclared_inputs"],
)

genrule(
    name = "cli-component",
    srcs = with_environment({
        "Cargo.lock": "Cargo.lock",
        "Cargo.toml": "Cargo.toml",
        "bin-nucleus": "//crates/bin/nucleus:package_files",
        "lib-sqlite": "//crates/lib/sqlite:package_files",
        "nucleus": "//crates/nucleus:package_files",
    }),
    out = "nucleus-cli-component.wasm",
    cmd = "$(exe //tools/glu:glu) artifact cli-component --out $OUT",
    labels = ["uses_undeclared_inputs"],
)

genrule(
    name = "docs",
    srcs = named_sources(
        {
            "production-crates": "//buck/cargo/production:crates-json",
            "production-dependencies": "//buck/cargo/production:dependencies-json",
        },
        _DOCS_SOURCES +
        _NOTES_SOURCES +
        [
            ":loc",
            ":rustdoc",
            "package.json",
            "pnpm-lock.yaml",
            "pnpm-workspace.yaml",
        ],
    ),
    out = "docs",
    cmd = "mkdir -p $OUT && BASE_PATH='{}' BUILD_COMMIT='{}' BUILD_DIRTY='{}' $(exe //tools/glu:glu) artifact docs --production-crates $(location //buck/cargo/production:crates-json) --production-dependencies $(location //buck/cargo/production:dependencies-json) --loc $(location :loc) --rustdoc $(location :rustdoc) --out $OUT".format(
        _DOCS_BASE_PATH,
        _DOCS_COMMIT,
        _DOCS_DIRTY,
    ),
    labels = ["uses_undeclared_inputs"],
)
