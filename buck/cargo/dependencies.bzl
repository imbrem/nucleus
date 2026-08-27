load("@prelude//rust:cargo_buildscript.bzl", "buildscript_run")
load("@prelude//rust:cargo_package.bzl", "cargo")

def _package_env(package):
    version = package["version"]
    version_without_build = version.split("+")[0]
    version_parts = version_without_build.split("-", 1)
    numbers = version_parts[0].split(".")
    env = {
        "CARGO_PKG_AUTHORS": "",
        "CARGO_PKG_DESCRIPTION": "",
        "CARGO_PKG_HOMEPAGE": "",
        "CARGO_PKG_LICENSE": "",
        "CARGO_PKG_LICENSE_FILE": "",
        "CARGO_PKG_NAME": package["name"],
        "CARGO_PKG_README": "",
        "CARGO_PKG_REPOSITORY": "",
        "CARGO_PKG_RUST_VERSION": "",
        "CARGO_PKG_VERSION": version,
        "CARGO_PKG_VERSION_MAJOR": numbers[0],
        "CARGO_PKG_VERSION_MINOR": numbers[1],
        "CARGO_PKG_VERSION_PATCH": numbers[2],
        "CARGO_PKG_VERSION_PRE": version_parts[1] if len(version_parts) == 2 else "",
    }
    env.update(package.get("env", {}))
    return env

def _target(package, target, label, archive):
    env = _package_env(package)
    # Cargo defines this for ordinary targets as well as build scripts. Proc
    # macros such as wasm-bindgen read it while expanding library code.
    env["CARGO_MANIFEST_DIR"] = "$(location :{})".format(archive)
    if package.get("buildscript") != None:
        env["OUT_DIR"] = "$(location :{}-build-script-run[out_dir])".format(label)
    attributes = {
        "name": label,
        "srcs": [":{}".format(archive)],
        "crate": target.get("crate_name", package["name"].replace("-", "_")),
        "crate_root": "{}/{}".format(archive, target.get("crate_root", "src/lib.rs")),
        "edition": package["edition"],
        "env": env,
        "visibility": ["PUBLIC"],
    }
    if package.get("features"):
        attributes["features"] = package["features"]
    if target.get("proc_macro", False):
        attributes["proc_macro"] = True
    if package.get("buildscript") != None:
        attributes["rustc_flags"] = [
            "@$(location :{}-build-script-run[rustc_flags])".format(label),
        ]
    if target.get("named_deps"):
        attributes["named_deps"] = target["named_deps"]
    cargo.rust_library(**attributes)

def _buildscript(package, script, label, archive):
    env = _package_env(package)
    env.update({
        "CARGO_MANIFEST_DIR": "$(location :{})".format(archive),
        "DEBUG": "true",
        "OPT_LEVEL": "0",
        "PROFILE": "debug",
    })
    attributes = {
        "name": "{}-build-script-build".format(label),
        "srcs": [":{}".format(archive)],
        "crate": "build_script_build",
        "crate_root": "{}/{}".format(archive, script.get("crate_root", "build.rs")),
        "edition": package["edition"],
        "env": env,
        "visibility": [],
    }
    if package.get("features"):
        attributes["features"] = package["features"]
    if script.get("named_deps"):
        attributes["named_deps"] = script["named_deps"]
    cargo.rust_binary(**attributes)

    run_attributes = {
        "name": "{}-build-script-run".format(label),
        "package_name": package["name"],
        "buildscript_rule": ":{}-build-script-build".format(label),
        "rustc_link_lib": True,
        "rustc_link_search": True,
        "version": package["version"],
    }
    run_env = dict(env)
    run_env.update(script.get("run_env", {}))
    run_attributes["env"] = run_env
    if package.get("features"):
        run_attributes["features"] = package["features"]
    buildscript_run(**run_attributes)

def declare_cargo_dependencies(dependencies):
    for package in dependencies["packages"]:
        label = "{}-{}".format(package["name"], package["version"])
        archive = "{}.crate".format(label)
        native.http_archive(
            name = archive,
            sha256 = package["checksum"],
            strip_prefix = label,
            # Match Cargo's crates.io registry configuration. The API download
            # route redirects to this CDN but rate-limits Buck's parallel
            # requests before they reach it.
            urls = ["https://static.crates.io/crates/{}/{}.crate".format(package["name"], label)],
            # A `links` crate publishes paths into its own source tree, such as
            # the header of a C library it bundles, and a dependent's build
            # script is handed them as `DEP_<LINKS>_<KEY>`. Those paths are
            # `$(location)` on this archive, so it cannot stay package-private.
            visibility = ["PUBLIC"],
        )
        for target in package["targets"]:
            _target(package, target, label, archive)
        if package.get("buildscript") != None:
            _buildscript(package, package["buildscript"], label, archive)
