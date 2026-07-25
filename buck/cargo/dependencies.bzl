load("@prelude//rust:cargo_buildscript.bzl", "buildscript_run")
load("@prelude//rust:cargo_package.bzl", "cargo")

def _pairs(values):
    return {pair[0]: pair[1] for pair in values}

def _target(package, target):
    env = _pairs(package["env"])
    if target["buildscript"] != None:
        env["OUT_DIR"] = "$(location :{}[out_dir])".format(target["buildscript"])
    attributes = {
        "name": target["name"],
        "srcs": [package["archive_label"]],
        "crate": target["crate_name"],
        "crate_root": target["crate_root"],
        "edition": target["edition"],
        "env": env,
        "visibility": ["PUBLIC"],
    }
    if target["features"]:
        attributes["features"] = target["features"]
    if target["proc_macro"]:
        attributes["proc_macro"] = True
    if target["buildscript"] != None:
        attributes["rustc_flags"] = [
            "@$(location :{}[rustc_flags])".format(target["buildscript"]),
        ]
    if target["named_deps"]:
        attributes["named_deps"] = _pairs(target["named_deps"])
    cargo.rust_library(**attributes)

def _buildscript(package, script):
    env = _pairs(package["env"])
    env.update({
        "CARGO_MANIFEST_DIR": "$(location {})".format(package["archive_label"]),
        "DEBUG": "true",
        "OPT_LEVEL": "0",
        "PROFILE": "debug",
    })
    attributes = {
        "name": script["name"],
        "srcs": [package["archive_label"]],
        "crate": "build_script_build",
        "crate_root": script["crate_root"],
        "edition": script["edition"],
        "env": env,
        "visibility": [],
    }
    if script["features"]:
        attributes["features"] = script["features"]
    if script["named_deps"]:
        attributes["named_deps"] = _pairs(script["named_deps"])
    cargo.rust_binary(**attributes)

    run_attributes = {
        "name": script["run_name"],
        "package_name": package["name"],
        "buildscript_rule": ":{}".format(script["name"]),
        "rustc_link_lib": True,
        "rustc_link_search": True,
        "version": package["version"],
    }
    run_attributes["env"] = env
    if script["features"]:
        run_attributes["features"] = script["features"]
    buildscript_run(**run_attributes)

def declare_cargo_dependencies(dependencies):
    for package in dependencies["packages"]:
        native.http_archive(
            name = package["archive"],
            sha256 = package["checksum"],
            strip_prefix = package["archive_prefix"],
            urls = [package["url"]],
            visibility = [],
        )
        for target in package["targets"]:
            _target(package, target)
        if package["buildscript"] != None:
            _buildscript(package, package["buildscript"])
