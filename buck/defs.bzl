def with_environment(inputs):
    environment = [
        "flake.lock",
        "flake.nix",
        "rust-toolchain.toml",
    ]
    if type(inputs) == type({}):
        inputs = dict(inputs)
        inputs.update({path: path for path in environment})
        return inputs
    return inputs + environment

def named_sources(named, files = []):
    sources = dict(named)
    sources.update({path: path for path in files})
    return with_environment(sources)
