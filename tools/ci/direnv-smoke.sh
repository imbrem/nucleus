#!/usr/bin/env bash

# Fail if entering the development environment through direnv does not finish.
#
# direnv reserves file descriptor 3 for its environment dump and reads that
# pipe until EOF, so anything started from .envrc that outlives the build and
# inherits fd 3 blocks direnv forever, after the build has already succeeded.
# Buck's daemon and forkserver are exactly that; see the guard in flake.nix.
#
# This cannot live in `glu ci`, because glu is only on PATH once the thing
# being checked here has already worked.

set -euo pipefail

timeout_seconds=${DIRENV_SMOKE_TIMEOUT:-600}

cd "$(dirname "$0")/../.."

# The hang only reproduces when direnv is the process that starts the Buck
# daemon. Dropping the recorded environment makes the shellHook kill any
# running daemon first, which forces that cold start even on a warm checkout.
rm -f .direnv/buck-environment .direnv/bin/glu

direnv allow .

status=0
environment=$(timeout "$timeout_seconds" direnv export bash) || status=$?

if [ "$status" -eq 124 ]; then
  echo "error: direnv did not finish within ${timeout_seconds}s." >&2
  echo "Something started from .envrc is holding direnv's fd 3 open." >&2
  exit 1
fi

if [ "$status" -ne 0 ]; then
  echo "error: direnv export failed with status $status." >&2
  exit "$status"
fi

if [ -z "$environment" ]; then
  echo "error: direnv exported an empty environment." >&2
  exit 1
fi

echo "direnv loaded the environment within ${timeout_seconds}s."
