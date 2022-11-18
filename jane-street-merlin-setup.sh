#!/bin/bash

cd "$(dirname "$0")"

ocamlmerlin="$(which ocamlmerlin 2>&-)"
ocamlmerlin_status=$?
if [[ $ocamlmerlin_status -ne 0 ]]; then
  echo >&2 'No ocamlmerlin on $PATH'
  exit $ocamlmerlin_status
fi

set -e

merlin_dir="$(dirname "$ocamlmerlin")"

# The stub files `jenga.conf` and `.ocaml-lib` should be deleted if
# `.local-merlin-binaries` exists or if the `.merlin-binaries` search ever stops
# looking for a tree file first.

# When `.local-merlin-binaries` is fully supported we can just point it at
# `$MERLIN_DIR` and drop this extra directory *and* the stub files entirely.
# This will require updating the `.gitignore`, too.
mkdir -p .for-jane-street-merlin
ln -sfn "$merlin_dir" .for-jane-street-merlin/dev
ln -sfn "$merlin_dir" .for-jane-street-merlin/prod

echo "$PWD/.for-jane-street-merlin" > .merlin-binaries
ocamlc -config | grep standard_library: | cut -d' ' -f2 > .ocaml-lib
