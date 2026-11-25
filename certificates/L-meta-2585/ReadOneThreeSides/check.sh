#!/bin/sh
set -eu
src_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd -- "${1:?Pass the path to the Lean project directory}"
proof_build=$(mktemp -d)
trap 'rm -rf -- "$proof_build"' EXIT
project_path=$(lake env printenv LEAN_PATH)
lean_bin=$(lake env which lean)
export LEAN_PATH="$proof_build:$project_path"
while IFS= read -r mod; do
    "$lean_bin" -j 2 -R "$src_dir" -o "$proof_build/$mod.olean" "$src_dir/$mod.lean"
done < "$src_dir/modules.txt"
