#!/bin/bash
set -xeuo pipefail

src_dir="$(cd "$(dirname "$0")" && pwd)"
build_dir="$src_dir/build"

mkdir -p "$build_dir/cargo"
python3 gen_microram_cargo_toml.py <"$src_dir/Cargo.toml" >"$build_dir/cargo/Cargo.toml"

cd "$build_dir/cargo"
cargo +1.56.0 update

cc_secret_objects= \
    features=microram \
    profile=microram \
    "$src_dir/../rust-support/build_microram.sh" interp_grit_microram

cp build/interp_grit_microram.{bc,ll,s} "$build_dir"
