#!/bin/bash
set -xeuo pipefail

name=$1

src_dir="$(cd "$(dirname "$0")" && pwd)"
build_dir="$src_dir/build"

(
    mkdir -p "$build_dir/cargo"
    python3 gen_microram_cargo_toml.py \
        "$src_dir/Cargo.toml" \
        "$build_dir/cargo/Cargo.toml"

    cd "$build_dir/cargo"
    cargo +1.56.0 update

    features=microram,${cc_extra_features:-} \
        "$src_dir/../rust-support/build_microram.sh" secrets secrets

    features=microram,${cc_extra_features:-} \
        keep_symbols=__spontaneous_jump_dest \
        "$src_dir/../rust-support/build_microram.sh" interp_${name}_microram

    cp build/interp_${name}_microram.{bc,ll,s} "$build_dir"
)
