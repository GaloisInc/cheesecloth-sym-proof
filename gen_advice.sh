#!/bin/bash
set -euo pipefail

name=$1
case $# in
    1)
        trace="traces/$name.cbor"
        ;;
    2)
        trace=$2
        ;;
    *)
        echo "usage: $0 <name> [trace.cbor]"
        exit 1
esac

edo() {
    echo " >>> $*"
    local ret=0
    "$@" || ret=$?
    if [[ "$ret" -ne 0 ]]; then
        echo "command failed with code $ret:"
        echo "$*"
    fi
    return $ret
}

cargo_flags=--release

rm -f advice/*.cbor
edo cargo run --bin proof_"$name" --features stage0,verbose -- "$trace"
edo cargo run --bin interp_"$name" --features stage1,verbose -- "$trace"
edo cargo run --bin interp_"$name" --features stage2,verbose -- "$trace"
edo cargo run --bin interp_"$name" --features stage3,verbose -- "$trace"
edo cargo run --bin interp_"$name" --features stage4,verbose -- "$trace"
