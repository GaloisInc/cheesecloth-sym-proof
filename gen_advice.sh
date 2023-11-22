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

rm -f advice/*.cbor
cargo run --bin proof_"$name" --features stage0,verbose -- "$trace"
cargo run --bin interp_"$name" --features stage1,verbose -- "$trace"
cargo run --bin interp_"$name" --features stage2,verbose -- "$trace"
cargo run --bin interp_"$name" --features stage3,verbose -- "$trace"
cargo run --bin interp_"$name" --features stage4,verbose -- "$trace"
