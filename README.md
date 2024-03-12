# Build process

```
# Generate advice files for all stages of the proof
./gen_advice.sh sqrt

# Generate rust source files for the program and secrets
mkdir -p gen
python3 prog_to_rust.py traces/sqrt.cbor >gen/sqrt_program.rs
python3 term_table_to_rust.py advice/term_table.cbor >gen/term_table.rs

# Test interpreter with final advice
cargo run --bin interp_sqrt_microram --features microram_api,verbose,inline-secrets
# Test again, emulating spontaneous-jump snapshot behavior
python3 hardcoded_snapshot_to_rust.py advice/hardcoded_snapshot.cbor >gen/sqrt_hardcoded_snapshot.rs
cargo run --bin interp_sqrt_microram --features microram_api,verbose,inline-secrets,microram_hardcoded_snapshot

# Build RISC-V assembly file for use with MicroRAM
./build_microram.sh sqrt

# Output is written to build/interp_sqrt_microram.s
```


## Checking for undefined symbols

During development, it's sometimes useful to check that all the necessary
library functions were included in the MicroRAM build.

```
# Compile `interp_grit_microram.s` to an object file
clang-13 --target=riscv64-unknown-elf -march=rv64im -c build/interp_grit_microram.s
# List all undefined symbols in the object file
riscv64-unknown-elf-nm interp_grit_microram.o | grep ' [uU] ' | c++filt
```

Every undefined symbol listed in this output must be available as an intrinsic
in the MicroRAM compiler.  Things named `__cc_foo` are usually intrinsics.  But
if there are (for example) Rust standard library functions in the list, then
there is probably an issue with the build script.

