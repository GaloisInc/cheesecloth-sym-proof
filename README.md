# Build process

```
# Generate advice files for all stages of the proof
./gen_advice.sh grit

# Generate rust source files for the program and secrets
mkdir -p gen
python3 prog_to_rust.py traces/grit.cbor >gen/grit_program.rs
python3 term_table_to_rust.py advice/term_table.cbor >gen/grit_term_table.rs

# Build RISC-V assembly file for use with MicroRAM
./build_microram.sh

# Output is written to build/interp_grit_microram.s
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

