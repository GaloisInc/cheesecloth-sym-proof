//! Load a CBOR file and concretely execute it, checking each step against the CBOR trace.
use std::env;
use env_logger;
use log::trace;
use witness_checker::micro_ram::types::Advice;
use sym_proof::{Addr, Word, WORD_BYTES};
use sym_proof::micro_ram::State;
use sym_proof::micro_ram::import;

fn run(path: &str) {
    let exec = import::load_exec(path);

    let prog = import::convert_code(&exec);
    eprintln!("loaded code: {} instrs", prog.len());
    let init_state = import::convert_init_state(&exec);
    eprintln!("loaded memory: {} words", init_state.mem.len());
    trace!("initial regs = {:?}", init_state.regs);

    let mut state = init_state;
    let mut cycle = 0;
    let mut mem_op_count = 0;
    eprintln!("trace: {} chunks", exec.trace.len());
    for (i, chunk) in exec.trace.iter().enumerate() {
        trace!("cycle {}: trace chunk {}: {} states, segment {}", cycle, i, chunk.states.len(), chunk.segment);
        for ram_state in &chunk.states {
            let expect_state = import::convert_ram_state(ram_state);
            let advs = exec.advice.get(&(cycle as u64 + 1)).map_or(&[] as &[_], |x| x);
            trace!("cycle {}: advs = {:?}", cycle, advs);

            let stutter = advs.iter().any(|adv| matches!(*adv, Advice::Stutter));
            if stutter {
                trace!("STUTTER on cycle {}", cycle);
                cycle += 1;
                continue;
            }

            let advice = advs.iter().filter_map(|adv| match *adv {
                Advice::Advise { advise } => Some(advise),
                _ => None,
            }).next();

            let pc = state.pc;
            let instr = prog.get(&pc).cloned().unwrap_or_else(|| {
                panic!("program executed out of bounds at {}", pc);
            });
            trace!("exec {:?}, pc = {}, regs = {:?}", instr, state.pc, state.regs);
            state.step(instr, advice);

            assert_eq!(state.pc, expect_state.pc, "after cycle {}", cycle);
            assert_eq!(state.regs, expect_state.regs, "after cycle {}", cycle);

            for adv in advs {
                if let Advice::MemOp { addr, value, .. } = *adv {
                    let offset_mask = WORD_BYTES as Addr - 1;
                    let word_addr = addr as Addr & !offset_mask;
                    assert_eq!(state.mem[&word_addr], value as Word,
                        "at address {}, after cycle {}", addr, cycle);
                    mem_op_count += 1;
                }
            }

            cycle += 1;
        }
    }

    eprintln!("valid trace: {} cycles, {} memory ops", cycle, mem_op_count);
}

fn main() {
    env_logger::init();
    let args = env::args().collect::<Vec<_>>();
    assert_eq!(args.len(), 2, "must provide cbor path");
    import::with_globals(|| run(&args[1]));
}

