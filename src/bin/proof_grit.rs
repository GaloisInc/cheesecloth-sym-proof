//! Load a CBOR file and concretely execute it, checking each step against the CBOR trace.
use std::collections::HashMap;
use std::convert::TryFrom;
use std::env;
use env_logger;
use log::trace;
use witness_checker::micro_ram::types::Advice;
use sym_proof::{Addr, Word, WORD_BYTES};
use sym_proof::micro_ram::NUM_REGS;
use sym_proof::micro_ram::import;
use sym_proof::symbolic::{State, MemState, MemConcrete, VarCounter, Term, Pred};

fn run(path: &str) -> Result<(), String> {
    let exec = import::load_exec(path);

    let prog = import::convert_code(&exec);
    eprintln!("loaded code: {} instrs", prog.len());
    let init_state = import::convert_init_state(&exec);
    eprintln!("loaded memory: {} words", init_state.mem.len());
    trace!("initial regs = {:?}", init_state.regs);


    // Run concrete prefix
    let mut conc_state = init_state;
    let memcpy_addr = exec.labels["memcpy#39"];
    while conc_state.pc != memcpy_addr {
        let instr = prog[&conc_state.pc];
        conc_state.step(instr, None);
    }
    // Run concretely to the start of the loop.
    for i in 0 .. 8 {
        let instr = prog[&conc_state.pc];
        eprintln!("run concrete [{}]: {:?}", conc_state.pc, instr);
        conc_state.step(instr, None);
    }

    eprintln!("concrete registers:");
    for (i, &x) in conc_state.regs.iter().enumerate() {
        eprintln!("{:2}: 0x{:x}", i, x);
    }

    eprintln!("loop start label = {:?}",
        exec.labels.iter().filter(|&(_, &v)| v == conc_state.pc).collect::<Vec<_>>());

    // Build initial symbolic state
    let mut v = VarCounter::new();
    let regs = (0 .. NUM_REGS).map(|_| v.var()).collect::<Box<[_]>>();
    let mut regs = *<Box<[_; NUM_REGS]>>::try_from(regs).unwrap();
    regs[0] = Term::const_(0);
    regs[11] = Term::const_(conc_state.regs[11]);
    regs[13] = Term::const_(conc_state.regs[13]);
    let mem = MemState::Concrete(MemConcrete {
        m: HashMap::new(),
        max: Addr::MAX,
    });
    let mut state = State::new(
        conc_state.pc,
        regs.clone(),
        mem,
        Vec::new(),
    );

    /*
    state.tactic_run_concrete(&prog)?;
    state.admit(Pred::Eq(Term::cmpae(regs[12].clone(), 32.into()), 1.into()));
    state.tactic_step_jmp_taken(prog[&state.pc()])?;
    */

    let loop_start = state.clone();

    state.tactic_run_concrete(&prog)?;
    state.admit(Pred::Eq(
        Term::cmpe(Term::add(regs[12].clone(), (-1_i64 as u64).into()), 0.into()),
        0.into(),
    ));
    state.tactic_step_jmp_taken(prog[&state.pc()])?;

    let loop_end = state.clone();

    for i in 0 .. NUM_REGS {
        eprintln!("{:2}: {} -> {}", i, loop_start.regs()[i], loop_end.regs()[i]);
    }

    let instr = prog[&state.pc()];
    eprintln!("next: {:?}", instr);
    state.tactic_step_concrete(instr)?;

    Ok(())
}

fn main() {
    env_logger::init();
    let args = env::args().collect::<Vec<_>>();
    assert_eq!(args.len(), 2, "must provide cbor path");
    import::with_globals(|| run(&args[1]).unwrap());
}

