//! Load a CBOR file and concretely execute it, checking each step against the CBOR trace.
use std::collections::HashMap;
use std::convert::TryFrom;
use std::env;
use env_logger;
use log::trace;
use sym_proof::Addr;
use sym_proof::micro_ram::NUM_REGS;
use sym_proof::micro_ram::import;
use sym_proof::proof::{Proof, Prop};
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
    // Run concretely: 8 steps to the start of the loop, then 11 more steps to run the first
    // iteration up to the condition check.  The loop is structured as a do/while, so the condition
    // check comes at the end.
    for _ in 0 .. 8 + 11 {
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

    let mut pf = Proof::new(prog);

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
    let state = State::new(
        v,
        conc_state.pc,
        regs.clone(),
        mem,
        Vec::new(),
    );

    let l_step = pf.rule_step_zero(state);
    pf.rule_step_extend(l_step, |mut spf| {
        spf.tactic_step_concrete()?;
        spf.admit(Pred::Eq(
            Term::cmpe(regs[12].clone(), 0.into()),
            0.into(),
        ));
        spf.tactic_step_jmp_taken()?;
        spf.tactic_run_concrete()?;
        Ok(())
    })?;

    let (loop_start, loop_end) = match *pf.lemma(l_step) {
        Prop::Step(ref a, ref b) => (a, b),
    };

    for i in 0 .. NUM_REGS {
        eprintln!("{:2}: {} -> {}", i, loop_start.regs()[i], loop_end.regs()[i]);
    }

    Ok(())
}

fn main() {
    env_logger::init();
    let args = env::args().collect::<Vec<_>>();
    assert_eq!(args.len(), 2, "must provide cbor path");
    import::with_globals(|| run(&args[1]).unwrap());
}

