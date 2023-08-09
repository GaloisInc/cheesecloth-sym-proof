//! Load a CBOR file and concretely execute it, checking each step against the CBOR trace.
use std::array;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::env;
use env_logger;
use log::trace;
use sym_proof::Addr;
use sym_proof::micro_ram::NUM_REGS;
use sym_proof::micro_ram::import;
use sym_proof::proof::{Proof, Prop};
use sym_proof::symbolic::{
    State, MemState, MemConcrete, MemLog, VarCounter, Term, Pred, IdentitySubsts, SubstTable,
};

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
    //regs[11] = Term::const_(conc_state.regs[11]);
    //regs[13] = Term::const_(conc_state.regs[13]);
    /*
    let mem = MemState::Concrete(MemConcrete {
        m: HashMap::new(),
        max: Addr::MAX,
    });
    */
    let mem = MemState::Log(MemLog { l: Vec::new() });
    let state = State::new(
        conc_state.pc,
        v.var(),
        regs.clone(),
        mem,
    );
    let mut preds = vec![
        Pred::Nonzero(Term::cmpa(regs[12].clone(), Term::const_(0))),
    ];

    let l_loop = pf.rule_step_zero(v, preds, state);
    pf.rule_step_extend(l_loop, |mut spf| {
        // Step over the condition check `cmpe` + `cnjmp`
        spf.tactic_step_concrete()?;
        spf.rule_derive_pred(|ppf| {
            ppf.show();
            ppf.rule_gt_ne_unsigned(regs[12].clone(), 0.into())?;
            Ok(())
        })?;
        spf.tactic_step_jmp_taken()?;

        // Run the loop body.
        spf.tactic_run_concrete()?;
        // Load
        spf.rule_step_mem_load_fresh()?;
        spf.tactic_run_concrete()?;
        // Store
        spf.rule_step_mem_symbolic()?;
        spf.tactic_run_concrete_until(conc_state.pc)?;

        spf.rule_forget_reg(11);
        spf.rule_forget_reg(13);
        spf.rule_forget_reg(14);
        spf.rule_forget_reg(15);
        spf.rule_forget_reg(32);

        Ok(())
    })?;

    // Print effect
    let dump = |prop: &_| {
        let p = match *prop {
            Prop::Step(ref p) => p,
        };
        for i in 0 .. NUM_REGS {
            eprintln!("{:2}: {} -> {}", i, p.pre().regs()[i], p.post().regs()[i]);
        }
        eprintln!("cycle: {} -> {}", p.pre().cycle(), p.post().cycle());
        for pred in p.preds() {
            eprintln!("pred: {}", pred);
        }
    };
    //dump(pf.lemma(l_loop));

    let l_loop2 = pf.rule_step_seq(l_loop, l_loop, |vars| {
        let rest: [Option<Term>; 40] = array::from_fn(|_| Some(vars.var()));
        let mut rest1 = rest.clone();
        let mut rest2 = rest.clone();

        let forgotten: [Option<Term>; 5] = array::from_fn(|_| Some(vars.var()));
        let mut forgotten1: [Option<Term>; 5] = forgotten.clone();
        let mut forgotten2: [Option<Term>; 5] = forgotten.clone();

        let mut n2 = rest[12].clone();
        let mut n1 = Some(Term::add(n2.clone().unwrap(), Term::const_((-1_i64) as u64)));

        let mut cycle2 = rest[33].clone();
        let mut cycle1 = Some(Term::add(cycle2.clone().unwrap(), Term::const_(13)));

        (
            SubstTable::new(move |v| match v {
                12 => n2.take().unwrap(),
                33 => cycle2.take().unwrap(),
                35 => forgotten2[0].take().unwrap(),
                36 => forgotten2[1].take().unwrap(),
                37 => forgotten2[2].take().unwrap(),
                38 => forgotten2[3].take().unwrap(),
                39 => forgotten2[4].take().unwrap(),
                _ => rest2[v].take().unwrap(),
            }),
            SubstTable::new(move |v| match v {
                12 => n1.take().unwrap(),
                33 => cycle1.take().unwrap(),
                11 => forgotten1[0].take().unwrap(),
                13 => forgotten1[1].take().unwrap(),
                14 => forgotten1[2].take().unwrap(),
                15 => forgotten1[3].take().unwrap(),
                32 => forgotten1[4].take().unwrap(),
                _ => rest1[v].take().unwrap(),
            }),
        )
    })?;

    let gt_1 = Pred::Nonzero(Term::cmpa(regs[12].clone(), 1.into()));
    pf.rule_step_extend(l_loop2, |mut spf| {
        spf.rule_strengthen_preds(vec![gt_1], |ppf| {
            ppf.show();
            ppf.rule_nonzero_const(1);
            ppf.rule_gt_sub_unsigned(regs[12].clone(), 1.into(), 1.into())?;
            ppf.rule_gt_ge_unsigned(regs[12].clone(), 1.into(), 0.into())?;
            ppf.show();
            Ok(())
        })
    })?;

    dump(pf.lemma(l_loop2));

    let l_loop4 = pf.rule_step_seq(l_loop2, l_loop2, |vars| {
        let rest: [Option<Term>; 40] = array::from_fn(|_| Some(vars.var()));
        let mut rest1 = rest.clone();
        let mut rest2 = rest.clone();

        let forgotten: [Option<Term>; 5] = array::from_fn(|_| Some(vars.var()));
        let mut forgotten1: [Option<Term>; 5] = forgotten.clone();
        let mut forgotten2: [Option<Term>; 5] = forgotten.clone();

        let mut n2 = rest[12].clone();
        let mut n1 = Some(
            Term::add(
                Term::add(
                    n2.clone().unwrap(),
                    Term::const_((-1_i64) as u64),
                ),
                Term::const_((-1_i64) as u64),
            ),
        );

        let mut cycle2 = rest[33].clone();
        let mut cycle1 = Some(
            Term::add(
                Term::add(
                    cycle2.clone().unwrap(),
                    Term::const_(13),
                ),
                Term::const_(13),
            ),
        );

        (
            SubstTable::new(move |v| match v {
                12 => n2.take().unwrap(),
                33 => cycle2.take().unwrap(),
                35 => forgotten2[0].take().unwrap(),
                36 => forgotten2[1].take().unwrap(),
                37 => forgotten2[2].take().unwrap(),
                38 => forgotten2[3].take().unwrap(),
                39 => forgotten2[4].take().unwrap(),
                _ => rest2[v].take().unwrap(),
            }),
            SubstTable::new(move |v| match v {
                12 => n1.take().unwrap(),
                33 => cycle1.take().unwrap(),
                11 => forgotten1[0].take().unwrap(),
                13 => forgotten1[1].take().unwrap(),
                14 => forgotten1[2].take().unwrap(),
                15 => forgotten1[3].take().unwrap(),
                32 => forgotten1[4].take().unwrap(),
                _ => rest1[v].take().unwrap(),
            }),
        )
    })?;
    //dump(pf.lemma(l_loop4));

    dbg!(l_loop);
    dbg!(l_loop2);

    Ok(())
}

fn main() {
    env_logger::init();
    let args = env::args().collect::<Vec<_>>();
    assert_eq!(args.len(), 2, "must provide cbor path");
    import::with_globals(|| run(&args[1]).unwrap());
}

