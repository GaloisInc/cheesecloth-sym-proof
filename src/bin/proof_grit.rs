//! Load a CBOR file and concretely execute it, checking each step against the CBOR trace.
use std::array;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::env;
use env_logger;
use log::trace;
use sym_proof::{Word, Addr};
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
    let dump_preds = |prop: &_| {
        let p = match *prop {
            Prop::Step(ref p) => p,
        };
        for pred in p.preds() {
            eprintln!("pred: {}", pred);
        }
        for pred in p.derived_preds() {
            eprintln!("pred (derived): {}", pred);
        }
    };
    dump(pf.lemma(l_loop));

    let mut l_loops = vec![l_loop];
    for i in 0 .. 6 {
        eprintln!("\n ===== build {}-iteration proof =====", 2 << i);
        let l_prev = *l_loops.last().unwrap();

        let l_cur = pf.rule_step_seq(l_prev, l_prev, |vars| {
            let rest: [Option<Term>; 40] = array::from_fn(|_| Some(vars.var()));
            let mut rest1 = rest.clone();
            let mut rest2 = rest.clone();

            let forgotten: [Option<Term>; 5] = array::from_fn(|_| Some(vars.var()));
            let mut forgotten1: [Option<Term>; 5] = forgotten.clone();
            let mut forgotten2: [Option<Term>; 5] = forgotten.clone();

            let mut n2 = rest[12].clone();
            let mut n1 = Some(Term::add(n2.clone().unwrap(), Term::const_((-1_i64 << i) as u64)));

            let mut cycle2 = rest[33].clone();
            let mut cycle1 = Some(Term::add(cycle2.clone().unwrap(), Term::const_(13 << i)));

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

        eprintln!("before strengthen:");
        dump_preds(pf.lemma(l_cur));

        let bound = Term::const_((2 << i) - 1);
        let prev_bound = Term::const_((1 << i) - 1);
        let step = Term::const_(1 << i);
        let gt_bound = Pred::Nonzero(Term::cmpa(regs[12].clone(), bound.clone()));
        pf.rule_step_extend(l_cur, |mut spf| {
            spf.rule_strengthen_preds(vec![gt_bound], |ppf| {
                //ppf.show();
                ppf.rule_nonzero_const(1);
                ppf.rule_gt_ge_unsigned(regs[12].clone(), bound.clone(), prev_bound.clone())?;
                ppf.rule_gt_sub_unsigned(regs[12].clone(), bound.clone(), step.clone())?;
                ppf.show();
                Ok(())
            })
        })?;

        eprintln!("after strengthen:");
        dump_preds(pf.lemma(l_cur));

        //dump(pf.lemma(l_cur));
        l_loops.push(l_cur);
    }

    let l_loop48 = {
        eprintln!("\n ===== build {}-iteration proof =====", 48);
        let l_loop16 = l_loops[4];
        let l_loop32 = l_loops[5];

        let l_loop48 = pf.rule_step_seq(l_loop16, l_loop32, |vars| {
            let rest: [Option<Term>; 40] = array::from_fn(|_| Some(vars.var()));
            let mut rest1 = rest.clone();
            let mut rest2 = rest.clone();

            let forgotten: [Option<Term>; 5] = array::from_fn(|_| Some(vars.var()));
            let mut forgotten1: [Option<Term>; 5] = forgotten.clone();
            let mut forgotten2: [Option<Term>; 5] = forgotten.clone();

            let mut n2 = rest[12].clone();
            let mut n1 = Some(Term::add(n2.clone().unwrap(), Term::const_((-16_i64) as u64)));

            let mut cycle2 = rest[33].clone();
            let mut cycle1 = Some(Term::add(cycle2.clone().unwrap(), Term::const_(13 * 16)));

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

        dump(pf.lemma(l_loop48));
        l_loop48
    };


    let p = pf.lemma(l_loop48).as_step().unwrap();
    // This version fails, since concretely the loop only runs 63 times, not 64:
    //let p = pf.lemma(l_loops[6]).as_step().unwrap();

    // Check that the precondition holds on the concrete state.  We have to provide a value for
    // each variable, similar to the substitution provided when joining lemmas.
    // FIXME: "forgotten" vars should be existential, not universal.  The current formulation of
    // StepProp lets us assert that a bunch of registers are zero after the loop, which is false.
    let conc_subst: [Word; 40] = array::from_fn(|i| match i {
        0 ..= 32 => conc_state.regs[i],
        33 => conc_state.cycle,
        _ => 0,
    });
    p.check_pre_concrete(&conc_subst, &conc_state)?;

    // The postcondition must hold under the same substitution, so we can compute the final cycle
    // count.
    let post_cycle = p.post().cycle.eval(&conc_subst);
    eprintln!("cycle count: {} -> {}", conc_state.cycle, post_cycle);

    Ok(())
}

fn main() {
    env_logger::init();
    let args = env::args().collect::<Vec<_>>();
    assert_eq!(args.len(), 2, "must provide cbor path");
    import::with_globals(|| run(&args[1]).unwrap());
}

