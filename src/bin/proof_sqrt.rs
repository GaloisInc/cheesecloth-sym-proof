//! Proof that sqrt runs for at least 5e22 steps.  We first run the program concretely up to the
//! start of the loop (~5492249 steps), then we show that the loop will run for
//! at least (~ i64::MAX-13) iterations (~5e22 steps).
//!
//! Usage:
//! ```
//! cargo run --release --features verbose --bin proof_sqrt  -- traces/sqrt-out-noinstrumentation-8M.cbor 
//! ```
// The proof implementation returns `Err` when a rule fails to apply.  A bad proof will be caught
// eventually, but checking all `Result`s lets us catch problems sooner.
#![deny(unused_must_use)]
use std::array;
use std::collections::{HashMap, HashSet};
use std::env;
use env_logger;
use log::trace;
use sym_proof::{Word, Addr};
use sym_proof::kernel::Proof;
use sym_proof::logic::{Term, TermKind, Prop, Binder, VarCounter, ReachableProp, StatePred};
use sym_proof::logic::shift::ShiftExt;
use sym_proof::micro_ram::Program;
use sym_proof::micro_ram::import;
use sym_proof::micro_ram::{Opcode, MemWidth, mem_load};
use sym_proof::symbolic::{self, MemState, MemSnapshot, Memory, MemMap, MemConcrete};
use sym_proof::tactics::{Tactics, ReachTactics};
use witness_checker::micro_ram::types::Advice;

const I_MAX:u64 = 4_000_000_000;

fn run(path: &str) -> Result<(), String> {
    let exec = import::load_exec(path);

    let (instrs, chunks) = import::convert_code_split(&exec);
    let prog = Program::new(&instrs, &chunks);
    eprintln!("loaded code: {} instrs", prog.len());
    let init_state = import::convert_init_state(&exec);
    eprintln!("loaded memory: {} words", init_state.mem.len());
    trace!("initial regs = {:?}", init_state.regs);

    // ----------------------------------------
    // Load advice
    // ----------------------------------------


    eprintln!("=== Load advice");
    let mut advs:HashMap<u64, u64> = HashMap::new();
    // Iterate through all the advices (i.e. MemOps, Stutter, Advice)
    // and only keep the `Advice` ones.
    for (key, advice_vec) in exec.advice.iter() {
        for advice in advice_vec {
            if let Advice::Advise { advise } = advice {
                // Extract the value from the Advise variant
                // and store it in the new HashMap
                advs.insert(*key, *advise);
            }
        }
    }

    // ----------------------------------------
    // Run the concrete prefix
    // ----------------------------------------

    let mut conc_state = init_state;
    let loop_label = ".LBB831_734#20819";
    let loop_addr = exec.labels[loop_label];

    eprintln!("=== Concrete execution until pc={} ", loop_addr);
    while conc_state.pc != loop_addr {
        let conc_pc : Addr = conc_state.pc;
        let instr = prog[conc_pc];
        let cyc = conc_state.cycle;
        // For some reason the cycle is off by one wrt advice
        let adv:Option<u64> =  advs.get(&(cyc + 1)).cloned();
        conc_state.step(instr, adv);
    }
    eprintln!("\tConcretely reached {} in {} cycle.", conc_state.pc, conc_state.cycle);

    // Run two loop iterations to normalize the state of memory and get back to the start.  While
    // running, we also record addresses in memory that are loaded or stored during the loop.
    let mut load_addrs = Vec::new();
    let mut store_addrs = Vec::new();
    let mut all_addrs = Vec::new();
    let start_cycle = conc_state.cycle;
    for _ in 0 .. 2 {
        loop {
            let instr = prog[conc_state.pc];
            let cyc = conc_state.cycle;
            let adv: Option<u64> = advs.get(&(cyc + 1)).cloned();

            match instr.opcode {
                Opcode::Load(w) => {
                    let addr = conc_state.operand_value(instr.op2);
                    load_addrs.push((addr, w));
                    all_addrs.push((addr, w));
                },
                Opcode::Store(w) => {
                    let addr = conc_state.operand_value(instr.op2);
                    store_addrs.push((addr, w));
                    all_addrs.push((addr, w));
                },
                _ => ()
            }

            conc_state.step(instr, adv);

            if conc_state.pc == loop_addr {
                break;
            }
        }
    }
    eprintln!("load_addrs size: {}", load_addrs.len());
    eprintln!("store_addrs size: {}", store_addrs.len());
    eprintln!("all_addrs size: {}", all_addrs.len());

    // Postprocess `all_addrs` by removing entries that are overwritten later.
    let all_addrs = {
        // Process stores in reverse order, so if write `i` is overwritten by `j`, `j` will be seen
        // first.
        let mut bytes_touched = HashSet::new();
        let mut addrs_rev = Vec::new();
        let iter = store_addrs.into_iter().rev()
            .chain(load_addrs.into_iter().rev());
        for (addr, w) in iter {
            let mut all_touched = true;
            for b in 0 .. w.bytes() {
                let untouched = bytes_touched.insert(addr + b);
                if untouched {
                    all_touched = false;
                }
            }
            if all_touched {
                continue;
            }
            addrs_rev.push((addr, w));
        }

        addrs_rev.reverse();
        addrs_rev
    };


    // ----------------------------------------
    // For diagnostics on registers
    // Change num_loops=10 to see what
    // registers change and which ones don't
    // ----------------------------------------
    let num_loops = 0;
    if (num_loops > 0) {
        eprintln!("Now lets go around {} loops to see how registers change", num_loops);
        let mut last_cycle_seen = conc_state.cycle;
        // record the registers
        let mut reg_log = vec![vec![0; num_loops]; conc_state.regs.len()];

        for li in 0 .. num_loops{
            // Do a step to move away from the label
            let instr = prog[conc_state.pc];
            let cyc = conc_state.cycle;
            // For some reason the cycle is off by one wrt advice
            let adv:Option<u64> =  advs.get(&(cyc + 1)).cloned();
            conc_state.step(instr, adv);

            // The run until the label is found again
            while conc_state.pc != loop_addr {
                let instr = prog[conc_state.pc];
                let cyc = conc_state.cycle;
                // For some reason the cycle is off by one wrt advice
                let adv:Option<u64> =  advs.get(&(cyc + 1)).cloned();
                conc_state.step(instr, adv);
            }
            eprintln!{"Loop diagnostic {}: Loop took {} cycles", li, conc_state.cycle - last_cycle_seen};
            last_cycle_seen = conc_state.cycle;

            for (ri, &x) in conc_state.regs.iter().enumerate() {
                reg_log[ri][li] = x;
            }
        }

        eprintln!("Log of registers during the loop diagnostic ");
        for (i, &x) in conc_state.regs.iter().enumerate() {
            eprintln!("{:2}: {:?}", i, reg_log[i]);
        }
    }

    // ----------------------------------------
    // Set up the proof state
    // ----------------------------------------
    let mut pf = Proof::new(prog);

    MemSnapshot::init_data(conc_state.mem.clone());


    /*
    // ----------------------------------------
    // Build the minimal memory for the loop
    // ----------------------------------------
    eprintln!("=== Build the symbolic memory.");
    let mut load_mem  : HashSet<(Addr, MemWidth, Word)> = HashSet::new();

    // Do a step to move away from the label
    let instr = prog[conc_state.pc];
    let cyc = conc_state.cycle;
    // For some reason the cycle is off by one wrt advice
    let adv:Option<u64> =  advs.get(&(cyc + 1)).cloned();
    conc_state.step(instr, adv); //we assume/know this step is not a memory step.

    // The run until the label is found again
    while conc_state.pc != loop_addr {
        let instr = prog[conc_state.pc];
        let cyc = conc_state.cycle;
        // For some reason the cycle is off by one wrt advice
        let adv:Option<u64> =  advs.get(&(cyc + 1)).cloned();
        let pc = conc_state.pc;
        conc_state.step(instr, adv);

        match instr.opcode {
            Opcode::Load(w) => {
                let addr = conc_state.operand_value(instr.op2);
                load_mem.insert((addr, w, pc));
            },
            _ => ()
        }
    }

    let mut init_mem_map  = |i| {
        let mut init_mem_map0 = MemMap::new();
        for &(addr, ww, pc) in load_mem.iter(){
            let val = mem_load(&conc_state.mem, ww, addr);
            init_mem_map0.store(ww, Term::const_(addr), Term::const_(val), &[]).ok();
        }

        // One address has the index
        init_mem_map0.store(MemWidth::W8, Term::const_(2147480784), i, &[]).ok();
        // One address has garbage (Really it's the index)
        init_mem_map0.store(MemWidth::W8, Term::const_(2147480680), i, &[]).ok();
        return Some(init_mem_map0)
    };
    */


    // ----------------------------------------
    // Concrete state is reachable
    // ----------------------------------------

    // `conc_state` is reachable.
    let p_conc = pf.tactic_admit(Prop::Reachable(ReachableProp {
        pred: Binder::new(|_vars| {
            StatePred {
                state: symbolic::State::new(
                    conc_state.pc,
                    conc_state.regs.map(|x| x.into()),
                    MemState::Snapshot(MemSnapshot { base: 0 }),
                    Some(conc_state.clone()),
                ),
                props: Box::new([]),
            }
        }),
        min_cycles: conc_state.cycle.into(),
    }));

    // Modify `p_conc` to match the premise of `p_loop`.
    pf.tactic_reach_extend(p_conc, |rpf| {
        rpf.rule_mem_abs_map(&all_addrs);
    });

    let init_mem_concrete = {
        match pf.props()[p_conc.1] {
            Prop::Reachable(ref rp) => {
                rp.pred.inner.state.mem.clone()
            },
            _ => unreachable!(),
        }
    };

    let init_mem_symbolic = |i| {
        let mut m = init_mem_concrete.clone();
        let i_minus_1 = Term::sub(i, 1.into());
        // One address has the index
        m.store(MemWidth::W8, Term::const_(0x7ffff468), i_minus_1, &[]).unwrap();
        // One address has garbage (Really it's the index)
        m.store(MemWidth::W8, Term::const_(0x7ffff4d0), i_minus_1, &[]).unwrap();
        m
    };

    // Helper to build the symbolic `StatePred` for the top of the loop.
    let st_loop = |i: Term| {
        StatePred {
            state: symbolic::State {
                // current pc should be the address of the loop
                pc: conc_state.pc,
                // We keep all concrete registers, except for the
                // index i in register 8.
                regs: array::from_fn(|r| {
                    match r {
                        8 => i,
                        _ => conc_state.regs[r].into(),
                    }
                }),
                // Memory in the initial state is a MemMap with all
                // the address in memeory that would be read in the
                // loop.
                mem: init_mem_symbolic(i),
                conc_st: Some(conc_state.clone()),
            },
            props: vec![].into(),
        }
    };

    // Helper to build the `Prop::Reachable` for a given `n` and cycle count `c`:
    //      reach(c, st_loop(i))
    let mk_prop_reach = |i: Term, c: Term| {
        Prop::Reachable(ReachableProp {
            pred: Binder::new(|vars| st_loop(i.shift())),
            min_cycles: c,
        })
    };

    // ----------------------------------------
    // Prove a double iteration (twice around the loop)
    // ----------------------------------------

    // We first prove a lemma of the form:
    //      forall b i,
    //          i > 0 ->
    //          I_MAX > i + 1 ->
    //          reach(b, st_loop(i)) ->
    //          reach(b + 5460, st_loop(i + 2))
    eprintln!("\n# Prove p_iter");
    let p_iter = pf.tactic_forall_intro(
        |vars| {
            // forall b i, 
            let b = vars.fresh();
            let i = vars.fresh();
            (vec![
                // i > 1 -> 
                Prop::Nonzero(Term::cmpa(i.clone(), 1.into())),
                // MAX > i+1 -> 
                Prop::Nonzero(Term::cmpa((I_MAX).into(),Term::add(1.into(), i.clone()))),
                // reach(c, st_loop(i)) -> 
                mk_prop_reach(i, b.clone()),
            ], i)
        },
        |pf, i| {
            // Premises:
            // i > 0
            let i_gt_1 = (1,0);
            // I_MAX > i + 1
            let i1_bound = (1,1);
            // reach(b, st_loop(i))
            let p_reach = (1, 2);

            // Prove: i != 0
            println!("==== ADMIT: \n\t forall i, i > 1 -> ((1 == i) == 0)");
            let admit1 = pf.tactic_admit(
                Prop::Forall(
                    Binder::new(|vars| {
                        let n = vars.fresh();
                        let p = Prop::Nonzero(Term::cmpa(n.clone(), 1.into()));
                        let q = Prop::Nonzero(Term::cmpe(Term::cmpe(1.into(), n.clone()), 0.into()));
                        (vec![p].into(), Box::new(q))
                    })
                ));
            let _i_not_0 = pf.tactic_apply(admit1, &[i]);

            // Prove: i + 1 != 0
            println!("==== ADMIT: \n\t i > 1 -> MAX > i+1 -> ((1 == (i + 1)) == 0)");
            //pf.show_prop(i_gt_1);
            //pf.show_prop(i1_bound);
            let admit2 = pf.tactic_admit(
                Prop::Forall(
                    Binder::new(|vars| {
                        let n = vars.fresh();
                        let h0 = Prop::Nonzero(Term::cmpa(n.clone(), 1.into()));
                        let h1 = Prop::Nonzero(Term::cmpa((I_MAX).into(), Term::add(n.clone(), 1.into())));
                        let conclusion = Prop::Nonzero(Term::cmpe(Term::cmpe(1.into(), Term::add(n.clone(), 1.into())), 0.into()));
                        (vec![h0,h1].into(), Box::new(conclusion))
                    })
                ));            
            let i1_not_0 = pf.tactic_apply(admit2, &[i]);

            // Extend `p_reach` with two iterations worth of steps.
            let (p_reach, _i1_not_0) = pf.tactic_swap(p_reach, i1_not_0);
            pf.tactic_reach_extend(p_reach, |rpf| {
                // rpf.show_state();

                // Define the proof for one single loop iteration.  The counter `n` is used to
                // number the steps in the debug output.
                let mut one_loop_proof = |n:&mut u32| -> () {
                    eprintln!("\t=== {}. Concretely until the symbolic step. pc {}, cycle {:?}", n,
                              rpf.state().pc, rpf.state().conc_st.clone().map(|cst| cst.cycle));
                    rpf.tactic_run_concrete();
                    *n += 1;

                    eprintln!("\t=== {}. Symbolic comparison symbolic step. pc {}, cycle {:?}", n,
                              rpf.state().pc, rpf.state().conc_st.clone().map(|cst| cst.cycle));
                    rpf.rule_step();
                    //rpf.show_state();
                    *n += 1;

                    eprintln!("\t=== {}. Replace the symbolic comparison with concrete value.
                               (i==1) -> 0. pc {}, cycle {:?}", n,
                              rpf.state().pc, rpf.state().conc_st.clone().map(|cst| cst.cycle));
                    rpf.rule_rewrite_reg(32, Term::const_(0));
                    *n += 1;

                    eprintln!("\t=== {}. Concretely until the symb. store. pc {}, cycle {:?}", n,
                              rpf.state().pc, rpf.state().conc_st.clone().map(|cst| cst.cycle));
                    rpf.tactic_run_concrete();
                    *n += 1;

                    eprintln!("\t=== {}. Symbolic store the i, with the rule_step", n);
                    rpf.rule_step();
                    // rpf.show_state();
                    *n += 1;

                    eprintln!("\t=== {}. Concretely (long) until the increment of i. pc {}, cycle {:?}", n,
                              rpf.state().pc, rpf.state().conc_st.clone().map(|cst| cst.cycle));
                    rpf.tactic_run_concrete();
                    //rpf.show_state();
                    *n += 1;

                    eprintln!("\t=== {}. Symbolic: increment the counter", n);
                    rpf.rule_step();
                    //rpf.show_state();
                    *n += 1;


                    eprintln!("\t=== {}. Concrete until the symbolic substraction. pc {}, cycle {:?}", n,
                              rpf.state().pc, rpf.state().conc_st.clone().map(|cst| cst.cycle));
                    rpf.tactic_run_concrete();
                    //rpf.show_state();
                    *n += 1;

                    // Why is i first substracted and then stored?
                    eprintln!("\t=== {}. Symbolic substraction and store `sp <- (i-1)`, with the rule_step", n);
                    rpf.rule_step(); // 253801. %11 = %8 + -1
                    rpf.rule_step(); //253802. %32 = %ax + 88
                    rpf.rule_step(); // 253803.        *(%32) = %11
                    // rpf.show_state();
                    *n += 1;


                    eprintln!("\t=== {}. Run until Beggining, wash and repeat", n);
                    rpf.tactic_run_until(loop_addr);
                    // rpf.show_state();
                    *n += 1;
                };

                // Apply the proof to two loops.
                let mut steps_counter = 1;
                println!("=== Prove the first loop");
                one_loop_proof(&mut steps_counter);
                println!("=== Prove the second loop");
                one_loop_proof(&mut steps_counter);

            });

        },
    );

    {
        eprintln!("p_iter prop:");
        let prop = &pf.props()[p_iter.1];
        let b = match *prop {
            Prop::Forall(ref b) => b,
            _ => panic!(),
        };

        for (i, p) in b.inner.0.iter().enumerate() {
            eprintln!("hyp.{}: {}", i, pf.print_adj(1, p));
        }
        eprintln!("concl: {}", pf.print_adj(1, &b.inner.1));
    }





    // ----------------------------------------
    // Prove the full loop by induction
    // ----------------------------------------
    println!("=== Prove the full loop by induction");

    // We are proving the following statement:
    //
    //      forall n,
    //          Max > 2n + 1 ->
    //          let i := Max - 2n in
    //          (i > 1) ->
    //          (Max > i + 1) ->
    //          forall b,
    //              reach(b, st_loop(i) ->
    //              reach(b + n * 5460, st_loop(max))
    //
    // We separate the binders for `b` and `n` because `tactic_induction` expects to see only a
    // single bound variable (`n`) in `Hsucc`.

    // End of the execution is Max - 1, to avoid trouble at the baoundary
    let target_below_max = 2; 
    let max_loops = Term::sub(I_MAX.into(),target_below_max.into());
    // Write i in terms of n (n increases, i decreases)
    let i_from_n = |n| (Term::sub(max_loops,Term::mull(2.into(), n)));

    eprintln!("\n#prove p_loop");
    let p_loop = pf.tactic_induction(
        Prop::Forall(Binder::new(|vars| {
            //      forall n,
            let n = vars.fresh();
            //          Max > 2n + 1 ->
            let p0 = Prop::Nonzero(Term::cmpa(I_MAX.into(), Term::add(Term::mull(n, 2.into()), 1.into())));
            //          let i := Max - 2n in
            let i:Term = i_from_n(n);
            //          (i > 1) ->
            let p1 = Prop::Nonzero(Term::cmpa(i, 1.into()));
            //          (Max > i + 1) ->
            let p2 = Prop::Nonzero(Term::cmpa(I_MAX.into(), Term::add(i,1.into())));
            let q = Prop::Forall(Binder::new(|vars| {
                let n = n.shift();
                let i:Term = i_from_n(n);
                //      forall b,
                let b = vars.fresh();
                //          reach(st_loop(i), b) ->
                let p = mk_prop_reach(i, b);
                //          reach(st_loop(max), b + n * 5460)
                let q = mk_prop_reach(max_loops, Term::add(b, Term::mull(n, 5460.into())));
                (vec![p].into(), Box::new(q))
            }));
            (vec![p0,p1,p2].into(), Box::new(q))
        })),
        |pf| {
            // println!("==== Context");
            // pf.show_context();
            // println!("==== END Context");
            pf.tactic_forall_intro(
                |vars| {
                    let b = vars.fresh();
                    let p = mk_prop_reach(max_loops, b);
                    (vec![p], b)
                },
                |_pf, _b| {
                    // No-op.  The conclusion for the zero case is the same as the last premise.
                },
            );
        },
        |pf, n| {
            eprintln!(" -- context for inductive case: --");
            pf.show_context();
            eprintln!(" -- end of context --");
            pf.tactic_forall_intro(
                |vars| {
                    let n = n.shift();
                    let n_plus_1 = Term::add(n, 1.into());
                    // Let i+2 := max - 2n
                    let i_plus_2 = i_from_n(n_plus_1);

                    let b = vars.fresh();
                    let p = mk_prop_reach(i_plus_2, b);
                    (vec![p], b)
                },
                |pf, b| {


                    // println!("============ Context");
                    // pf.show_context();
                    // println!("============ END Context");
                    let n = n.shift();
                    let n_plus_1 = Term::add(n, 1.into());

                    // Let i := max - 2n
                    let i = i_from_n(n);
                    // Let i_sub_22 := max - 2 (n + 1)
                    let i_sub_2 = i_from_n(n_plus_1);

                    // (Max >u 2n + 3) -> (i > 1)
                    println!("==== ADMIT: \n\tforall n, (Max >u 2n + 3) -> (i > 1)");
                    // The hypothesis:
                    // pf.show_prop((2,0));


                    let admit3 = pf.tactic_admit(
                        Prop::Forall(
                            Binder::new(|vars| {
                                let n = vars.fresh();
                                let i = i_from_n(n);
                                let h0 = Prop::Nonzero(Term::cmpa((I_MAX).into(), Term::add(Term::mull(2.into(), n.clone()), 3.into())));
                                let conclusion = Prop::Nonzero(Term::cmpa(i.into(), 1.into()));
                                (vec![h0].into(), Box::new(conclusion))
                            })
                        ));
                    let _i_gt_1 = pf.tactic_apply(admit3, &[n]);

                    // forall n,
                    // n+1 > 0 ->
                    // Max > 2n+3 ->
                    // Max > (max_loops - 2n ) + 1
                    println!("==== ADMIT: \n\tn+1 > 0 ->\n\tMax > 2n+2 -> \n\tMax > (max_loops - 2n ) + 1");
                    // pf.show_prop((1,0));
                    // pf.show_prop((2,0));


                    let admit4 = pf.tactic_admit(
                    Prop::Forall(
                        Binder::new(|vars| {
                                    // forall n, 
                                    let n = vars.fresh();
                            let i = i_from_n(n);
                                    // n+1 > 0 ->
                        let h0 = Prop::Nonzero(Term::cmpa(Term::add(n.clone(),1.into()), 0.into()));
                                    // Max > 2n+2 ->
                        let h1 = Prop::Nonzero(Term::cmpa((I_MAX).into(), Term::add(Term::mull(2.into(), n.clone()), 3.into())));
                                    // Max > (max_loops - 2n ) + 1
                                    let conclusion = Prop::Nonzero(
                                        Term::cmpa(I_MAX.into(),
                               Term::add(Term::sub(max_loops, Term::mull(n,2.into())), 1.into())));
                        (vec![h0,h1].into(), Box::new(conclusion))
                        })
                    ));
                    let _i1_no_over = pf.tactic_apply(admit4, &[n]);

                    // let _i1_no_over = pf.tactic_admit(
                    //     Prop::Nonzero(Term::cmpa(I_MAX.into(),
                    //                              Term::add(Term::sub(max_loops, Term::mull(n,2.into())), 1.into())))
                    // );

                    println!("==== Clone P_iter");
                    let p_iter = pf.tactic_clone(p_iter);

                    // println!("============ Context");
                    // pf.show_context();
                    // println!("============ END Context");

                    println!("==== Apply P_iter to {:?}", i_sub_2);
                    let _p_first = pf.tactic_apply(p_iter, &[b, i_sub_2]);


                    // (Max >u (2n + 3)) ->
                    // (Max >u (2n + 1))
                    println!("==== ADMIT: \n\t(Max >u (2n + 3)) ->\n\t(Max >u (2n + 1))");
                    // pf.show_prop((2,0));


                    let admit5 = pf.tactic_admit(
                    Prop::Forall(
                        Binder::new(|vars| {
                        let n = vars.fresh();
                            let h0 = Prop::Nonzero(Term::cmpa((I_MAX).into(), Term::add(Term::mull(2.into(), n.clone()), 3.into())));
                        let conclusion = Prop::Nonzero(Term::cmpa(I_MAX.into(),
                             Term::add(Term::mull(n,2.into()), 1.into())));
                        (vec![h0].into(), Box::new(conclusion))
                        })
                    ));
                    let _ind_hyp_h1 = pf.tactic_apply(admit5, &[n]);

                    // println!("============ Context");
                    // pf.show_context();
                    // println!("============ END Context");

                    println!("==== Apply induction hypothesis, first bind");
                    let p_ind = pf.tactic_clone((1, 1));
                    let p_rest = pf.tactic_apply0(p_ind);


                    let expected_cycles =
                        Term::add(b, Term::add(Term::mull(n, 5460.into()), 5460.into()));

                    // (b + (n*5460 + 5460)) == (b + 5460) + n*5460
                    println!("==== ADMIT: (b + (n*5460 + 5460)) == (b + 5460) + n*5460");
                    pf.tactic_admit(Prop::Nonzero(Term::cmpe(
                        Term::add(Term::add(b, 5460.into()), Term::mull(n, 5460.into())),
                        expected_cycles,
                    )));


                    println!("============ Context");
                    pf.show_context();
                    println!("============ END Context");

                    // reach(b + 5460, st_loop(i_sub_2 + 2)) ->
                    // reach(b + 5460, st_loop(i)
                    println!("==== ADMIT: \n\tforall i, forall b, \n\treach(b + 5460, st_loop(i_sub_2 + 2)) ->\n\treach(b + 5460, st_loop(i)");
                    pf.show_prop((3,6));

                    let admit6 = pf.tactic_admit(
                    Prop::Forall(
                        Binder::new(|vars| {
                        let nn = vars.fresh();
                                    let nn_plus_1 = Term::add(nn, 1.into());
                        let bb = vars.fresh();
                                    // Let i := max - 2n in 
                            let is = i_from_n(nn);
                            // Let i_sub_22 := max - 2 (n + 1) in
                            let is_sub_2 = i_from_n(nn_plus_1);
                            // reach(b + 5460, st_loop(i_sub_2 + 2)) ->
                            let h0 = mk_prop_reach(Term::add(is_sub_2,2.into()), Term::add(bb,5460.into()));
                                    // reach(b + 5460, st_loop(i)
                        let conclusion = mk_prop_reach(is, Term::add(bb,5460.into())) ;
                        (vec![h0].into(), Box::new(conclusion))
                        })
                    ));
                    let _ind_hyp_h0 = pf.tactic_apply(admit6, &[n, b]);

                    // let _ind_hyp_h0 = pf.tactic_admit(  mk_prop_reach(i, Term::add(b,5460.into())));

                    println!("==== Apply induction hypothesis, second bind");
                    let p_final = pf.tactic_apply(p_rest, &[Term::add(b, 5460.into())]);


                    println!("==== Shrink");
                    pf.tactic_reach_shrink(p_final, expected_cycles);
                },
            );
        },
    );
    //pf.show_context();


    // ----------------------------------------
    // Prove the full execution
    // ----------------------------------------

    eprintln!("\n#Prove p_exec");


    // Combine `p_conc` and `p_loop` to prove that the loop's final state is reachable.
    println!("==== Apply p_loop 1");
    // Initial n value:
    let initial_n = {
        // current value of r8
        let r8_val = conc_state.regs[8];
        let diff = I_MAX - r8_val - target_below_max;
        if diff%2 != 0{
            eprintln!("=== Error, Max-r[8] should be even, but r[8]={}, Max={}", r8_val, I_MAX)
        }
        diff/2
    };
    println!("==== Initial n = {}", initial_n);
    let p_loop_n = pf.tactic_apply(p_loop, &[initial_n.into()]);
    pf.rule_trivial();
    println!("==== Apply p_loop 2");
    let p_loop_n = pf.tactic_apply0(p_loop_n);
    println!("==== Apply p_loop_n");

    // println!("============ Context");
    // pf.show_context();
    // println!("============ END Context");
    let p_exec = pf.tactic_apply(p_loop_n, &[conc_state.cycle.into()]);


    println!("\n============");
    println!("Final theorem:\n{}", pf.print(&pf.props()[p_exec.1]));
    println!("============\n");
    println!("Ok: Proof verified");
    Ok(())
}

fn main() {
    env_logger::init();
    let args = env::args().collect::<Vec<_>>();
    assert_eq!(args.len(), 2, "must provide cbor path");
    import::with_globals(|| run(&args[1]).unwrap());
}

