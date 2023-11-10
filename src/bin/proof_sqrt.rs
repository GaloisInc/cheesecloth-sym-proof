//! Proof that grit runs for at least 1000 steps.  We first run the program concretely up to the
//! start of the first `memcpy` (~500 steps), then we show that the `memcpy` loop will run for
//! at least 63 iterations (~800 steps).
//!
//! Usage:
//! ```
//! cargo run --bin proof_grit -- grit.cbor
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
use sym_proof::logic::{Term, Prop, Binder, VarCounter, ReachableProp, StatePred};
use sym_proof::logic::shift::ShiftExt;
use sym_proof::micro_ram::Program;
use sym_proof::micro_ram::import;
use sym_proof::micro_ram::{Opcode, MemWidth, mem_load};
use sym_proof::symbolic::{self, MemState, MemLog, Memory, MemMap, MemConcrete};
use sym_proof::tactics::{Tactics, ReachTactics};
use witness_checker::micro_ram::types::Advice;

fn run(path: &str) -> Result<(), String> {
    let exec = import::load_exec(path);

    let (instrs, chunks) = import::convert_code_split(&exec);
    let prog = Program::new(&instrs, &chunks);
    eprintln!("loaded code: {} instrs", prog.len());
    let init_state = import::convert_init_state(&exec);
    eprintln!("loaded memory: {} words", init_state.mem.len());
    trace!("initial regs = {:?}", init_state.regs);

    // Load advice
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
    eprintln!("loaded advice");
    
    // ----------------------------------------
    // Run the concrete prefix
    // ----------------------------------------

    let mut conc_state = init_state;
    // Concrete execution until label LBB831_734#20819 which is near the loop.
    let loop_label = ".LBB831_734#20819";
    let loop_addr = exec.labels[loop_label];
    eprintln!("Starting concrete execution until label: {}, address: {} ", loop_label, loop_addr);
    while conc_state.pc != loop_addr {
	let conc_pc : Addr = conc_state.pc;
        let instr = prog[conc_pc];
	let cyc = conc_state.cycle;
	// For some reason the cycle is off by one wrt advice
	let adv:Option<u64> =  advs.get(&(cyc + 1)).cloned();
        conc_state.step(instr, adv);
    }

    eprintln!("STOPed the first run of concrete execution. Pc {}. Cycle {}", conc_state.pc, conc_state.cycle);
    

    // TODO: remmove this looping and make it lean.
    let num_loops = 10;
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
	eprintln!{"Testing the loop: Loop took {} cycles", conc_state.cycle - last_cycle_seen};
	last_cycle_seen = conc_state.cycle;

	for (ri, &x) in conc_state.regs.iter().enumerate() {
	    reg_log[ri][li] = x;
	}
    }

    eprintln!("Log of registers during the loop ");
    for (i, &x) in conc_state.regs.iter().enumerate() {
        eprintln!("{:2}: {:?}", i, reg_log[i]);
    }

    
    // TODO this could be done in a separate state. Or even do once
    // and store in a file.  We store the first time an address is
    // loaded with the value.
    // TODO: We could skip addresses that where stored first, but this
    // gets odd with the byte addressing.
    eprintln!("Now lets go around once more to register memory usage.");
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
    // At the end of the loop (i.e. back at the initial state) we fill
    // in the values of memory
    
    let mut init_mem_map = MemMap::new(u64::MAX);
    for &(addr, ww, pc) in load_mem.iter(){
	let val = mem_load(&conc_state.mem, ww, addr);
	init_mem_map.store(ww, Term::const_(addr), Term::const_(val), &[])?;
	let to_problem_address = addr - 4295563809;
	if addr.abs_diff(4295563809) < 10 {
            eprintln!("Loading to address {}. w={:?}, val={}, pc={}", addr, ww, val, pc); 
	    
	}
	    
    }

    
    
    // Run concretely: 8 steps to the start of the loop, then 11 more steps to run the first
    // iteration up to the condition check.  The loop is structured as a do/while, so the condition
    // check comes at the end.
    for _ in 0 .. 8 + 11 {
        let instr = prog[conc_state.pc];
        eprintln!("run concrete [{}]: {:?}", conc_state.pc, instr);
        conc_state.step(instr, None);
    }

    eprintln!("concrete registers:");
    for (i, &x) in conc_state.regs.iter().enumerate() {
        eprintln!("{:2}: 0x{:x}", i, x);
    }

    // ----------------------------------------
    // Set up the proof state
    // ----------------------------------------
    let mut pf = Proof::new(prog);


    // ----------------------------------------
    // Prove a single iteration
    // ----------------------------------------

    // We first prove a lemma of the form:
    //      forall b n, n > 0 -> R({r10 = i}, b) -> R({r10 = i + 2}, b + ???)
    // The proof is done by running symbolic execution.
    eprintln!("\nprove p_iter");
    let p_iter = pf.tactic_forall_intro(
        |vars| {
            // Set up the variables and premises.  There is only one variable, `n`, and only
            // one premise, `n > 0`.  The `Term` representing `n` will be passed through to the
            // proof callback.
            let b = vars.fresh();
            let i = vars.fresh();
            (vec![
		// i !=0
                Prop::Nonzero(Term::cmpa(i.clone(), 0.into())),
		// 1+i !=0
                Prop::Nonzero(Term::cmpa(Term::add(1.into(), i.clone()), 0.into())),
                Prop::Reachable(ReachableProp {
                    pred: Binder::new(|vars| {
                        let i = i.shift();
                        StatePred {
                            state: symbolic::State {
                                pc: conc_state.pc,
                                regs: array::from_fn(|r| {
                                    // We keep all registers concrete, except for the index i in register 8.
                                    match r {
					8 => i,
					_ => conc_state.regs[r].into(),
                                    }
                                }),
                                // Memory in the initial state is an empty `MemLog`, which implies
                                // that nothing is known about memory.
                                mem: MemState::Map(init_mem_map),
				conc_st: Some (conc_state.clone()),
                            },
                            props: vec![].into(),
                        }
                    }),
                    min_cycles: b.clone(),
                }),
            ], i)
        },
        |pf, i| {
            // The reachability is in the next context (1) and it is
            // the third prop (2)
            let p_reach = (1, 2);

            // We assume `i != 0` and `i+1 != 0`,
	    // so we can go around the loop twice.
	    let p_ne = pf.tactic_admit(
                Prop::Nonzero(Term::cmpe(Term::cmpe(i.clone(), 0.into()), 0.into())));
	    // ((1 == (a1 + 1)) == 0)
	    let i1_not_0 = pf.tactic_admit(
		Prop::Nonzero(Term::cmpe(Term::cmpe(1.into(), Term::add(i.clone(), 1.into())), 0.into())));
	    let p_ne1 = pf.tactic_admit(
                Prop::Nonzero(Term::cmpe(Term::cmpe(Term::add(i.clone(), 1.into()), 0.into()), 0.into())));

		
	    
            let (p_reach, p_ne1) = pf.tactic_swap(p_reach, p_ne1);
            // let _ = (p_ne,i1_not_0);

            pf.tactic_reach_extend(p_reach, |rpf| {
                //rpf.show_context();
                //rpf.show_state();

                // Symbolic execution through one iteration of the loop.
		
		eprintln!("1. Run concretely until. pc {}, cycle {:?}",
			  rpf.state().pc, rpf.state().conc_st.clone().map(|cst| cst.cycle));
                rpf.tactic_run_concrete();
		rpf.show_state();
		
		eprintln!("2. one symbolic step. pc {}, cycle {:?}",
			  rpf.state().pc, rpf.state().conc_st.clone().map(|cst| cst.cycle));
                rpf.rule_step();
		rpf.show_state();
		
		eprintln!("3. Run concretely until. pc {}, cycle {:?}",
			  rpf.state().pc, rpf.state().conc_st.clone().map(|cst| cst.cycle));
                rpf.tactic_run_concrete();
		rpf.show_state();

		eprintln!("4. Run a load, with the rule_step");
                rpf.rule_step();
		rpf.show_state();
		
                eprintln!("5. Run concretely until. pc {}, cycle {:?}",
			  rpf.state().pc, rpf.state().conc_st.clone().map(|cst| cst.cycle));
                rpf.tactic_run_concrete();
		rpf.show_state();

		eprintln!("6. Run until stuck");
                rpf.tactic_run_db();
		rpf.show_state();

		
                rpf.show_context();
		eprintln!("7. Run jump. pc {}, cycle {:?}",
			  rpf.state().pc, rpf.state().conc_st.clone().map(|cst| cst.cycle));
		rpf.show_state();
		rpf.tactic_run_concrete();
		rpf.rule_step_jump(false);

		eprintln!("8. Run until stuck");
		rpf.show_state();
		rpf.tactic_run();
		
		eprintln!("9. Run a Jump, pc {}, cycle {:?}",
			  rpf.state().pc, rpf.state().conc_st.clone().map(|cst| cst.cycle));
		rpf.show_state();
		rpf.rule_step_jump(false);
		
		eprintln!("10. Run until...pc {}, cycle {:?}",
			  rpf.state().pc, rpf.state().conc_st.clone().map(|cst| cst.cycle));
		rpf.show_state();
                rpf.tactic_run_until(conc_state.pc);

                // Erase information about memory and certain registers to make it easier to
                // sequence this `StepProp` with itself.
                for &r in &[11, 13, 14, 15, 32] {
                    rpf.rule_forget_reg(r);
                }
                rpf.rule_forget_mem();

                //rpf.show_state();
            });

            // Rename variables so the final state uses the same names as the initial state.
            pf.tactic_reach_rename_vars(p_reach, |vars| {
                let mut var_map = [None; 39];
                for i in 0 .. 33 {
                    var_map[i] = Some(vars.fresh_var().index());
                }
                var_map[34] = var_map[11];
                var_map[35] = var_map[13];
                var_map[36] = var_map[14];
                var_map[37] = var_map[15];
                var_map[38] = var_map[32];
                var_map
            });
        },
    );


    // ----------------------------------------
    // Prove the full loop by induction
    // ----------------------------------------

    // We are proving the following statement:
    //
    //      forall n,
    //          n < 1000 ->
    //          forall b,
    //              reach(b, {r12 = n}) ->
    //              reach(b + n * 13, {r12 = 0})
    //
    // We separate the binders for `b` and `n` because `tactic_induction` expects to see only a
    // single bound variable (`n`) in `Hsucc`.

    // Helper to build a `StatePred` with the loop counter set to `n`:
    //      { r12 = n }
    let mk_state_pred = |vars: &mut VarCounter, n: Term| {
        StatePred {
            state: symbolic::State {
                pc: conc_state.pc,
                regs: array::from_fn(|r| {
                    let v = vars.fresh();
                    match r {
                        8 => n.clone(),
			_ => conc_state.regs[r].into(),
                    }
                }),
                mem: MemState::Log(MemLog { l: Vec::new() }),
		conc_st: Some (conc_state.clone()),
            },
            props: vec![].into(),
        }
    };

    // Helper to build the `Prop::Reachable` for a given `n` and cycle count `c`:
    //      reach(c, { r12 = n })
    let mk_prop_reach = |n: Term, c: Term| {
        Prop::Reachable(ReachableProp {
            pred: Binder::new(|vars| mk_state_pred(vars, n.shift())),
            min_cycles: c,
        })
    };

    eprintln!("\nprove p_loop");
    let p_loop = pf.tactic_induction(
        Prop::Forall(Binder::new(|vars| {
            let n = vars.fresh();
            let p = Prop::Nonzero(Term::cmpa(1000.into(), n));
            let q = Prop::Forall(Binder::new(|vars| {
                let n = n.shift();
                let b = vars.fresh();
                let p = mk_prop_reach(n, b);
                let q = mk_prop_reach(0.into(), Term::add(b, Term::mull(n, 13.into())));
                (vec![p].into(), Box::new(q))
            }));
            (vec![p].into(), Box::new(q))
        })),
        |pf| {
            //pf.show_context();
            pf.tactic_forall_intro(
                |vars| {
                    let b = vars.fresh();
                    let p = mk_prop_reach(0.into(), b);
                    (vec![p], b)
                },
                |_pf, _b| {
                    // No-op.  The conclusion for the zero case is the same as the last premise.
                },
            );
        },
        |pf, n| {
            pf.tactic_forall_intro(
                |vars| {
                    let n = n.shift();
                    let b = vars.fresh();
                    let p = mk_prop_reach(Term::add(n, 1.into()), b);
                    (vec![p], b)
                },
                |pf, b| {
                    let n = n.shift();
                    let n_plus_1 = Term::add(n, 1.into());
                    //pf.show_context();

                    let p_iter = pf.tactic_clone(p_iter);
                    let _p_first = pf.tactic_apply(p_iter, &[b, n_plus_1]);

                    pf.tactic_admit(Prop::Nonzero(Term::cmpa(1000.into(), n)));
                    let p_ind = pf.tactic_clone((1, 1));
                    let p_rest = pf.tactic_apply0(p_ind);

                    let expected_cycles =
                        Term::add(b, Term::add(Term::mull(n, 13.into()), 13.into()));
                    pf.tactic_admit(Prop::Nonzero(Term::cmpe(
                        Term::add(Term::add(b, 13.into()), Term::mull(n, 13.into())),
                        expected_cycles,
                    )));
                    let p_final = pf.tactic_apply(p_rest, &[Term::add(b, 13.into())]);
                    pf.tactic_reach_shrink(p_final, expected_cycles);
                },
            );
        },
    );
    //pf.show_context();


    // ----------------------------------------
    // Prove the full execution
    // ----------------------------------------

    eprintln!("\nprove p_exec");
    // `conc_state` is reachable.
    let p_conc = pf.tactic_admit(Prop::Reachable(ReachableProp {
        pred: Binder::new(|_vars| {
            StatePred {
                state: symbolic::State {
                    pc: conc_state.pc,
                    regs: conc_state.regs.map(|x| x.into()),
                    mem: MemState::Log(MemLog::new()),
		    conc_st: Some (conc_state.clone()),
                },
                props: Box::new([]),
            }
        }),
        min_cycles: conc_state.cycle.into(),
    }));

    // Modify `p_conc` to match the premise of `p_loop`.
    pf.tactic_reach_extend(p_conc, |rpf| {
        for r in 0 .. 33 {
            if r == 12 {
                // Pad out the variable numbering to align with p_loop.
                rpf.rule_var_fresh();
            } else {
                rpf.rule_forget_reg(r);
            }
        }
    });

    // Combine `p_conc` and `p_loop` to prove that the loop's final state is reachable.
    let p_loop_n = pf.tactic_apply(p_loop, &[conc_state.regs[12].into()]);
    pf.rule_trivial();
    let p_loop_n = pf.tactic_apply0(p_loop_n);
    let p_exec = pf.tactic_apply(p_loop_n, &[conc_state.cycle.into()]);


    println!("\nfinal theorem:\n{}", pf.print(&pf.props()[p_exec.1]));

    println!("ok");
    Ok(())
}

fn main() {
    env_logger::init();
    let args = env::args().collect::<Vec<_>>();
    assert_eq!(args.len(), 2, "must provide cbor path");
    import::with_globals(|| run(&args[1]).unwrap());
}

