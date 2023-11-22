//! Proof that sqrt runs for at least ??? steps.  We first run the program concretely up to the
//! start of the loop (~??? steps), then we show that the loop will run for
//! at least ?? iterations (~?? steps).
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
    // LBB831_734#20819 (pc=253846) is near the loop, but slighly after the start.
    let loop_label = ".LBB831_734#20819"; //What about .LBB713_45#19734
    // The loop starts at pc = 253854;
    //]let loop_addr = 253854; //
    let loop_addr = exec.labels[loop_label];
    eprintln!("Starting concrete execution until address: {} ", loop_addr);
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

    
    // ----------------------------------------
    // Set up the proof state
    // ----------------------------------------
    
    let mut pf = Proof::new(prog);


    
    // ----------------------------------------
    // Build the minimal memory for the loop
    // ----------------------------------------
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
		// eprintln!("LOAD - {} : {} <- {} ", pc, addr, (conc_state.regs[instr.rd as usize]) );
            },
            Opcode::Store(w) => {
		let addr = conc_state.operand_value(instr.op2);
		//eprintln!("STORE - {} : {} <- {} ", pc, addr, (conc_state.regs[instr.r1 as usize]) );
            }
	    _ => ()
	}
    }
    
    let mut init_mem_map  = |i| {
	let mut init_mem_map0 = MemMap::new(u64::MAX);
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
    

    // ----------------------------------------
    // Define the state at the top of the loop
    // and it's reachability.
    // ----------------------------------------
    let st_loop = |vars: &mut VarCounter, i: Term| {
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
                mem: MemState::Map(init_mem_map(i).unwrap()),
		conc_st: Some (conc_state.clone()),
            },
            props: vec![].into(),
        }
    };

    // Helper to build the `Prop::Reachable` for a given `n` and cycle count `c`:
    //      reach(c, st_loop(i))
    let mk_prop_reach = |i: Term, c: Term| {
        Prop::Reachable(ReachableProp {
            pred: Binder::new(|vars| st_loop(vars, i.shift())),
            min_cycles: c,
        })
    };
    
    // ----------------------------------------
    // Prove a double iteration (twice around the loop)
    // ----------------------------------------

    // We first prove a lemma of the form:
    //      forall b n, i > 0 -> ???
    //                  R({r10 = i, concrete_regs}, b) -> R({r10 = i + 2, concrete_regs}, b + 5460)
    // The proof is done by running symbolic execution.
    eprintln!("\nprove p_iter");
    let p_iter = pf.tactic_forall_intro(
        |vars| {
            // Set up the variables and premises.  There is only one variable, `n`, and only
            // one premise, `n > 0`.  The `Term` representing `n` will be passed through to the
            // proof callback.
            let b = vars.fresh();
            //let forget_var = vars.fresh();
            let i = vars.fresh();

            (vec![
		// i > 0
                Prop::Nonzero(Term::cmpa(i.clone(), 1.into())),
		// MAX_unsigned > i+1
                Prop::Nonzero(Term::cmpa((u64::MAX).into(),Term::add(1.into(), i.clone()))),
		// reach(c, st_loop(i))
		mk_prop_reach(i, b.clone()),
            ], i)
        },
        |pf, i| {
            // The reachability is in the next context (1) and it is
            // the fourth prop (3)
            let p_reach = (1, 2);

	    // ((1 == a1) == 0)
	    let i_not_0 = pf.tactic_admit(
		Prop::Nonzero(Term::cmpe(Term::cmpe(1.into(), i.clone()), 0.into())));
	    // ((1 == (a1 + 1)) == 0)
	    let i1_not_0 = pf.tactic_admit(
		Prop::Nonzero(Term::cmpe(Term::cmpe(1.into(), Term::add(i.clone(), 1.into())), 0.into())));

            let (p_reach, i1_not_0) = pf.tactic_swap(p_reach, i1_not_0);
            // let _ = (p_ne,i1_not_0);

            pf.tactic_reach_extend(p_reach, |rpf| {
		
		rpf.show_state();

		// Define the proof for one single loop iteration.
		let mut one_loop_proof = |n:&mut u32| -> () {
		    eprintln!("{}. Concretely until the symbolic step. pc {}, cycle {:?}", n,
			      rpf.state().pc, rpf.state().conc_st.clone().map(|cst| cst.cycle));
		    rpf.tactic_run_concrete();
		    *n += 1;
		    
		    eprintln!("{}. Symbolic comparison symbolic step. pc {}, cycle {:?}", n,
			      rpf.state().pc, rpf.state().conc_st.clone().map(|cst| cst.cycle));
                    rpf.rule_step();
		    //rpf.show_state();
		    *n += 1;
		    
		    eprintln!("{}. Replace the symbolic comparison with concrete value.  (i==1) -> 0. pc {}, cycle {:?}", n,
			      rpf.state().pc, rpf.state().conc_st.clone().map(|cst| cst.cycle));
		    rpf.rule_rewrite_reg(32,Term::const_(0));
		    *n += 1;
		    
		    eprintln!("{}. Concretely until the symb. store. pc {}, cycle {:?}", n,
			      rpf.state().pc, rpf.state().conc_st.clone().map(|cst| cst.cycle));
                    rpf.tactic_run_concrete();
		    *n += 1;
		    
		    eprintln!("{}. Symbolic store the i, with the rule_step", n);
                    rpf.rule_step();
		    rpf.show_state();
		    *n += 1;
		    
                    eprintln!("{}. Concretely (long) until the increment of i. pc {}, cycle {:?}", n,
			      rpf.state().pc, rpf.state().conc_st.clone().map(|cst| cst.cycle));
                    rpf.tactic_run_concrete();
		    //rpf.show_state();
		    *n += 1;
		    
		    eprintln!("{}. Symbolic: increment the counter", n);
                    rpf.rule_step();
		    //rpf.show_state();
		    *n += 1;
		    
		    
		    eprintln!("{}. Concrete until the symbolic substraction. pc {}, cycle {:?}", n,
			      rpf.state().pc, rpf.state().conc_st.clone().map(|cst| cst.cycle));
		    rpf.tactic_run_concrete();
		    //rpf.show_state();
		    *n += 1;
		    
		    // Why is i first substracted and then stored?
		    eprintln!("{}. Symbolic substraction and store `sp <- (i-1)`, with the rule_step", n);
                    rpf.rule_step(); // 253801. %11 = %8 + -1
		    rpf.rule_step(); //253802. %32 = %ax + 88
		    rpf.rule_step(); // 253803.	*(%32) = %11
		    rpf.show_state();
		    *n += 1;
		    
		    
		    eprintln!("{}. Run until Beggining, wash and repeat", n);
		    rpf.tactic_run_until(loop_addr);
		    rpf.show_state();
		    *n += 1;
		};

		// Apply the proof to two loops.
		let steps_counter: &mut u32 = &mut 1;
		one_loop_proof(steps_counter);
		one_loop_proof(steps_counter);
		
                
                // Erase information about memory and certain registers to make it easier to
                // sequence this `StepProp` with itself.
                // for &r in &[11, 13, 14, 15, 32] {
                //     rpf.rule_forget_reg(r);
                // }
                // rpf.rule_forget_mem();

            });

            // // Rename variables so the final state uses the same names as the initial state.
            // pf.tactic_reach_rename_vars(p_reach, |vars| {
            //     let mut var_map = [None; 39];
            //     for i in 0 .. 33 {
            //         var_map[i] = Some(vars.fresh_var().index());
            //     }
            //     var_map[34] = var_map[11];
            //     var_map[35] = var_map[13];
            //     var_map[36] = var_map[14];
            //     var_map[37] = var_map[15];
            //     var_map[38] = var_map[32];
            //     var_map
            // });
        },
    );


    // ----------------------------------------
    // Prove the full loop by induction
    // ----------------------------------------

    // We are proving the following statement:
    //
    //      forall n,
    //          Max > 2n + 3 ->
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
    let max_loops = Term::sub(u64::MAX.into(),2.into());
    // Write i in terms of n (n increases, i decreases)
    let i_from_n = |n| (Term::sub(max_loops,Term::mull(2.into(), n)));
    
    eprintln!("\nprove p_loop");
    let p_loop = pf.tactic_induction(
        Prop::Forall(Binder::new(|vars| {
	    //      forall n,
            let n = vars.fresh();
	    //          Max > 2n + 1 ->
	    let p0 = Prop::Nonzero(Term::cmpa(u64::MAX.into(), Term::add(Term::mull(n, 2.into()), 1.into())));
            //          let i := Max - 2n in
	    let i:Term = i_from_n(n);
	    //          (i > 1) ->
	    let p1 = Prop::Nonzero(Term::cmpa(i, 1.into()));
            //          (Max > i + 1) ->
	    let p2 = Prop::Nonzero(Term::cmpa(u64::MAX.into(), Term::add(i,1.into())));
            let q = Prop::Forall(Binder::new(|vars| {
                let n = n.shift();
		let i:Term = i_from_n(n);
		//      forall b,
                let b = vars.fresh();
		//          reach(b, st_loop(i)) ->
                let p = mk_prop_reach(i, b);
		//          reach(b + n * 5460, st_loop(max))
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

		    
		    // println!("==== Context");
		    // pf.show_context();
		    // println!("==== END Context");
		    
                    let n = n.shift();
                    let n_plus_1 = Term::add(n, 1.into());

		    // Let i := max - 2n
		    let i = i_from_n(n);
		    // Let i+2 := max - 2n
		    let i_sub_2 = i_from_n(n_plus_1);
		    
		    // (Max >u 2n + 3) -> (i > 1)
		    println!("==== ADMIT: \n\t(Max >u 2n + 3) -> (i > 1)");
		    pf.show_prop((2,0));
		    let i_gt_1 = pf.tactic_admit(
			Prop::Nonzero(Term::cmpa(i, 1.into())));

		    
		    // n+1 > 0 ->
		    // Max > 2n+2 ->
		    // Max > (Max - 2 - 2n ) + 1
		    println!("==== ADMIT: \n\tn+1 > 0 ->\n\tMax > 2n+2 -> \n\tMax > (Max - 2 - 2n ) + 1");
		    pf.show_prop((1,0));
		    pf.show_prop((2,0));
		    let i1_no_over = pf.tactic_admit(
			Prop::Nonzero(Term::cmpa(u64::MAX.into(),
						 Term::add(Term::sub(max_loops, Term::mull(n,2.into())), 1.into()))));

		    println!("==== CLone P_iter");
		    let p_iter = pf.tactic_clone(p_iter);

		     
		    // println!("==== Context");
		    // pf.show_context();
		    // println!("==== END Context");
		    
		    println!("==== apply P_iter");
		    let _p_first = pf.tactic_apply(p_iter, &[b, i_sub_2]);
		    
		    
		    // (Max >u (2n + 3)) ->
		    // (Max >u (2n + 1))
		    println!("==== ADMIT: \n\t(Max >u (2n + 3)) ->\n\t(Max >u (2n + 1))");
		    pf.show_prop((2,0));
		    let IndHyp_H0 = pf.tactic_admit(
			Prop::Nonzero(Term::cmpa(u64::MAX.into(),
						 Term::add(Term::mull(n,2.into()), 1.into()))));

	
		    // println!("==== Context");
		    // pf.show_context();
		    // println!("==== END Context");

		    println!("==== apply induction hypothesis");
		    let p_ind = pf.tactic_clone((1, 1));
                    let p_rest = pf.tactic_apply0(p_ind);

		    
                    let expected_cycles =
			Term::add(b, Term::add(Term::mull(n, 5460.into()), 5460.into()));
                    pf.tactic_admit(Prop::Nonzero(Term::cmpe(
                        Term::add(Term::add(b, 5460.into()), Term::mull(n, 5460.into())),
                        expected_cycles,
                    )));

		    
		    // println!("==== Context");
		    // pf.show_context();
		    // println!("==== END Context");


		    // reach(b + 5460, st_loop(i_sub_2 + 2)) ->
		    // reach(b + 5460, st_loop(i)
		    println!("==== ADMIT: \n\treach(b + 5460, st_loop(i_sub_2 + 2)) ->\n\treach(b + 5460, st_loop(i)");
		    pf.show_prop((3,4));
		    let IndHyp_H0 = pf.tactic_admit(  mk_prop_reach(i, Term::add(b,5460.into())));

		    println!("==== apply induction hypothesis AGAIN");

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

    eprintln!("\nprove p_exec");
    // `conc_state` is reachable.
    let p_conc = pf.tactic_admit(Prop::Reachable(ReachableProp {
        pred: Binder::new(|_vars| {
            StatePred {
                state: symbolic::State {
                    pc: conc_state.pc,
                    regs: conc_state.regs.map(|x| x.into()),
                    mem: MemState::Map(init_mem_map(conc_state.regs[8].into()).unwrap()),
		    conc_st: Some (conc_state.clone()),
                },
                props: Box::new([]),
            }
        }),
        min_cycles: conc_state.cycle.into(),
    }));

    // println!("==== Context");
    // pf.show_context();
    // println!("==== END Context");

    // Modify `p_conc` to match the premise of `p_loop`.
    pf.tactic_reach_extend(p_conc, |rpf| {
        for r in 0 .. 33 {
            if r == 8 {
                // Pad out the variable numbering to align with p_loop.
                //rpf.rule_var_fresh();
            } else {
		// no op
            }
        }
    });

    

    // Combine `p_conc` and `p_loop` to prove that the loop's final state is reachable.
    println!("==== Apply p_loop 1");
    // Initial n value:
    let initial_n = {
	// current value of r8
	let r8_val = conc_state.regs[8];
	let diff = u64::MAX - r8_val - 2;
	if diff%2 != 0{
	    eprintln!("=== Error, Max-r[8] should be even, but r[8]={}, Max={}", r8_val, u64::MAX)
	}
	diff/2
    };
    println!("==== Initial n = {}", initial_n);
    let p_loop_n = pf.tactic_apply(p_loop, &[initial_n.into()]);
    pf.rule_trivial();
    println!("==== Apply p_loop 2");
    let p_loop_n = pf.tactic_apply0(p_loop_n);
    println!("==== Apply p_loop_n");
    
    // println!("==== Context");
    // pf.show_context();
    // println!("==== END Context");
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

