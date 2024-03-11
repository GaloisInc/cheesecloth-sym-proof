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
#![cfg_attr(feature = "deny_warnings", deny(warnings))]
use core::array;
use std::collections::{HashMap, HashSet};
use std::env;
use env_logger;
use log::trace;
use sym_proof::Addr;
use sym_proof::advice;
use sym_proof::kernel::Proof;
use sym_proof::logic::{Term, Prop, Binder, VarCounter, ReachableProp, StatePred};
use sym_proof::logic::shift::ShiftExt;
use sym_proof::micro_ram::{Program, MemWidth};
use sym_proof::micro_ram::import;
use sym_proof::symbolic::{self, MemState, MemSnapshot, MemLog};
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

    // ----------------------------------------
    // Load advice
    // ----------------------------------------

    eprintln!("=== Load advice");
    let mut advise_values = HashMap::<u64, u64>::new();
    let mut stutters = HashSet::<u64>::new();
    // Iterate through all the advices (i.e. MemOps, Stutter, Advice)
    // and only keep the `Advice` ones.
    for (&step_index, advice_vec) in exec.advice.iter() {
        for advice in advice_vec {
            match *advice {
                Advice::Advise { advise } => {
                    advise_values.insert(step_index, advise);
                },
                Advice::Stutter => {
                    stutters.insert(step_index);
                },
                _ => {},
            }
        }
    }

    // ----------------------------------------
    // Run the concrete prefix
    // ----------------------------------------

    let mut conc_state = init_state;
    let mut step_index = 0;
    // Run to the start of the first `memcpy`.
    let loop_label = exec.labels.keys().find(|s| s.starts_with(".LBB1_5#")).unwrap();
    let loop_addr = exec.labels[loop_label];

    eprintln!("=== Concrete execution until pc={} ", loop_addr);
    while conc_state.pc != loop_addr {
        // Increment early.  The first step's advice is at index 1, not 0.
        step_index += 1;
        if stutters.contains(&step_index) {
            continue;
        }
        let conc_pc : Addr = conc_state.pc;
        let instr = prog[conc_pc];
        let adv: Option<u64> = advise_values.get(&step_index).copied();
        //eprintln!("step: {:?}, {:?}", instr, adv);
        conc_state.step(instr, adv);
        //eprintln!("stepped: pc = {}, cyc = {}", conc_state.pc, conc_state.cycle);
    }
    eprintln!("\tConcretely reached {} in {} cycle.", conc_state.pc, conc_state.cycle);

    eprintln!("concrete registers:");
    for (i, &x) in conc_state.regs.iter().enumerate() {
        eprintln!("{:2}: 0x{:x}", i, x);
    }

    // Record the concrete state so we don't need to rerun the concrete prefix in later stages.
    #[cfg(feature = "recording_concrete_state")] {
        use std::fs::{self, File};
        let dir = advice::advice_dir();
        fs::create_dir_all(&dir)
            .map_err(|e| e.to_string())?;
        let mut f = File::create(dir.join("concrete_state.cbor"))
            .map_err(|e| e.to_string())?;
        serde_cbor::to_writer(f, &conc_state)
            .map_err(|e| e.to_string())?;
    }


    // ----------------------------------------
    // Set up the proof state
    // ----------------------------------------
    let mut pf = Proof::new(prog);

    MemSnapshot::init_data(conc_state.mem.clone());

    // ----------------------------------------
    // Admit some arithmetic lemmas
    // ----------------------------------------

    // Z3 prologue:
    // (declare-const a (_ BitVec 64))
    // (declare-const b (_ BitVec 64))
    // (declare-const c (_ BitVec 64))
    // (declare-const d (_ BitVec 64))
    // (declare-const n (_ BitVec 64))
    // (declare-const m (_ BitVec 64))

    // Z3 epilogue:
    // (check-sat)
    // (get-model)

    // To check each lemma, append the Z3 prologue, the SMTlib code for the lemma, and the Z3
    // epilogue.  It should report `unsat`.

    println!("==== ADMIT: forall n, n > 1  ->  (n - 1) != 0");
    // (assert (bvugt n (_ bv1 64)))
    // (assert (not (not (= (bvsub n (_ bv1 64)) (_ bv0 64)))))
    let arith_n_minus_1_ne_0 = advice::dont_record(|| {
        pf.tactic_admit(Prop::Forall(Binder::new(|vars| {
            let n = vars.fresh();
            // n > 1
            let n_limit = Prop::Nonzero(Term::cmpa(n, 1.into()));
            // (n - 1) != 0
            let n_minus_1 = Term::sub(n, 1.into());
            let concl = Prop::Nonzero(Term::cmpe(Term::cmpe(n_minus_1, 0.into()), 0.into()));
            (vec![n_limit].into(), Box::new(concl))
        })))
    });

    println!("==== ADMIT: forall n, n > 0  ->  n < 1000  ->  n + 1 > 1");
    // (assert (bvugt n (_ bv0 64)))
    // (assert (bvugt (_ bv1000 64) n))
    // (assert (not (bvugt (bvadd n (_ bv1 64)) (_ bv1 64))))
    let arith_n_plus_1_gt_1 = advice::dont_record(|| {
        pf.tactic_admit(Prop::Forall(Binder::new(|vars| {
            let n = vars.fresh();
            // n > 0
            let n_lo = Prop::Nonzero(Term::cmpa(n, 0.into()));
            // n < 1000
            let n_hi = Prop::Nonzero(Term::cmpa(1000.into(), n));
            // n + 1 > 1
            let concl = Prop::Nonzero(Term::cmpa(Term::add(n, 1.into()), 1.into()));
            (vec![n_lo, n_hi].into(), Box::new(concl))
        })))
    });

    println!("==== ADMIT: forall n, n > 0  ->  n < 1000  ->  n - 1 < 1000");
    // (assert (bvugt n (_ bv0 64)))
    // (assert (bvugt (_ bv1000 64) n))
    // (assert (not (bvugt (_ bv1000 64) (bvsub n (_ bv1 64)))))
    let arith_n_minus_1_lt_1000 = advice::dont_record(|| {
        pf.tactic_admit(Prop::Forall(Binder::new(|vars| {
            let n = vars.fresh();
            // n > 0
            let n_lo = Prop::Nonzero(Term::cmpa(n, 0.into()));
            // n < 1000
            let n_hi = Prop::Nonzero(Term::cmpa(1000.into(), n));
            // n + 1 > 1
            let concl = Prop::Nonzero(Term::cmpa(1000.into(), Term::sub(n, 1.into())));
            (vec![n_lo, n_hi].into(), Box::new(concl))
        })))
    });

    println!("==== ADMIT: forall a b c, (a + b) + c == a + (b + c)");
    // (assert (not (= (bvadd (bvadd a b) c) (bvadd a (bvadd b c)))))
    let arith_add_assoc = advice::dont_record(|| {
        pf.tactic_admit(Prop::Forall(Binder::new(|vars| {
            let a = vars.fresh();
            let b = vars.fresh();
            let c = vars.fresh();
            let l = Term::add(Term::add(a, b), c);
            let r = Term::add(a, Term::add(b, c));
            let concl = Prop::Nonzero(Term::cmpe(l, r));
            (vec![].into(), Box::new(concl))
        })))
    });


    // Admit that `conc_state` is reachable.
    //
    // We don't record this rule application since it's public, and the code is duplicated
    // explicitly in `interp_grit`.
    let p_conc = advice::dont_record(|| {
        pf.tactic_admit(Prop::Reachable(ReachableProp {
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
        }))
    });


    // ----------------------------------------
    // START OF SECRET PROOF
    // ----------------------------------------

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

        // For testing purposes, apply a `mem_abs` rule that actually reads from the concrete
        // state's memory.
        rpf.rule_mem_abs_map(&[(8, MemWidth::WORD)]);
        rpf.rule_mem_abs_log(&[]);
    });


    // ----------------------------------------
    // Prove a single iteration
    // ----------------------------------------

    // We first prove a lemma of the form:
    //      forall b n, n > 1 -> R({r12 = n}, b) -> R({r12 = n - 1}, b + 13)
    // The proof is done by running symbolic execution.
    eprintln!("\nprove p_iter");
    let p_iter = pf.tactic_forall_intro(
        |vars| {
            // Set up the variables and premises.  There is only one variable, `n`, and only
            // one premise, `n > 1`.  The `Term` representing `n` will be passed through to the
            // proof callback.
            let b = vars.fresh();
            let n = vars.fresh();
            (vec![
                Prop::Nonzero(Term::cmpa(n.clone(), 1.into())),
                Prop::Reachable(ReachableProp {
                    pred: Binder::new(|vars| {
                        let n = n.shift();
                        let regs = array::from_fn(|r| {
                            // We unconditionally allocate a var for each reg so that
                            // almost all registers will be set to the same-numbered var:
                            // `rN = xN`.
                            let v = vars.fresh();
                            match r {
                                12 => n.clone(),
                                _ => v,
                            }
                        });
                        StatePred {
                            state: symbolic::State::new (
                                conc_state.pc,
                                regs,
                                // Memory in the initial state is an empty `MemLog`, which implies
                                // that nothing is known about memory.
                                MemState::Log(MemLog::new()),
                                Some (conc_state.clone()),
                            ),
                            props: vec![].into(),
                        }
                    }),
                    min_cycles: b.clone(),
                }),
            ], n)
        },
        |pf, n| {
            // Prove the conclusion.
            //pf.show_context();
            let p_reach = (1, 1);

            // From the premise `n > 1`, we can derive `n - 1 != 0`, which is needed to show that
            // the jump is taken.
            //
            // We do this part early because the last lemma proved within this closure becomes
            // the conclusion of the `forall`.
            let arith_n_minus_1_ne_0 = pf.tactic_clone(arith_n_minus_1_ne_0);
            let p_ne = pf.tactic_apply(arith_n_minus_1_ne_0, &[n]);
            let (p_reach, p_ne) = pf.tactic_swap(p_reach, p_ne);
            let _ = p_ne;

            pf.tactic_reach_extend(p_reach, |rpf| {
                //rpf.show_context();
                //rpf.show_state();

                // Symbolic execution through one iteration of the loop.
                rpf.tactic_run();
                rpf.rule_step_load_fresh();
                rpf.tactic_run();
                rpf.show_context();
                rpf.show_state();
                rpf.rule_step_jump(true);
                rpf.tactic_run_until(conc_state.pc);

                // Erase information about memory and certain registers to make it easier to
                // sequence this `StepProp` with itself.
                for &r in &[11, 13, 14, 15, 32] {
                    rpf.rule_forget_reg(r);
                }
                rpf.rule_mem_abs_log(&[]);

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
    //              reach(b, {r12 = n + 1}) ->
    //              reach(b + n * 13, {r12 = 1})
    //
    // We separate the binders for `b` and `n` because `tactic_induction` expects to see only a
    // single bound variable (`n`) in `Hsucc`.

    // Helper to build a `StatePred` with the loop counter set to `n`:
    //      { r12 = n }
    let mk_state_pred = |vars: &mut VarCounter, n: Term| {
        let regs = array::from_fn(|r| {
            let v = vars.fresh();
            match r {
                12 => n,
                _ => v,
            }
        });
        StatePred {
            state: symbolic::State::new(
                conc_state.pc,
                regs,
                MemState::Log(MemLog::new()),
                Some(conc_state.clone()),
            ),
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
            //let p1 = Prop::Nonzero(Term::cmpa(n, 1.into()));
            let p2 = Prop::Nonzero(Term::cmpa(1000.into(), n));
            let q = Prop::Forall(Binder::new(|vars| {
                let n = n.shift();
                let b = vars.fresh();
                let p = mk_prop_reach(Term::add(n, 1.into()), b);
                let q = mk_prop_reach(1.into(), Term::add(b, Term::mull(n, 13.into())));
                (vec![p].into(), Box::new(q))
            }));
            (vec![p2].into(), Box::new(q))
        })),
        |pf| {
            //pf.show_context();
            pf.tactic_forall_intro(
                |vars| {
                    let b = vars.fresh();
                    let p = mk_prop_reach(1.into(), b);
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
                    let p = mk_prop_reach(Term::add(n, 2.into()), b);
                    (vec![p], b)
                },
                |pf, b| {
                    let n = n.shift();
                    let n_plus_1 = Term::add(n, 1.into());
                    let n_plus_2 = Term::add(n, 2.into());

                    let arith_n_plus_1_gt_1 = pf.tactic_clone(arith_n_plus_1_gt_1);
                    let p_n_plus_2_gt_1 = pf.tactic_apply(arith_n_plus_1_gt_1,
                        &[Term::add(n, 1.into())]);

                    let p_iter = pf.tactic_clone(p_iter);
                    let _p_first = pf.tactic_apply(p_iter, &[b, n_plus_2]);

                    let arith_n_minus_1_lt_1000 = pf.tactic_clone(arith_n_minus_1_lt_1000);
                    pf.tactic_apply(arith_n_minus_1_lt_1000,
                        &[Term::add(n, 1.into())]);

                    let p_ind = pf.tactic_clone((1, 1));
                    let p_rest = pf.tactic_apply0(p_ind);


                    let expected_cycles =
                        Term::add(b, Term::add(Term::mull(n, 13.into()), 13.into()));
                    let arith_add_assoc = pf.tactic_clone(arith_add_assoc);
                    pf.tactic_apply(arith_add_assoc, &[b, 13.into(), Term::mull(n, 13.into())]);

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

    // Combine `p_conc` and `p_loop` to prove that the loop's final state is reachable.
    let p_loop_n = pf.tactic_apply(p_loop, &[(conc_state.regs[12] - 1).into()]);
    pf.rule_trivial();
    let p_loop_n = pf.tactic_apply0(p_loop_n);
    let p_exec = pf.tactic_apply(p_loop_n, &[conc_state.cycle.into()]);


    println!("\nfinal theorem:\n{}", pf.print(&pf.props()[p_exec.1]));

    println!("ok");

    #[cfg(feature = "recording_rules")] {
        use sym_proof::advice::RecordingStreamTag;
        use sym_proof::interp::Rule;
        advice::recording::rules::Tag.record(&Rule::Done);
    }
    advice::finish()?;

    Ok(())
}

fn main() {
    env_logger::init();
    let args = env::args().collect::<Vec<_>>();
    assert_eq!(args.len(), 2, "must provide cbor path");
    import::with_globals(|| run(&args[1]).unwrap());
}

