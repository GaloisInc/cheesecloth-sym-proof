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
use std::env;
use env_logger;
use log::trace;
use sym_proof::advice::{self, RecordingStreamTag};
use sym_proof::interp::Rule;
use sym_proof::kernel::Proof;
use sym_proof::logic::{Term, Prop, Binder, VarCounter, ReachableProp, StatePred};
use sym_proof::logic::shift::ShiftExt;
use sym_proof::micro_ram::Program;
use sym_proof::micro_ram::import;
use sym_proof::symbolic::{self, MemState, MemLog};
use sym_proof::tactics::{Tactics, ReachTactics};

fn run(path: &str) -> Result<(), String> {
    let exec = import::load_exec(path);

    let (instrs, chunks) = import::convert_code_split(&exec);
    let prog = Program::new(&instrs, &chunks);
    eprintln!("loaded code: {} instrs", prog.len());
    let init_state = import::convert_init_state(&exec);
    eprintln!("loaded memory: {} words", init_state.mem.len());
    trace!("initial regs = {:?}", init_state.regs);


    // ----------------------------------------
    // Run the concrete prefix
    // ----------------------------------------

    let mut conc_state = init_state;
    // Run to the start of the first `memcpy`.
    let memcpy_addr = exec.labels["memcpy#39"];
    while conc_state.pc != memcpy_addr {
        let instr = prog[conc_state.pc];
        conc_state.step(instr, None);
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
    //      forall b n, n > 0 -> R({r12 = n}, b) -> R({r12 = n - 1}, b + 13)
    // The proof is done by running symbolic execution.
    eprintln!("\nprove p_iter");
    let p_iter = pf.tactic_forall_intro(
        |vars| {
            // Set up the variables and premises.  There is only one variable, `n`, and only
            // one premise, `n > 0`.  The `Term` representing `n` will be passed through to the
            // proof callback.
            let b = vars.fresh();
            let n = vars.fresh();
            (vec![
                Prop::Nonzero(Term::cmpa(n.clone(), 0.into())),
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

            // From the premise `n > 0`, we can derive `n != 0`, which is needed to show that
            // the jump is taken.
            //
            // We do this part early because the last lemma proved within this closure becomes
            // the conclusion of the `forall`.
            // TODO: pf.rule_gt_ne_unsigned(n.clone(), 0.into())?;
            let p_ne = pf.tactic_admit(
                Prop::Nonzero(Term::cmpe(Term::cmpe(n.clone(), 0.into()), 0.into())));
            let (p_reach, p_ne) = pf.tactic_swap(p_reach, p_ne);
            let _ = p_ne;

            pf.tactic_reach_extend(p_reach, |rpf| {
                //rpf.show_context();
                //rpf.show_state();

                // Symbolic execution through one iteration of the loop.
                rpf.tactic_run();
                rpf.rule_step_jump(true);
                rpf.tactic_run();
                rpf.rule_step_load_fresh();
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
        let regs = array::from_fn(|r| {
            let v = vars.fresh();
            match r {
                12 => n,
                _ => v,
            }
        });
        StatePred {
            state: symbolic::State::new (
                conc_state.pc,
                regs,
                MemState::Log(MemLog { l: Vec::new().into() }),
                Some (conc_state.clone()),
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
                state: symbolic::State::new(
                    conc_state.pc,
                    conc_state.regs.map(|x| x.into()),
                    MemState::Log(MemLog::new()),
                    Some (conc_state.clone()),
                ),
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

    #[cfg(feature = "recording_rules")] {
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

