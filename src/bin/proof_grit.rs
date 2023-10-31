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
use sym_proof::logic::{Term, Prop, Binder, VarCounter, StepProp, StatePred, VarId};
use sym_proof::logic::shift::ShiftExt;
use sym_proof::micro_ram::import;
use sym_proof::proof::Proof;
use sym_proof::symbolic::{self, MemState, MemLog};

fn run(path: &str) -> Result<(), String> {
    let exec = import::load_exec(path);

    let prog = import::convert_code(&exec);
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


    let _lemmas = Proof::prove(&prog, |pf| {
        // ----------------------------------------
        // Prove a single iteration
        // ----------------------------------------

        // We first prove a lemma of the form:
        //      forall n, n > 0 -> {r12 = n} ->* {r12 = n - 1}
        // The proof is done by running symbolic execution.
        eprintln!("\nprove l_iter");
        let l_iter = pf.rule_forall_intro(
            |vars| {
                // Set up the variables and premises.  There is only one variable, `n`, and only
                // one premise, `n > 0`.  The `Term` representing `n` will be passed through to the
                // proof callback.
                let n = vars.fresh();
                (vec![Prop::Nonzero(Term::cmpa(n.clone(), 0.into()))], n)
            },
            |pf, n| {
                // Prove the conclusion.
                //pf.show_context();

                // From the premise `n > 0`, we can derive `n != 0`, which is needed to show that
                // the jump is taken.
                //
                // We do this part early because the last lemma proved within this closure becomes
                // the conclusion of the `forall`.
                pf.rule_gt_ne_unsigned(n.clone(), 0.into())?;

                // Set up the initial state.
                let l = pf.rule_step_zero(|vars| {
                    // `rule_step_zero` introduces a binder (the existential built into the
                    // `StepProp`), so we need to shift `n` from the outer context to make it valid
                    // under the binder.
                    let n = n.shift();
                    StatePred {
                        state: symbolic::State {
                            pc: conc_state.pc,
                            regs: array::from_fn(|r| {
                                // We unconditionally allocate a var for each reg so that almost
                                // all registers will be set to the same-numbered var: `rN = xN`.
                                let v = vars.fresh();
                                match r {
                                    12 => n.clone(),
                                    _ => v,
                                }
                            }),
                            // Memory in the initial state is an empty `MemLog`, which implies that
                            // nothing is known about memory.
                            mem: MemState::Log(MemLog::new()),
                        },
                        props: vec![].into(),
                    }
                });

                pf.rule_step_extend(l, |spf| {
                    // Symbolic execution through one iteration of the loop.
                    spf.tactic_run();
                    spf.rule_step_jump(true)?;
                    spf.tactic_run();
                    spf.rule_step_load_fresh()?;
                    spf.tactic_run_until(conc_state.pc)?;

                    // Erase information about memory and certain registers to make it easier to
                    // sequence this `StepProp` with itself.
                    for &r in &[11, 13, 14, 15, 32] {
                        spf.rule_forget_reg(r);
                    }
                    spf.rule_forget_mem();
                    Ok(())
                })?;
                Ok(())
            },
        )?;

        // ----------------------------------------
        // Prove the full loop by induction
        // ----------------------------------------

        // Helper to build the initial state with the loop counter set to `n`:
        //      { r12 = n }
        let p_pre_state = |vars: &mut VarCounter, n: Term| {
            StatePred {
                state: symbolic::State {
                    pc: conc_state.pc,
                    regs: array::from_fn(|r| {
                        let v = vars.fresh();
                        match r {
                            12 => n.clone(),
                            _ => v,
                        }
                    }),
                    mem: MemState::Log(MemLog { l: Vec::new() }),
                },
                props: vec![].into(),
            }
        };
        // Helper to build the statement that running with the loop counter set to `n` runs for
        // `13*n` steps and reduces the counter to zero:
        //      { r12 = n } ->(13*n) { r12 = 0 }
        let p_step = |n: Term| {
            let pre = Binder::new(|vars| p_pre_state(vars, n.shift()));
            let mut post = pre.clone();
            post.inner.state.regs[12] = Term::const_(0);
            Prop::Step(StepProp {
                pre,
                post,
                min_cycles: Term::mull(n.clone(), 13.into()),
            })
        };
        // Helper to build the complete statement we're trying to prove:
        //      forall n, n < 1000 -> { r12 = n } ->(13*n) { r12 = 0 }
        let p = |n: Term| {
            Prop::Forall(Binder::new(|_| {
                let step = p_step(n.shift());
                (vec![Prop::Nonzero(Term::cmpa(1000.into(), n.shift()))].into(), Box::new(step))
            }))
        };

        // Premise that no overflow occurred: `n + 1 > 0`.  This is part of the inductive case
        // passed to `rule_induction`.
        let no_overflow = |n: Term| {
            Prop::Nonzero(Term::cmpa(Term::add(n, 1.into()), 0.into()))
        };

        // Prove the base case:
        //      (0 + 1 > 0) -> { r12 = 0 } ->(0) { r12 = 0 }
        //
        // The premise `0 + 1 > 0` normalizes to `1` (true), but it still needs to be present so
        // the lemma matches `p(0)` as expected by `rule_induction`.
        eprintln!("\nprove Hzero");
        let l_zero = pf.tactic_implies_intro(vec![no_overflow(0.into())], |pf| {
            pf.rule_step_zero(|vars| {
                p_pre_state(vars, 0.into())
            });
            Ok(())
        })?;

        // Prove the inductive case:
        //      forall n,
        //      n + 1 > 0 ->
        //      (n < 1000 -> { r12 = n } ->(13*n) { r12 = 0 }) ->
        //      (n + 1 < 1000 -> { r12 = n + 1 } ->(13*(n+1)) { r12 = 0 })
        //
        // Note: currently `Prop::Forall` doesn't get normalized in any way, so `a -> (b -> c)` (a
        // `Forall` with one premise, whose conclusion is a `Forall` with one premise) is not
        // considered equivalent to `a -> b -> c` (a `Forall` with two premises).
        eprintln!("\nprove Hsucc");
        let l_succ = pf.rule_forall_intro(
            |vars| {
                let n = vars.fresh();
                (vec![no_overflow(n.clone()), p(n.clone())], n)
            },
            |pf, n| {
                let lt_1000 = Prop::Nonzero(
                    Term::cmpa(1000.into(), Term::add(n.clone(), 1.into())));
                pf.tactic_implies_intro(vec![lt_1000], |pf| {
                    let n = n.shift();
                    // Currently, we don't have rules to prove this simple arithmetic fact:
                    //      0 < n + 1 < 1000 -> n < 1000
                    let l_imp = pf.admit(Prop::implies(vec![
                        Prop::Nonzero(Term::cmpa(1000.into(), Term::add(n.clone(), 1.into()))),
                        Prop::Nonzero(Term::cmpa(Term::add(n.clone(), 1.into()), 0.into())),
                    ].into(), Prop::Nonzero(Term::cmpa(1000.into(), n.clone()))));
                    pf.tactic_apply0(l_imp)?;

                    let l = pf.rule_shift(1, 1);
                    let l_n_iters = pf.tactic_apply0(l)?;

                    let l_iter = pf.rule_shift(0, l_iter);
                    let l_next_iter = pf.rule_apply(l_iter, &[Term::add(n.clone(), 1.into())])?;

                    //pf.show_context_verbose();
                    let witness: [_; 33] = array::from_fn(|i| match i {
                        11 => Term::var_unchecked(VarId::new(0, 34)),
                        13 => Term::var_unchecked(VarId::new(0, 35)),
                        14 => Term::var_unchecked(VarId::new(0, 36)),
                        15 => Term::var_unchecked(VarId::new(0, 37)),
                        32 => Term::var_unchecked(VarId::new(0, 38)),
                        _ => Term::var_unchecked(VarId::new(0, i as _)),
                    });
                    let _l_n_plus_one_iters = pf.rule_step_seq(l_next_iter, l_n_iters, &witness)?;

                    Ok(())
                })?;
                Ok(())
            },
        )?;

        eprintln!("\napply induction with {l_zero}, {l_succ}");
        let _l_iters = pf.rule_induction(l_zero, l_succ)?;

        eprintln!("\nfinal context:");
        pf.show_context();

        Ok(())
    })?;
    eprintln!("ok");

    Ok(())
}

fn main() {
    env_logger::init();
    let args = env::args().collect::<Vec<_>>();
    assert_eq!(args.len(), 2, "must provide cbor path");
    import::with_globals(|| run(&args[1]).unwrap());
}

