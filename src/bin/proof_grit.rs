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
use std::collections::HashMap;
use std::env;
use env_logger;
use log::trace;
use sym_proof::Word;
use sym_proof::logic::{Term, Prop, Binder, VarCounter, StepProp, StatePred, VarId, SubstTable};
use sym_proof::micro_ram::NUM_REGS;
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


    let lemmas = Proof::prove(&prog, |pf| {
        // Prove a single iteration
        let l_iter = pf.rule_forall_intro(
            |vars| {
                let n = vars.fresh();
                (vec![Prop::Nonzero(Term::cmpa(n.clone(), 0.into()))], n)
            },
            |pf, n| {
                // `n != 0` is needed to show that the jump is taken.
                pf.rule_gt_ne_unsigned(n.clone(), 0.into())?;
                let l = pf.rule_step_zero(|vars| {
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
                        props: vec![],
                    }
                });
                pf.rule_step_extend(l, |spf| {
                    spf.rule_step()?;
                    spf.rule_step_jump(true)?;
                    spf.rule_step()?;
                    spf.rule_step_load_fresh()?;
                    for _ in 0 .. 9 {
                        spf.rule_step()?;
                    }

                    for &r in &[11, 13, 14, 15, 32] {
                        spf.rule_forget_reg(r);
                    }
                    Ok(())
                })?;
                Ok(())
            },
        )?;

        // Prove that N steps can be extended into N+1 steps (inductive case)
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
                props: vec![],
            }
        };
        let p_step = |n: Term| {
            let pre = Binder::new(5, |vars| p_pre_state(vars, n.clone()));
            let mut post = pre.clone();
            post.inner.state.regs[12] = Term::const_(0);
            Prop::Step(StepProp {
                pre,
                post,
                min_cycles: Term::mull(n.clone(), 13.into()),
            })
        };
        let p = |n: Term| {
            let step = p_step(n.clone());
            Prop::Forall(Binder::new(6, |_| {
                (vec![Prop::Nonzero(Term::cmpa(1000.into(), n.clone()))], Box::new(step))
            }))
        };

        let no_overflow = |n: Term| {
            Prop::Nonzero(Term::cmpa(Term::add(n, 1.into()), 0.into()))
        };
        let l_zero = pf.tactic_implies_intro(vec![no_overflow(0.into())], |pf| {
            pf.rule_step_zero(|vars| {
                p_pre_state(vars, 0.into())
            });
            Ok(())
        })?;

        let l_succ = pf.rule_forall_intro(
            |vars| {
                let n = vars.fresh();
                (vec![no_overflow(n.clone()), p(n.clone())], n)
            },
            |pf, n| {
                let lt_1000 = Prop::Nonzero(
                    Term::cmpa(1000.into(), Term::add(n.clone(), 1.into())));
                pf.tactic_implies_intro(vec![lt_1000], |pf| {
                    let l_imp = pf.admit(Prop::implies(vec![
                        Prop::Nonzero(Term::cmpa(1000.into(), Term::add(n.clone(), 1.into()))),
                        Prop::Nonzero(Term::cmpa(Term::add(n.clone(), 1.into()), 0.into())),
                    ], Prop::Nonzero(Term::cmpa(1000.into(), n.clone()))));
                    pf.tactic_apply0(2, l_imp)?;

                    let l_n_iters = pf.tactic_apply0(1, 1)?;
                    let l_next_iter = pf.rule_apply(0, l_iter, &mut SubstTable::new(|v| {
                        // FIXME
                        if v == VarId::new(1, 0) {
                            Term::add(n.clone(), 1.into())
                        } else {
                            Term::var_unchecked(v)
                        }
                    }))?;

                    let l_n_plus_one_iters = pf.admit(p_step(Term::add(n.clone(), 1.into())));
                    Ok(())
                })?;
                Ok(())
            },
        )?;

        let l_iters = pf.rule_induction(0, l_zero, 0, l_succ)?;

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

