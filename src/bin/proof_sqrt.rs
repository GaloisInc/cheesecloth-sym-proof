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
#![cfg_attr(feature = "deny_warnings", deny(warnings))]
use core::array;
use std::collections::{HashMap, HashSet};
use std::env;
use env_logger;
use log::trace;
use sym_proof::Addr;
use sym_proof::advice;
use sym_proof::kernel::Proof;
use sym_proof::logic::{Term, Prop, Binder, ReachableProp, StatePred};
use sym_proof::logic::shift::ShiftExt;
use sym_proof::micro_ram::{Program, NUM_REGS};
use sym_proof::micro_ram::import;
use sym_proof::micro_ram::Opcode;
use sym_proof::symbolic::{self, MemState, MemSnapshot};
use sym_proof::tactics::{Tactics, ReachTactics};
use witness_checker::micro_ram::types::Advice;

const I_MAX: u64 = 4_000_000_000;
const N_MAX: u64 = I_MAX / 2;

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
    let loop_label = exec.labels.keys().find(|s| s.starts_with(".LBB829_731#")).unwrap();
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

    // ----------------------------------------
    // Identify live memory
    // ----------------------------------------

    /// Run this many iterations concretely before switching to symbolic execution.  This must
    /// be enough iterations to get the state of registers and memory to stabilize.
    ///
    /// When running MicroRAM, this number should be used as the count for `--spontaneous-jump`.
    const NUM_CONCRETE_ITERS: usize = 1;

    let live_addrs = {
        let outer_conc_state = &mut conc_state;
        let outer_step_index = &mut step_index;

        // Create a copy of the state that we can freely modify.
        let mut conc_state = outer_conc_state.clone();
        let mut step_index = *outer_step_index;

        let mut live_addrs = Vec::new();
        // A set for deduplicating `live_addrs` entries.
        let mut live_addrs_set = HashSet::new();
        // Bytes that have been written, making them no longer live-in.
        let mut written_bytes = HashSet::new();

        for i in 0 .. 4 {
            let old_live_addrs = live_addrs.clone();
            let old_live_mem = old_live_addrs.iter()
                .map(|&(addr, w)| conc_state.mem_load(w, addr))
                .collect::<Vec<_>>();

            if i == NUM_CONCRETE_ITERS {
                *outer_conc_state = conc_state.clone();
                *outer_step_index = step_index;
            }

            // Run one iteration of the loop.
            loop {
                step_index += 1;
                if stutters.contains(&step_index) {
                    continue;
                }
                let instr = prog[conc_state.pc];
                let adv: Option<u64> = advise_values.get(&step_index).copied();

                match instr.opcode {
                    Opcode::Load(w) => {
                        let addr = conc_state.operand_value(instr.op2);
                        let all_written = (0 .. w.bytes()).all(|b| {
                            written_bytes.contains(&(addr + b))
                        });
                        if !all_written {
                            if live_addrs_set.insert((addr, w)) {
                                eprintln!("live_addrs: read {:x} ({:?}) at pc = {}",
                                    addr, w, conc_state.pc);
                                live_addrs.push((addr, w));
                            }
                        }
                    },
                    Opcode::Store(w) => {
                        let addr = conc_state.operand_value(instr.op2);
                        for b in 0 .. w.bytes() {
                            written_bytes.insert(addr + b);
                        }
                    },
                    _ => ()
                }

                conc_state.step(instr, adv);

                if conc_state.pc == loop_addr {
                    break;
                }
            }

            if live_addrs != old_live_addrs {
                eprintln!("iteration {}: live addrs changed", i);
            } else {
                let live_mem = live_addrs.iter()
                    .map(|&(addr, w)| conc_state.mem_load(w, addr))
                    .collect::<Vec<_>>();
                if live_mem != old_live_mem {
                    eprintln!("iteration {}: memory changed:", i);
                    let iter = live_addrs.iter().zip(
                        old_live_mem.iter().zip(live_mem.iter()));
                    for (&(addr, w), (&val1, &val2)) in iter {
                        if val1 != val2 {
                            eprintln!("  {:x},{:?}: {:x} -> {:x}", addr, w, val1, val2);
                        }
                    }
                }
            }
        }

        live_addrs
    };

    eprintln!("initial concrete state:");
    eprintln!("  pc = {}", conc_state.pc);
    eprintln!("  cycle = {}", conc_state.cycle);
    for r in 0 .. NUM_REGS {
        eprintln!("  regs[{}] = {}", r, conc_state.regs[r]);
    }

    eprintln!("live_addrs size: {}", live_addrs.len());

    // Record the concrete state so we don't need to rerun the concrete prefix in later stages.
    #[cfg(feature = "recording_concrete_state")] {
        use std::fs::{self, File};
        fs::create_dir_all("advice")
            .map_err(|e| e.to_string())?;
        let mut f = File::create("advice/concrete_state.cbor")
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

    println!("==== ADMIT: forall n a, n < N_MAX  ->  1 < a  ->  a < 10  ->  2n + a != 1");
    // (assert (bvugt (_ bv2000000000 64) n))
    // (assert (bvugt a (_ bv1 64)))
    // (assert (bvugt (_ bv10 64) a))
    // (assert (not (not (= (bvadd (bvmul (_ bv2 64) n) a) (_ bv1 64)))))
    let arith_2n_plus_k_ne_1 = advice::dont_record(|| {
        pf.tactic_admit(Prop::Forall(Binder::new(|vars| {
            let n = vars.fresh();
            let a = vars.fresh();
            // n < N_MAX
            let n_limit = Prop::Nonzero(Term::cmpa(N_MAX.into(), n));
            // 1 < a
            let a_min = Prop::Nonzero(Term::cmpa(a, 1.into()));
            // a < 10
            let a_max = Prop::Nonzero(Term::cmpa(10.into(), a));
            // (2 * n + a == 1) == 0
            let a = Term::add(Term::mull(2.into(), n), a);
            let eq = Term::cmpe(1.into(), a);
            let ne = Prop::Nonzero(Term::cmpe(eq, 0.into()));
            (vec![n_limit, a_min, a_max].into(), Box::new(ne))
        })))
    });

    println!("==== ADMIT: forall a b, 0 < a  ->  a < b  ->  a - 1 < b");
    // (assert (bvugt a (_ bv0 64)))
    // (assert (bvugt b a))
    // (assert (not (bvugt b (bvsub a (_ bv1 64)))))
    let arith_lt_sub_1 = advice::dont_record(|| {
        pf.tactic_admit(Prop::Forall(Binder::new(|vars| {
            let a = vars.fresh();
            let b = vars.fresh();
            // 0 < a
            let low = Prop::Nonzero(Term::cmpa(a, 0.into()));
            // a < b
            let high = Prop::Nonzero(Term::cmpa(b, a));
            // a - 1 < b
            let concl = Prop::Nonzero(Term::cmpa(b, Term::sub(a, 1.into())));
            (vec![low, high].into(), Box::new(concl))
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

    println!("==== ADMIT: forall n a, n < N_MAX  ->  a < 10  ->  2n + a < 2^32");
    // (assert (bvugt (_ bv2000000000 64) n))
    // (assert (bvugt (_ bv10 64) a))
    // (assert (not (bvugt #x0000000100000000 (bvadd (bvmul (_ bv2 64) n) a))))
    let arith_2n_plus_k_32bit = advice::dont_record(|| {
        pf.tactic_admit(Prop::Forall(Binder::new(|vars| {
            let n = vars.fresh();
            let a = vars.fresh();
            // n < N_MAX
            let n_limit = Prop::Nonzero(Term::cmpa(N_MAX.into(), n));
            // a < 10
            let a_limit = Prop::Nonzero(Term::cmpa(10.into(), a));
            let l = Term::add(Term::mull(2.into(), n), a);
            let concl = Prop::Nonzero(Term::cmpa((1 << 32).into(), l));
            (vec![n_limit, a_limit].into(), Box::new(concl))
        })))
    });

    println!("==== ADMIT: forall a, a < 2^32  ->  (a & 0xffffffff) == a");
    // (assert (bvugt #x0000000100000000 a))
    // (assert (not (= (bvand a #x00000000ffffffff) a)))
    let arith_32bit_mask = advice::dont_record(|| {
        pf.tactic_admit(Prop::Forall(Binder::new(|vars| {
            let a = vars.fresh();
            // a < 2^32
            let a_limit = Prop::Nonzero(Term::cmpa((1 << 32).into(), a));
            let l = Term::and(a, 0xffff_ffff.into());
            let r = a;
            let concl = Prop::Nonzero(Term::cmpe(l, r));
            (vec![a_limit].into(), Box::new(concl))
        })))
    });

    println!("==== ADMIT: forall a, a < 2^32  ->  a != 1  ->  (a >> 31) * 0x100000000 | a != 1");
    // (assert (bvugt #x0000000100000000 a))
    // (assert (not (= a (_ bv1 64))))
    // (assert (not (not (= (bvor (bvmul (bvlshr a (_ bv31 64)) #xffffffff00000000)) (_ bv1 64)))))
    let arith_sign_extend_ne_1 = advice::dont_record(|| {
        pf.tactic_admit(Prop::Forall(Binder::new(|vars| {
            let a = vars.fresh();
            // a < 2^32
            let a_limit = Prop::Nonzero(Term::cmpa((1 << 32).into(), a));
            // a != 1
            let a_ne_1 = Prop::Nonzero(Term::cmpe(Term::cmpe(1.into(), a), 0.into()));
            let l1 = Term::mull(Term::shr(a, 31.into()), 0xffff_ffff_0000_0000.into());
            let l = Term::or(l1, a);
            let concl = Prop::Nonzero(Term::cmpe(Term::cmpe(l, 1.into()), 0.into()));
            (vec![a_limit, a_ne_1].into(), Box::new(concl))
        })))
    });


    // ----------------------------------------
    // Concrete state is reachable
    // ----------------------------------------

    // `conc_state` is reachable.
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
        rpf.rule_mem_abs_map(&live_addrs);
    });

    let init_mem_concrete = {
        match pf.props()[p_conc.1] {
            Prop::Reachable(ref rp) => {
                rp.pred.inner.state.mem.clone()
            },
            _ => unreachable!(),
        }
    };

    let init_mem_symbolic = |_i| {
        let m = init_mem_concrete.clone();
        //let i_minus_1 = Term::sub(i, 1.into());
        // One address has the index
        //m.store(MemWidth::W8, Term::const_(0x7ffff468), i_minus_1, &[]).unwrap();
        // One address has garbage (Really it's the index)
        //m.store(MemWidth::W8, Term::const_(0x7ffff4d0), i_minus_1, &[]).unwrap();
        m
    };

    // Helper to build the symbolic `StatePred` for the top of the loop.
    let st_loop = |i: Term| {
        StatePred {
            state: symbolic::State {
                // current pc should be the address of the loop
                pc: conc_state.pc,
                // We keep all concrete registers, except for the
                // index i in register 9.
                regs: array::from_fn(|r| {
                    match r {
                        9 => i,
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
            pred: Binder::new(|_vars| st_loop(i.shift())),
            min_cycles: c,
        })
    };

    // ----------------------------------------
    // Prove a double iteration (twice around the loop)
    // ----------------------------------------

    let start_i = NUM_CONCRETE_ITERS as u64 + 1;

    // We first prove a lemma of the form:
    //      forall b n,
    //          n < N_MAX ->
    //          reach(b, st_loop(2n + start_i)) ->
    //          reach(b + 5426, st_loop(2(n+1) + start_i))
    eprintln!("\n# Prove p_iter");
    let p_iter = pf.tactic_forall_intro(
        |vars| {
            // forall b n, 
            let b = vars.fresh();
            let n = vars.fresh();
            let i = Term::add(Term::mull(2.into(), n), start_i.into());
            (vec![
                // n < N_MAX ->
                Prop::Nonzero(Term::cmpa(N_MAX.into(), n)),
                // reach(b, st_loop(2n + start_i)) -> 
                mk_prop_reach(i, b.clone()),
            ], n)
        },
        |pf, n| {
            // Premises:
            // n < N_MAX
            // reach(b, st_loop(2n + start_i))
            let p_reach = (1, 1);

            pf.rule_trivial();

            // Note: these lemmas must be adjusted when changing `start_i`.

            // Note: i = 2 * n + start_i

            let term_i_plus_1 = Term::add(Term::mull(n, 2.into()), (start_i + 1).into());
            let term_i_plus_2 = Term::add(Term::mull(n, 2.into()), (start_i + 2).into());

            let arith_2n_plus_k_ne_1 = pf.tactic_clone(arith_2n_plus_k_ne_1);
            let _i_plus_1_ne_1 = pf.tactic_apply(arith_2n_plus_k_ne_1, &[n, (start_i + 1).into()]);
            let _i_plus_2_ne_1 = pf.tactic_apply(arith_2n_plus_k_ne_1, &[n, (start_i + 2).into()]);

            let arith_2n_plus_k_32bit = pf.tactic_clone(arith_2n_plus_k_32bit);
            let _i_plus_1_32bit =
                pf.tactic_apply(arith_2n_plus_k_32bit, &[n, (start_i + 1).into()]);
            let _i_plus_2_32bit =
                pf.tactic_apply(arith_2n_plus_k_32bit, &[n, (start_i + 2).into()]);

            let arith_sign_extend_ne_1 = pf.tactic_clone(arith_sign_extend_ne_1);
            let _arith_sign_extend_i_plus_1_ne_1 =
                pf.tactic_apply(arith_sign_extend_ne_1, &[term_i_plus_1]);
            let _arith_sign_extend_i_plus_2_ne_1 =
                pf.tactic_apply(arith_sign_extend_ne_1, &[term_i_plus_2]);

            let arith_32bit_mask = pf.tactic_clone(arith_32bit_mask);
            let _i_plus_1_32bit_mask = pf.tactic_apply(arith_32bit_mask, &[term_i_plus_1]);
            let _i_plus_2_32bit_mask = pf.tactic_apply(arith_32bit_mask, &[term_i_plus_2]);

            let _last = _i_plus_2_32bit_mask;

            // Extend `p_reach` with two iterations worth of steps.
            let (p_reach, _) = pf.tactic_swap(p_reach, _last);
            pf.tactic_reach_extend(p_reach, |rpf| {
                let term_i_plus_1 = term_i_plus_1.shift();
                let term_i_plus_2 = term_i_plus_2.shift();
                // rpf.show_state();

                let mut stage_counter = 1;
                let mut print_stage = move |msg: &str| {
                    eprintln!("\t=== {}. {}", stage_counter, msg);
                    stage_counter += 1;
                };

                // Define the proof for one single loop iteration.  The counter `n` is used to
                // number the steps in the debug output.
                let mut one_loop_proof = |term_i_plus_k: Term| -> () {
                    //rpf.show_state();

                    print_stage("Mask `i` and rewrite symbolic expr");
                    rpf.rule_step();
                    rpf.rule_step();
                    //rpf.show_state();
                    rpf.rule_rewrite_reg(10, term_i_plus_k);
                    //rpf.show_state();

                    print_stage("Loop condition check (exit not taken)");
                    rpf.tactic_run();
                    //rpf.show_context();
                    //rpf.show_state();
                    rpf.rule_rewrite_reg(32, 0.into());
                    //rpf.show_state();

                    print_stage("Run until top of loop");
                    rpf.tactic_run_until(loop_addr);
                    //rpf.show_state();

                    let pc = rpf.state().pc;
                    if pc != loop_addr {
                        let instr = prog[pc];
                        panic!("got stuck at pc = {}, instr = {:?}", pc, instr);
                    }
                };

                // Apply the proof to two loops.
                println!("=== Prove the first loop");
                one_loop_proof(term_i_plus_1);
                println!("=== Prove the second loop");
                one_loop_proof(term_i_plus_2);

                // Shrink memory so that the conclusion matches the premise.
                rpf.rule_mem_abs_map(&live_addrs);
            });
        },
    );


    // ----------------------------------------
    // Prove the full loop by induction
    // ----------------------------------------
    println!("=== Prove the full loop by induction");

    // We are proving the following statement:
    //
    //      forall n,
    //          n < N_MAX ->
    //          forall b,
    //              reach(b, st_loop(start_i)) ->
    //              reach(b + n * 5426, st_loop(2n + start_i))
    //
    // We separate the binders for `b` and `n` because `tactic_induction` expects to see only a
    // single bound variable (`n`) in `Hsucc`.

    eprintln!("\n#prove p_loop");
    let p_loop = pf.tactic_induction(
        Prop::Forall(Binder::new(|vars| {
            // forall n,
            let n = vars.fresh();
            // n < N_MAX ->
            let p0 = Prop::Nonzero(Term::cmpa(N_MAX.into(), n));

            let q = Prop::Forall(Binder::new(|vars| {
                let n = n.shift();
                // forall b,
                let b = vars.fresh();
                // reach(b, st_loop(start_i)) ->
                let p = mk_prop_reach(start_i.into(), b);
                // reach(b + n * 5426, st_loop(2n + start_i))
                let i = Term::add(Term::mull(2.into(), n), start_i.into());
                let cyc = Term::add(b, Term::mull(n, 5426.into()));
                let q = mk_prop_reach(i, cyc);
                (vec![p].into(), Box::new(q))
            }));
            (vec![p0].into(), Box::new(q))
        })),

        // Base case
        |pf| {
            pf.tactic_forall_intro(
                |vars| {
                    let b = vars.fresh();
                    let p = mk_prop_reach(start_i.into(), b);
                    (vec![p], b)
                },
                |_pf, _b| {
                    // No-op.  The conclusion for the zero case is the same as the last premise.
                },
            );
        },

        // Inductive case
        |pf, n| {
            pf.tactic_forall_intro(
                |vars| {
                    let b = vars.fresh();
                    let p = mk_prop_reach(start_i.into(), b);
                    (vec![p], b)
                },
                |pf, b| {
                    let n = n.shift();
                    let p_n_plus_1_limit = (1, 0);
                    let p_ind_hyp = (1, 1);

                    // Show `n < N_MAX`
                    let _p_n_plus_1_limit = pf.tactic_clone(p_n_plus_1_limit);
                    let arith_lt_sub_1 = pf.tactic_clone(arith_lt_sub_1);
                    let _n_limit = pf.tactic_apply(arith_lt_sub_1,
                        &[Term::add(n, 1.into()), N_MAX.into()]);

                    // Use the induction hypothesis to show that iteration `n` is reachable.
                    let p_ind_hyp = pf.tactic_clone(p_ind_hyp);
                    let p_ind_hyp1 = pf.tactic_apply0(p_ind_hyp);
                    let _p_ind_hyp2 = pf.tactic_apply(p_ind_hyp1, &[b]);

                    //println!("============ Context (inductive case):");
                    //pf.show_context();
                    //println!("============ END Context");

                    // Use `p_iter` to show that iteration `n+1` is reachable.
                    let p_iter = pf.tactic_clone(p_iter);
                    let cyc_n = Term::add(b, Term::mull(n, 5426.into()));
                    let p_final = pf.tactic_apply(p_iter, &[cyc_n, n]);

                    // Rewrite the cycle count using associativity.
                    let arith_add_assoc = pf.tactic_clone(arith_add_assoc);
                    let cyc_eq = pf.tactic_apply(arith_add_assoc,
                        &[b, Term::mull(n, 5426.into()), 5426.into()]);
                    let cyc_n_plus_1 =
                        Term::add(b, Term::add(Term::mull(n, 5426.into()), 5426.into()));
                    pf.tactic_reach_shrink(p_final, cyc_n_plus_1);

                    // Move `p_final` to the end, so it becomes the conclusion of the forall.
                    pf.tactic_swap(cyc_eq, p_final);
                },
            );
        },
    );
    //pf.show_context();


    // ----------------------------------------
    // Prove the full execution
    // ----------------------------------------

    eprintln!("\n#Prove p_exec");
    pf.show_context();

    // Apply `p_loop` to `p_conc`.
    pf.rule_trivial();
    let p_loop1 = pf.tactic_apply(p_loop, &[(N_MAX - 1).into()]);
    let p_loop2 = pf.tactic_apply0(p_loop1);
    let p_exec = pf.tactic_apply(p_loop2, &[conc_state.cycle.into()]);

    // Shrink the cycle count to the lower bound we intend to reveal to the verifier.
    pf.tactic_reach_shrink(p_exec, 10_000_000_000_000.into());

    println!("\n============");
    println!("Final theorem:\n{}", pf.print(&pf.props()[p_exec.1]));
    println!("============\n");
    println!("Ok: Proof verified");

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

