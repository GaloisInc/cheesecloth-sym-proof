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
use sym_proof::advice::{self, RecordingStreamTag};
use sym_proof::interp::Rule;
use sym_proof::kernel::Proof;
use sym_proof::logic::{Term, TermKind, Prop, Binder, VarCounter, ReachableProp, StatePred};
use sym_proof::logic::shift::ShiftExt;
use sym_proof::micro_ram::Program;
use sym_proof::micro_ram::import;
use sym_proof::micro_ram::{Opcode, MemWidth, mem_load};
use sym_proof::symbolic::{self, MemState, MemSnapshot, Memory, MemMap, MemConcrete};
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

    println!("==== ADMIT: forall n, 2n != 1");
    // (assert (not (not (= (bvmul (_ bv2 64) n) (_ bv1 64)))))
    let arith_2n_ne_1 = pf.tactic_admit(Prop::Forall(Binder::new(|vars| {
        let n = vars.fresh();
        // (2 * n == 1) == 0
        let a = Term::mull(2.into(), n);
        let eq = Term::cmpe(1.into(), a);
        let ne = Prop::Nonzero(Term::cmpe(eq, 0.into()));
        (vec![].into(), Box::new(ne))
    })));

    println!("==== ADMIT: forall m n, m < 2^63  ->  n < m  ->  2n + 5 != 1");
    // (assert (bvugt #x7fffffffffffffff m))
    // (assert (bvugt m n))
    // (assert (not (not (= (bvadd (bvmul (_ bv2 64) n) (_ bv5 64)) (_ bv1 64)))))
    let arith_2n_plus_5_ne_1 = pf.tactic_admit(Prop::Forall(Binder::new(|vars| {
        let m = vars.fresh();
        let n = vars.fresh();
        // m < 2^63
        let m_limit = Prop::Nonzero(Term::cmpa((1 << 63).into(), m));
        // n < m
        let n_limit = Prop::Nonzero(Term::cmpa(m, n));
        // (2 * n + 5 == 1) == 0
        let a = Term::add(Term::mull(2.into(), n), 5.into());
        let eq = Term::cmpe(1.into(), a);
        let ne = Prop::Nonzero(Term::cmpe(eq, 0.into()));
        (vec![m_limit, n_limit].into(), Box::new(ne))
    })));

    println!("==== ADMIT: forall a b, 0 < a  ->  a < b  ->  a - 1 < b");
    // (assert (bvugt a (_ bv0 64)))
    // (assert (bvugt b a))
    // (assert (not (bvugt b (bvsub a (_ bv1 64)))))
    let arith_lt_sub_1 = pf.tactic_admit(Prop::Forall(Binder::new(|vars| {
        let a = vars.fresh();
        let b = vars.fresh();
        // 0 < a
        let low = Prop::Nonzero(Term::cmpa(a, 0.into()));
        // a < b
        let high = Prop::Nonzero(Term::cmpa(b, a));
        // a - 1 < b
        let concl = Prop::Nonzero(Term::cmpa(b, Term::sub(a, 1.into())));
        (vec![low, high].into(), Box::new(concl))
    })));


    println!("==== ADMIT: forall a b c, (a + b) + c == a + (b + c)");
    // (assert (not (= (bvadd (bvadd a b) c) (bvadd a (bvadd b c)))))
    let arith_add_assoc = pf.tactic_admit(Prop::Forall(Binder::new(|vars| {
        let a = vars.fresh();
        let b = vars.fresh();
        let c = vars.fresh();
        let l = Term::add(Term::add(a, b), c);
        let r = Term::add(a, Term::add(b, c));
        let concl = Prop::Nonzero(Term::cmpe(l, r));
        (vec![].into(), Box::new(concl))
    })));


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

    let start_i = 4;

    // We first prove a lemma of the form:
    //      forall b n,
    //          n < N_MAX ->
    //          reach(b, st_loop(2n + start_i)) ->
    //          reach(b + 5460, st_loop(2(n+1) + start_i))
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
            let arith_2n_ne_1 = pf.tactic_clone(arith_2n_ne_1);
            let _i_ne_1 = pf.tactic_apply(arith_2n_ne_1, &[Term::add(n, 2.into())]);

            let arith_2n_plus_5_ne_1 = pf.tactic_clone(arith_2n_plus_5_ne_1);
            let _i_plus_1_ne_1 = pf.tactic_apply(arith_2n_plus_5_ne_1, &[N_MAX.into(), n]);

            // Extend `p_reach` with two iterations worth of steps.
            let (p_reach, _i_plus_1_ne_1) = pf.tactic_swap(p_reach, _i_plus_1_ne_1);
            pf.tactic_reach_extend(p_reach, |rpf| {
                let n = n.shift();
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
                    rpf.show_context();
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
    //              reach(b + n * 5460, st_loop(2n + start_i))
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
                // reach(b + n * 5460, st_loop(2n + start_i))
                let i = Term::add(Term::mull(2.into(), n), start_i.into());
                let cyc = Term::add(b, Term::mull(n, 5460.into()));
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
                    let cyc_n = Term::add(b, Term::mull(n, 5460.into()));
                    let p_final = pf.tactic_apply(p_iter, &[cyc_n, n]);

                    // Rewrite the cycle count using associativity.
                    let arith_add_assoc = pf.tactic_clone(arith_add_assoc);
                    let cyc_eq = pf.tactic_apply(arith_add_assoc,
                        &[b, Term::mull(n, 5460.into()), 5460.into()]);
                    let cyc_n_plus_1 =
                        Term::add(b, Term::add(Term::mull(n, 5460.into()), 5460.into()));
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

