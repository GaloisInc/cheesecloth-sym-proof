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
use sym_proof::micro_ram::NUM_REGS;
use sym_proof::micro_ram::import;
use sym_proof::proof::{Proof, Prop, LemmaId};
use sym_proof::symbolic::{
    State, MemState, MemLog, VarCounter, Term, Pred, SubstTable,
};

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


    // ----------------------------------------
    // Prove behavior of one iteration
    // ----------------------------------------

    // We want to prove a lemma along the lines of:
    //
    //  forall C R12,
    //  { pc = 123 /\ cycle = C /\ r0 = 0 /\ r12 = R12 /\ R12 > 0 }
    //      ->*
    //  { pc = 123 /\ cycle = C + 13 /\ r0 = 0 /\ r12 = R12 - 1 }
    //
    // Register r12 is the `n` argument to `memcpy`, which indicates the number of bytes to copy.
    // In the implementation used in `grit`, `n` is decremented each time around the loop until it
    // reaches zero.  The loop itself takes 13 cycles.
    //
    // Registers other than r0 and r12 have values of some sort, and some are even updated during
    // the loop, but none of them are relevant to our overall proof.

    eprintln!("\nproving 1 iteration:");

    let mut pf = Proof::new(prog);

    // Set up the pre state.
    let mut vars = VarCounter::new();
    // All registers are symbolic (except for r0, which is always zero).
    let mut regs: [Term; NUM_REGS] = array::from_fn(|_| vars.fresh());
    regs[0] = Term::const_(0);
    // We don't care about any of the values read or written during the `memcpy` loop.  So we use
    // `MemLog`, where writes are allowed even at symbolic addresses.  Since we don't care about
    // the values loaded, we use `load_fresh` below, which introduces a fresh, unconstrained
    // variable for the result of the load.
    let mem = MemState::Log(MemLog { l: Vec::new() });
    // Require that `r12 >u 0` in the initial state.  `cmpa` is unsigned greater-than.
    let preds = vec![
        // `regs[12]` is the symbolic variable `x12`, so this predicate is `nonzero(x12 >u 0)`.
        // Note that `>u` is the MicroRAM binary operator `cmpa`, which returns 0 or 1.  In Coq,
        // this would be a value of type `bool`, not the `Prop` `x > y`.
        Pred::Nonzero(Term::cmpa(regs[12].clone(), Term::const_(0))),
    ];
    // We place no constraints on the initial value of the cycle counter.  This makes the lemma
    // applicable no matter how many loop iterations we previously performed.
    let cycle = vars.fresh();
    let state = State::new(
        conc_state.pc,
        cycle.clone(),
        regs.clone(),
        mem,
    );

    // Prove the lemma.
    let l_loop = pf.tactic_step_prove(vars, preds, state, |mut spf| {
        // Call this function any time to print the next instruction to be executed:
        //spf.show_instr();

        // The loop begins with `cmpe` + `cnjmp`, which jumps to the top of the loop if the counter
        // `n` is nonzero.

        // Step over the `cmpe` condition check first.  `step_concrete` tries to handle cases where
        // the inputs to the instruction are concrete.
        spf.tactic_step_concrete()?;

        // We want to step over the `cnjmp`, which is taken when the condition flag in r32 is
        // nonzero.  Currently, `r32` holds the symbolic expression `x12 == 0`.  We'd like to
        // replace this with a concrete constant so we can use `tactic_step_concrete` on the jump.
        //eprintln!("reg 32 = {}", spf.regs[32]);
        // First, we need to show `eq((x12 == 0), 0)`.
        spf.rule_derive_pred(|ppf| {
            // Show all `Pred`s in the current context.  These are facts we know about the symbolic
            // variables.
            //ppf.show();
            // From `nonzero(x12 >u 0)`, derive `eq((x12 == 0), 0)`.
            ppf.rule_gt_ne_unsigned(regs[12].clone(), 0.into())?;
            Ok(())
        })?;
        // Now we can rewrite the value of r32 to the constant 0.
        spf.rule_rewrite_reg(32, Term::const_(0))?;
        // The jump condition is concrete, so `step_concrete` can handle it.
        spf.tactic_step_concrete()?;

        // Run the loop body.

        // `run_concrete` applies `step_concrete` until it fails.
        spf.tactic_run_concrete()?;
        // We've reached a load instruction.  We don't care about the value, so just replace it
        // with a fresh variable.
        spf.rule_step_mem_load_fresh()?;
        // Keep running to complete the loop.
        spf.tactic_run_concrete_until(conc_state.pc)?;


        // The symbolic expressions for these registers are complex, and their values don't affect
        // the proof.  We replace each register with a fresh variable, forgetting everything we
        // know about its actual value, because this simplifies the work of chaining iterations
        // together.
        spf.rule_forget_reg(11);
        spf.rule_forget_reg(13);
        spf.rule_forget_reg(14);
        spf.rule_forget_reg(15);
        spf.rule_forget_reg(32);

        Ok(())
    })?;

    // Helper functions to print a `Prop::Step` lemma.
    let dump = |prop: &Prop| {
        let p = prop.as_step().unwrap();
        eprintln!("pc: {} -> {}", p.pre().pc, p.post().pc);
        for i in 0 .. NUM_REGS {
            eprintln!("{:2}: {} -> {}", i, p.pre().regs()[i], p.post().regs()[i]);
        }
        eprintln!("cycle: {} -> {}", p.pre().cycle, p.post().cycle);
        for pred in p.preds() {
            eprintln!("pred: {}", pred);
        }
    };
    // Helper functions to print just the predicates from a `Prop::Step` lemma.  This is useful for
    // debugging uses of `rule_strengthen_preds`, where we expect certain predicates to be removed.
    let dump_preds = |prop: &Prop| {
        let p = prop.as_step().unwrap();
        for pred in p.preds() {
            eprintln!("pred: {}", pred);
        }
        for pred in p.derived_preds() {
            eprintln!("pred (derived): {}", pred);
        }
    };

    eprintln!("\nfinal lemma for 1 iteration:");
    dump(pf.lemma(l_loop));


    // ----------------------------------------
    // Compose multi-iteration proofs
    // ----------------------------------------

    // We've proved a lemma describing a single iteration.  We now prove several more lemmas
    // describing multiple iterations at once.

    // For each `n`, this stores the `LemmaId` of a `Prop::Step` covering `n` iterations.
    let mut l_loops = HashMap::<u64, LemmaId>::new();
    l_loops.insert(1, l_loop);

    // Join a lemma for `m1` iterations with a lemma for `m2` iterations to prove a new lemma
    // describing `m1 + m2` iterations.
    let mut join = |m1, m2| -> Result<(), String> {
        let n = m1 + m2;
        eprintln!("\nbuild {}-iteration proof:", n);
        let l1 = l_loops[&m1];
        let l2 = l_loops[&m2];

        // `step_seq` is the sequencing rule for `Prop::Step`:
        //      {P} ->* {Q} /\ {Q} ->* {R} => {P} ->* {R}
        //
        // The closure passed to `step_seq` produces a pair of assignments.  These are needed
        // because each `Prop::Step` is really a statement of the form:
        //      forall x, preds x -> forall s, pre x s -> exists s', post x s
        // where `x` gives a value for each symbolic variable and `s` and `s'` are concrete states.
        // We want to compose a new lemma of this form out of two existing ones; the composed lemma
        // has its own `x` (`vars`), and to invoke the two inner lemmas, we must pass some
        // expression in terms of the outer `x`.  The two assigments returned by the closure give
        // those expressions, one for each variable of each inner lemma.
        //
        // Substituting the first assignment into `l1`'s post state and the second assignment into
        // `l2`'s pre state must produce two equivalent states.  This allows composing the two
        // `Prop::Step`s.
        let l_cur = pf.rule_step_seq(l1, l2, |vars| {
            // Here we are careful about the number and order of `vars.fresh()` calls to ensure
            // that the new lemma takes its variables in the same order as the old ones.  This
            // ensures every lemma in `l_loops` has the same meaning for its variables.

            // `rest` gives fresh variables for unused registers and other cases not covered below.
            let rest: [Option<Term>; 40] = array::from_fn(|_| Some(vars.fresh()));
            let mut rest1 = rest.clone();
            let mut rest2 = rest.clone();

            // Extra vars to use for the variables introduced by `forget_reg` in the middle state.
            // These don't appear anywhere in the final lemma, which keeps lemmas from growing
            // larger with each `join`.
            let forgotten: [Option<Term>; 5] = array::from_fn(|_| Some(vars.fresh()));
            let mut forgotten1: [Option<Term>; 5] = forgotten.clone();
            let mut forgotten2: [Option<Term>; 5] = forgotten.clone();

            // In all `l_loops` lemmas, the initial value of `r12` is `x12`.  For `l1`, we
            // substitute the outer lemma's variable `y12` (`rest[12]`) for `x12`, which means
            // `r12`'s initial value is `y12` and its final value is `y12 - m1` (since `l1` runs
            // the loop for `m1` iterations and decreases the counter by `m1`).
            let mut n1 = rest[12].clone();
            // For `l2`, we substitute `y12 - m1` for `x12`, so the initial value of register `r12`
            // is `y12 - m1` and the final value is `y12 - m1 - m2`.  Notice that the two middle
            // states (`l1`'s pre state and `l2`'s post state) both have `r12 = y12 - m1`.
            let mut n2 = Some(Term::add(n1.clone().unwrap(),
                Term::const_(-(m1 as i64) as u64)));

            // We use a similar scheme for the cycle number, which is `x33`.  Each iteration is 13
            // cycles, so the middle state has `cycle = y33 + 13 * m1`.
            let mut cycle1 = rest[33].clone();
            let mut cycle2 = Some(Term::add(cycle1.clone().unwrap(),
                Term::const_(13 * m1)));

            (
                SubstTable::new(move |v| match v {
                    12 => n1.take().unwrap(),
                    33 => cycle1.take().unwrap(),
                    35 => forgotten1[0].take().unwrap(),
                    36 => forgotten1[1].take().unwrap(),
                    37 => forgotten1[2].take().unwrap(),
                    38 => forgotten1[3].take().unwrap(),
                    39 => forgotten1[4].take().unwrap(),
                    _ => rest1[v].take().unwrap(),
                }),
                SubstTable::new(move |v| match v {
                    12 => n2.take().unwrap(),
                    33 => cycle2.take().unwrap(),
                    11 => forgotten2[0].take().unwrap(),
                    13 => forgotten2[1].take().unwrap(),
                    14 => forgotten2[2].take().unwrap(),
                    15 => forgotten2[3].take().unwrap(),
                    32 => forgotten2[4].take().unwrap(),
                    _ => rest2[v].take().unwrap(),
                }),
            )
        })?;

        // Strengthen the predicates of the new lemma.  The 1-step lemma requires `x12 >u 0`, and
        // `step_seq` combines the predicates of the two input lemmas (after substituting), so we
        // end up with a 2-step lemma requiring `x12 >u 0` and `x12 - 1 >u 0`.  These can be
        // combined into a single predicate `x12 >u 1`, preventing the list of predicates from
        // doubling in size each time we double the step count.
        eprintln!("before strengthen:");
        dump_preds(pf.lemma(l_cur));

        pf.rule_step_extend(l_cur, |mut spf| {
            // Introduce the new predicate `x12 >u n - 1`, and show that it implies the two
            // existing predicates `x12 >u m1 - 1` and `x12 - m1 >u m2 - 1` so they can be removed.
            let bound = Term::const_(n - 1);
            let prev_bound = Term::const_(m1 - 1);
            let step = Term::const_(m1);
            let gt_bound = Pred::Nonzero(Term::cmpa(regs[12].clone(), bound.clone()));
            spf.rule_strengthen_preds(vec![gt_bound], |ppf| {
                // In this scope, we have only the new predicate `x12 >u n - 1`.  We wish to prove
                // the other two predicates mentioned above, which will cause `strengthen_preds` to
                // remove them from the predicate list of the `Prop::Step`.

                //ppf.show();

                // First, we explicitly prove the trivial fact `nonzero(1)`.  Some of the premises
                // of the later rules, such as `n - 1 >=u m1 - 1`, will be constant-folded to
                // `nonzero(1)` automatically, and the resulting premise must be in scope for the
                // rule to succeed.
                ppf.rule_nonzero_const(1);

                // `(x12 >u n - 1) /\ (n - 1 >= m1 - 1) => (x12 >u m1 - 1)`
                ppf.rule_gt_ge_unsigned(regs[12].clone(), bound.clone(), prev_bound.clone())?;
                // `(x12 >u n - 1) /\ (0 <= m1 <= n - 1) => (x12 - m1 >u n - 1 - m1)`.  Note that
                // `n - 1 - m1 = m2 - 1`.
                ppf.rule_gt_sub_unsigned(regs[12].clone(), bound.clone(), step.clone())?;
                ppf.show();
                Ok(())
            })
        })?;

        eprintln!("after strengthen:");
        dump_preds(pf.lemma(l_cur));

        //dump(pf.lemma(l_cur));
        l_loops.insert(n, l_cur);

        Ok(())
    };

    // Efficiently combine lemmas to reach a 63-step lemma.
    join(1, 1)?;
    join(2, 2)?;
    join(4, 4)?;
    join(8, 8)?;
    join(16, 16)?;
    join(32, 16)?;
    join(48, 8)?;
    join(56, 4)?;
    join(60, 2)?;
    join(62, 1)?;

    // We can also prove the 64-step lemma, but it won't apply to the concrete state where the loop
    // counter is only 63.
    join(32, 32)?;


    // ----------------------------------------
    // Apply the lemma to the concrete state
    // ----------------------------------------

    eprintln!("\napply proof to concrete state:");

    // Changing 63 to 64 here fails, because concretely the loop only runs for 63 iterations.
    let p = pf.lemma(l_loops[&63]).as_step().unwrap();

    // Check that the precondition holds on the concrete state.  We have to provide a value for
    // each variable, similar to the substitution provided when joining lemmas.
    //
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

    assert!(post_cycle > 1000);
    eprintln!("proof complete");

    Ok(())
}

fn main() {
    env_logger::init();
    let args = env::args().collect::<Vec<_>>();
    assert_eq!(args.len(), 2, "must provide cbor path");
    import::with_globals(|| run(&args[1]).unwrap());
}

