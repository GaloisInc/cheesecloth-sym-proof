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
use std::env;
use env_logger;
use log::trace;
use sym_proof::advice;
use sym_proof::interp;
use sym_proof::kernel::Proof;
use sym_proof::logic::{Term, Prop, Binder, ReachableProp, StatePred};
use sym_proof::micro_ram::{self, Program};
use sym_proof::micro_ram::import;
use sym_proof::symbolic::{self, MemState, MemSnapshot};
use sym_proof::tactics::Tactics;

fn run(path: &str) -> Result<(), String> {
    let exec = import::load_exec(path);

    let (instrs, chunks) = import::convert_code_split(&exec);
    let prog = Program::new(&instrs, &chunks);
    eprintln!("loaded code: {} instrs", prog.len());
    let init_state = import::convert_init_state(&exec);
    eprintln!("loaded memory: {} words", init_state.mem.len());
    trace!("initial regs = {:?}", init_state.regs);

    // Load the concrete state from disk so we don't need to rerun the concrete prefix.
    #[cfg(not(feature = "playback_concrete_state"))] {
        compile_error!("can't run proof interpreter without playback_concrete_state");
    }
    #[cfg(feature = "playback_concrete_state")]
    let conc_state: micro_ram::State = {
        use std::fs::File;
        let f = File::open("advice/concrete_state.cbor")
            .map_err(|e| e.to_string())?;
        serde_cbor::from_reader(f)
            .map_err(|e| e.to_string())?
    };

    MemSnapshot::init_data(conc_state.mem.clone());


    // ----------------------------------------
    // Set up the proof state
    // ----------------------------------------

    // Load advice first, so `AVec`s inside `Proof` can find their lengths.
    advice::load()?;

    let mut pf = Proof::new(prog);


    // Set up initial proof context
    //
    // Unlike `proof_sqrt`, we don't wrap these in `advice::dont_record`.  In `proof_sqrt`, we want
    // to avoid recording the rule application.  Here, the rule application has already been
    // omitted, but we'd like to record any `Term`s, `AVec`s, etc. that may show up during the
    // application of this rule.

    // Arithmetic lemmas.

    let _arith_2n_ne_1 = pf.tactic_admit(Prop::Forall(Binder::new(|vars| {
        let n = vars.fresh();
        // (2 * n == 1) == 0
        let a = Term::mull(2.into(), n);
        let eq = Term::cmpe(1.into(), a);
        let ne = Prop::Nonzero(Term::cmpe(eq, 0.into()));
        (vec![].into(), Box::new(ne))
    })));

    let _arith_2n_plus_5_ne_1 = pf.tactic_admit(Prop::Forall(Binder::new(|vars| {
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

    let _arith_lt_sub_1 = pf.tactic_admit(Prop::Forall(Binder::new(|vars| {
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

    let _arith_add_assoc = pf.tactic_admit(Prop::Forall(Binder::new(|vars| {
        let a = vars.fresh();
        let b = vars.fresh();
        let c = vars.fresh();
        let l = Term::add(Term::add(a, b), c);
        let r = Term::add(a, Term::add(b, c));
        let concl = Prop::Nonzero(Term::cmpe(l, r));
        (vec![].into(), Box::new(concl))
    })));

    // `conc_state` is reachable.
    pf.rule_admit(Prop::Reachable(ReachableProp {
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


    interp::playback_proof(&mut pf, advice::playback::rules::Tag);

    pf.show_context();
    println!("\nfinal theorem:\n{}", pf.print(pf.props().last().unwrap()));

    println!("ok");
    // Drop `Proof` so any `AVec`s inside will record their lengths.
    drop(pf);
    advice::finish()?;

    Ok(())
}

fn main() {
    env_logger::init();
    let args = env::args().collect::<Vec<_>>();
    assert_eq!(args.len(), 2, "must provide cbor path");
    import::with_globals(|| run(&args[1]).unwrap());
}

