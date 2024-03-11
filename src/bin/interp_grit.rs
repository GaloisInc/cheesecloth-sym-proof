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
        let f = File::open(advice::advice_dir().join("concrete_state.cbor"))
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

    let arith_n_minus_1_ne_0 = pf.rule_admit(Prop::Forall(Binder::new(|vars| {
        let n = vars.fresh();
        // n > 1
        let n_limit = Prop::Nonzero(Term::cmpa(n, 1.into()));
        // (n - 1) != 0
        let n_minus_1 = Term::sub(n, 1.into());
        let concl = Prop::Nonzero(Term::cmpe(Term::cmpe(n_minus_1, 0.into()), 0.into()));
        (vec![n_limit].into(), Box::new(concl))
    })));

    let arith_n_plus_1_gt_1 = pf.rule_admit(Prop::Forall(Binder::new(|vars| {
        let n = vars.fresh();
        // n > 0
        let n_lo = Prop::Nonzero(Term::cmpa(n, 0.into()));
        // n < 1000
        let n_hi = Prop::Nonzero(Term::cmpa(1000.into(), n));
        // n + 1 > 1
        let concl = Prop::Nonzero(Term::cmpa(Term::add(n, 1.into()), 1.into()));
        (vec![n_lo, n_hi].into(), Box::new(concl))
    })));

    let arith_n_minus_1_lt_1000 = pf.rule_admit(Prop::Forall(Binder::new(|vars| {
        let n = vars.fresh();
        // n > 0
        let n_lo = Prop::Nonzero(Term::cmpa(n, 0.into()));
        // n < 1000
        let n_hi = Prop::Nonzero(Term::cmpa(1000.into(), n));
        // n + 1 > 1
        let concl = Prop::Nonzero(Term::cmpa(1000.into(), Term::sub(n, 1.into())));
        (vec![n_lo, n_hi].into(), Box::new(concl))
    })));

    let arith_add_assoc = pf.rule_admit(Prop::Forall(Binder::new(|vars| {
        let a = vars.fresh();
        let b = vars.fresh();
        let c = vars.fresh();
        let l = Term::add(Term::add(a, b), c);
        let r = Term::add(a, Term::add(b, c));
        let concl = Prop::Nonzero(Term::cmpe(l, r));
        (vec![].into(), Box::new(concl))
    })));

    // `conc_state` is reachable.
    //
    // Unlike `proof_grit`, we don't wrap this in `advice::dont_record`.  In `proof_grit`, we want
    // to avoid recording the rule application.  Here, the rule application has already been
    // omitted, but we'd like to record any `Term`s, `AVec`s, etc. that may show up during the
    // application of this rule.
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

