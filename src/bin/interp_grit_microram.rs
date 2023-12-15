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
use std::cell::RefCell;
use std::env;
use std::fs::File;
use env_logger;
use log::trace;
use serde_cbor;
use sym_proof::Word;
use sym_proof::advice;
use sym_proof::interp;
use sym_proof::kernel::Proof;
use sym_proof::logic::{Term, Prop, Binder, VarCounter, ReachableProp, StatePred};
use sym_proof::micro_ram::{self, Program, NUM_REGS};
use sym_proof::symbolic::{self, MemState, MemSnapshot};

#[path = "../../gen/grit_program.rs"] mod program;
#[path = "../../gen/grit_term_table.rs"] mod term_table;


struct CpuState {
    pc: Word,
    cycle: Word,
    regs: [Word; NUM_REGS],
}

static mut SNAPSHOT_CPU_STATE: CpuState = CpuState {
    pc: 0,
    cycle: 0,
    regs: [0; NUM_REGS],
};

unsafe fn load_snapshot_cpu_state() {
    // Load the concrete state from disk so we don't need to rerun the concrete prefix.
    #[cfg(not(feature = "playback_concrete_state"))] {
        compile_error!("can't run proof interpreter without playback_concrete_state");
    }
    #[cfg(feature = "playback_concrete_state")]
    let conc_state: micro_ram::State = {
        use std::fs::File;
        let mut f = File::open("advice/concrete_state.cbor").unwrap();
        serde_cbor::from_reader(f).unwrap()
    };
    unsafe {
        SNAPSHOT_CPU_STATE = CpuState {
            pc: conc_state.pc,
            cycle: conc_state.cycle,
            regs: conc_state.regs,
        };
    }
}


fn run() -> Result<(), String> {
    let prog = Program::new(&program::PROG_INSTRS, &program::PROG_CHUNKS);
    eprintln!("loaded code: {} instrs", prog.len());
    //eprintln!("loaded memory: {} words", init_state.mem.len());


    // ----------------------------------------
    // Set up the proof state
    // ----------------------------------------

    let mut pf = Proof::new(prog);

    // `conc_state` is reachable.
    //
    // Unlike `interp_grit`, we don't wrap this in `advice::dont_record`.  In `proof_grit`, we want
    // to avoid recording the rule application.  Here, the rule application has already been
    // omitted, but we'd like to record any `Term`s, `AVec`s, etc. that may show up during the
    // application of this rule.
    let cpu_state = unsafe { &SNAPSHOT_CPU_STATE };
    pf.rule_admit(Prop::Reachable(ReachableProp {
        pred: Binder::new(|_vars| {
            StatePred {
                state: symbolic::State::new(
                    cpu_state.pc,
                    cpu_state.regs.map(|x| x.into()),
                    MemState::Snapshot(MemSnapshot { base: 0 }),
                    None,
                ),
                props: Box::new([]),
            }
        }),
        min_cycles: cpu_state.cycle.into(),
    }));

    interp::playback_proof(&mut pf, advice::playback::rules::Tag);

    println!("\nfinal theorem:\n{}", pf.print(pf.props().last().unwrap()));

    println!("ok");

    Ok(())
}

fn main() {
    env_logger::init();
    unsafe { load_snapshot_cpu_state() };
    unsafe { load_advice() };
    run().unwrap();
}


#[derive(Default)]
struct AdviceStream {
    data: Vec<advice::Value>,
    pos: usize,
}

impl AdviceStream {
    pub fn new(data: Vec<advice::Value>) -> AdviceStream {
        AdviceStream { data, pos: 0 }
    }

    pub fn next(&mut self) -> advice::Value {
        assert!(self.pos < self.data.len(),
            "tried to read past end of advice stream of length {}", self.data.len());
        let x = self.data[self.pos];
        self.pos += 1;
        x
    }
}

thread_local! {
    static ADVICE: RefCell<AdviceStream> = RefCell::new(AdviceStream::default());
}

unsafe fn load_advice() {
    // Load advice
    let f = File::open("advice/linear.cbor").unwrap();
    let advice: Vec<_> = serde_cbor::from_reader(f).unwrap();
    ADVICE.with(|c| {
        *c.borrow_mut() = AdviceStream::new(advice);
    });
}

#[no_mangle]
extern "C" fn __cc_advise(max: advice::Value) -> advice::Value {
    let x = ADVICE.with(|c| c.borrow_mut().next());
    assert!(x <= max);
    x
}
