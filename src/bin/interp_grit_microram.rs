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
use sym_proof::advice;
use sym_proof::interp;
use sym_proof::kernel::Proof;
use sym_proof::micro_ram::Program;

#[path = "../../gen/grit_program.rs"] mod program;
#[path = "../../gen/grit_term_table.rs"] mod term_table;

fn run() -> Result<(), String> {
    let prog = Program::new(&program::PROG_INSTRS, &program::PROG_CHUNKS);
    eprintln!("loaded code: {} instrs", prog.len());
    //eprintln!("loaded memory: {} words", init_state.mem.len());

    // TODO: concrete prefix?

    // Load advice
    let f = File::open("advice/linear.cbor")
        .map_err(|e| e.to_string())?;
    let advice: Vec<_> = serde_cbor::from_reader(f)
        .map_err(|e| e.to_string())?;
    ADVICE.with(|c| {
        *c.borrow_mut() = AdviceStream::new(advice);
    });

    // ----------------------------------------
    // Set up the proof state
    // ----------------------------------------

    let mut pf = Proof::new(prog);

    // TODO: add initial reach prop to `pf`

    interp::playback_proof(&mut pf, advice::playback::rules::Tag);

    println!("\nfinal theorem:\n{}", pf.print(pf.props().last().unwrap()));

    println!("ok");

    Ok(())
}

fn main() {
    env_logger::init();
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

#[no_mangle]
extern "C" fn __cc_advise(max: advice::Value) -> advice::Value {
    let x = ADVICE.with(|c| c.borrow_mut().next());
    assert!(x <= max);
    x
}
