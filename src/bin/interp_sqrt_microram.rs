//! Proof that sqrt runs for at least 10^13 steps.
// The proof implementation returns `Err` when a rule fails to apply.  A bad proof will be caught
// eventually, but checking all `Result`s lets us catch problems sooner.
#![deny(unused_must_use)]
#![cfg_attr(feature = "deny_warnings", deny(warnings))]
#![cfg_attr(feature = "microram", no_std)]
#![cfg_attr(feature = "microram", no_main)]
#![cfg_attr(feature = "microram", feature(default_alloc_error_handler))]
#![cfg_attr(feature = "microram", feature(lang_items))]

extern crate alloc;

use core::mem;
use core::ptr;
use alloc::boxed::Box;
use alloc::vec;
#[cfg(feature = "microram")] use cheesecloth_alloc;
use sym_proof::Word;
use sym_proof::advice;
use sym_proof::interp;
use sym_proof::kernel::Proof;
use sym_proof::logic::{Term, TermKind, Prop, Binder, ReachableProp, StatePred};
use sym_proof::micro_ram::{Program, NUM_REGS};
use sym_proof::symbolic::{self, MemState, MemSnapshot};

#[path = "../../gen/sqrt_program.rs"] mod program;
#[path = "../../gen/sqrt_term_table.rs"] mod term_table;


// Initial snapshot

#[derive(Clone, Debug)]
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


#[cfg(not(feature = "microram"))]
mod emulate_snapshot {
    use std::cell::RefCell;
    use std::collections::BTreeMap;
    use sym_proof::{Addr, Word};
    use sym_proof::micro_ram;
    use super::{CpuState, SNAPSHOT_CPU_STATE};

    thread_local! {
        static SNAPSHOT_MEM: RefCell<BTreeMap<Addr, Word>> = RefCell::new(BTreeMap::new());
    }

    #[no_mangle]
    extern "C" fn cc_load_snapshot_word(addr: u64) -> u64 {
        let value = SNAPSHOT_MEM.with(|rc| {
            rc.borrow().get(&addr).copied().unwrap()
        });
        eprintln!("cc_load_snapshot_word: ({addr}, {value}),");
        value
    }

    #[cfg(not(feature = "microram"))]
    pub unsafe fn load_concrete_state() {
        // Load the concrete state from disk so we don't need to rerun the concrete prefix.
        #[cfg(not(feature = "playback_concrete_state"))] {
            compile_error!("can't run proof interpreter without playback_concrete_state");
        }
        #[cfg(feature = "playback_concrete_state")]
        let conc_state: micro_ram::State = {
            use std::fs::File;
            let f = File::open("advice/concrete_state.cbor").unwrap();
            serde_cbor::from_reader(f).unwrap()
        };

        unsafe {
            SNAPSHOT_CPU_STATE = CpuState {
                pc: conc_state.pc,
                cycle: conc_state.cycle,
                regs: conc_state.regs,
            };
        }

        SNAPSHOT_MEM.with(|rc| {
            *rc.borrow_mut() = conc_state.mem;
        });
    }
}

#[cfg(feature = "microram")]
#[no_mangle]
extern "C" fn cc_load_snapshot_word(addr: u64) -> u64 {
    // TODO/HACK: hardcoded initial state from sqrt concrete execution
    //assert!(addr % mem::size_of::<u64>() as u64 == 0);
    //unsafe { ptr::read_volatile(addr as usize as *mut u64) }

    static mut COUNTER: usize = 0;
    static MEM_ADVICE: &[(u64, u64)] = &[
        (2147480720, 461708),
        (4295565208, 8589934593),
        (4295564600, 137438953475),
        (4295564584, 137438953484),
        (4295565304, 4295566784),
        (4295560608, 4294967296),
        (4295566792, 12884901889),
        (4295560592, 4295563808),
        (4295563808, 65),
        (4295563808, 65),
        (4295563808, 65),
        (4295563808, 65),
        (4295563808, 65),
        (4295563808, 65),
        (4295563808, 65),
        (4295563808, 65),
        (4295560600, 4294967297),
        (4295565280, 12884901889),
        (4295565200, 4295569024),
        (4295565232, 8589934593),
        (4295560608, 4294967296),
        (4295565256, 12884901888),
        (4295565224, 4295566608),
        (4295566784, 4295568544),
        (4295565248, 4295568448),
        (4295565272, 4295568928),
        (4295567168, 4295564912),
        (4295564608, 12),
        (4295564592, 4295564704),
        (2147480728, 4295565136),
        (4295565136, 8589934593),
        (2147480768, 4295565128),
        (4295565128, 4295566176),
        (2147480688, 253863),
        (2147480680, 3),
        (2147480672, 1),
        (2147480664, 4295564144),
        (2147480656, 1),
        (2147480648, 4295564560),
        (2147480640, 4295565008),
        (4295564712, 51539607558),
        (4295565216, 0),
        (2147480288, 145902),
        (2147480280, 1),
        (2147480272, 4295565128),
        (2147480264, 4295565200),
        (2147480256, 2),
        (2147480248, 4295565200),
        (2147480240, 1),
        (2147480232, 4295565224),
        (2147480224, 4295564560),
        (2147480216, 0),
        (2147480208, 4295565176),
        (2147480200, 1),
        (2147480304, 3721),
        (2147480312, 0),
        (4295569024, 3721),
        (4295569032, 0),
        (4295565216, 0),
        (4295565208, 8589934593),
        (2147480624, 254629),
        (2147480616, 4295565128),
        (2147480608, 4295565128),
        (2147480600, 4295560592),
        (2147480592, 4295565128),
        (2147480584, 4295565200),
        (2147480576, 4295564560),
        (2147480568, 4295560144),
        (2147480560, 4295560592),
        (2147480552, 0),
        (2147480544, 4295565176),
        (2147480536, 1),
        (2147480528, 4295565032),
        (4295564720, 64424509453),
        (4295565240, 0),
        (4295565264, 0),
        (4295565256, 12884901888),
        (4295565264, 0),
        (4295565288, 0),
        (4295566800, 0),
        (2147480456, 4295565272),
        (4295566792, 12884901889),
        (2147480520, 4295566784),
        (2147480464, 57),
        (4295568544, 9367487224930631680),
        (4295566800, 0),
        (2147480352, 1),
        (2147480344, 1),
        (2147480432, 4295564560),
        (2147480440, 0),
        (2147480424, 4295565128),
        (4295565240, 0),
        (4295565232, 8589934593),
        (2147480416, 0),
        (2147480488, 4294967295),
        (2147480480, 0),
        (2147480472, 0),
        (2147480512, 1),
        (2147480448, 9079256848778919936),
        (2147480504, 8),
        (2147480496, 2),
        (4295568456, 28),
        (4295568448, 0),
        (4295568928, 2305843009213693952),
        (4295568936, 0),
        (4295566608, 57),
        (4295565288, 0),
        (4295565280, 12884901889),
        (2147480400, 144165),
        (2147480392, 1),
        (2147480384, 57),
        (2147480376, 57),
        (2147480368, 9367487224930631680),
        (2147480360, 4295568928),
        (4295566176, 16),
        (4295565144, 0),
        (4295564568, 4295564912),
        (4295565136, 8589934593),
        (4295564600, 137438953475),
        (4295564584, 137438953484),
        (4295564608, 12),
        (4295564616, 0),
        (2147480784, 3),
    ];
    unsafe {
        let (a, v) = MEM_ADVICE[COUNTER];
        COUNTER += 1;
        assert!(addr == a);
        v
    }
}


#[cfg(not(feature = "microram"))]
mod emulate_advice {
    use std::cell::RefCell;
    use std::fs::File;
    use serde_cbor;
    use sym_proof::advice;

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

    pub unsafe fn load_advice() {
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
}


#[cfg(not(feature = "microram"))]
fn exit() -> ! {
    println!("ok");
    std::process::exit(0);
}

#[cfg(not(feature = "microram"))]
#[track_caller]
fn fail() -> ! {
    panic!("fail")
}

#[cfg(feature = "microram")]
extern "C" {
    fn __cc_answer(val: usize) -> !;
}

#[cfg(feature = "microram")]
fn exit() -> ! {
    unsafe {
        ptr::write_volatile(0xffff_ffff_ffff_fff0 as *mut usize, 1);
        __cc_answer(1);
    }
}

#[cfg(feature = "microram")]
fn fail() -> ! {
    unsafe {
        __cc_answer(0);
    }
}


fn run() -> ! {
    let prog = Program::new(&program::PROG_INSTRS, &program::PROG_CHUNKS);


    // ----------------------------------------
    // Set up the proof state
    // ----------------------------------------

    let mut pf = Proof::new(prog);

    unsafe {
        // TODO/HACK: hardcoded initial state from sqrt concrete execution
        SNAPSHOT_CPU_STATE = CpuState {
            pc: 253846,
            cycle: 5511359,
            regs: [
                0, 253863, 2147480696, 0, 0, 57, 0, 0,
                4, 1, 4295565128, 1, 11, 16, 4295566176, 1,
                4295566176, 0, 4295564144, 1, 4295564560, 4295565008, 4295560144, 4295560592,
                0, 4295565176, 1, 4295565032, 0, 28, 0, 0,
                4295566176
            ]
        };
    }


    // Set up initial proof context
    //
    // Unlike `proof_sqrt`, we don't wrap these in `advice::dont_record`.  In `proof_sqrt`, we want
    // to avoid recording the rule application.  Here, the rule application has already been
    // omitted, but we'd like to record any `Term`s, `AVec`s, etc. that may show up during the
    // application of this rule.

    // Arithmetic lemmas.

    pf.rule_admit(Prop::Forall(Binder::new(|vars| {
        let n = vars.fresh();
        // (2 * n == 1) == 0
        let a = Term::mull(2.into(), n);
        let eq = Term::cmpe(1.into(), a);
        let ne = Prop::Nonzero(Term::cmpe(eq, 0.into()));
        (vec![].into(), Box::new(ne))
    })));

    pf.rule_admit(Prop::Forall(Binder::new(|vars| {
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

    pf.rule_admit(Prop::Forall(Binder::new(|vars| {
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

    pf.rule_admit(Prop::Forall(Binder::new(|vars| {
        let a = vars.fresh();
        let b = vars.fresh();
        let c = vars.fresh();
        let l = Term::add(Term::add(a, b), c);
        let r = Term::add(a, Term::add(b, c));
        let concl = Prop::Nonzero(Term::cmpe(l, r));
        (vec![].into(), Box::new(concl))
    })));

    // `conc_state` is reachable.
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

    #[cfg(not(feature = "microram"))] {
        println!("\nfinal theorem:\n{}", pf.print(pf.props().last().unwrap()));
    }

    let prop = pf.props().last().unwrap();
    let rp = match *prop {
        Prop::Reachable(ref rp) => rp,
        _ => fail(),
    };
    let min_cycles = match rp.min_cycles.kind() {
        TermKind::Const(x) => x,
        _ => fail(),
    };
    let ok = min_cycles >= 10_000_000_000_000;
    if !ok {
        fail();
    }

    exit();
}

#[cfg(not(feature = "microram"))]
fn main() {
    env_logger::init();
    unsafe { emulate_snapshot::load_concrete_state() };
    unsafe { emulate_advice::load_advice() };
    run();
}

#[cfg(feature = "microram")]
#[no_mangle]
fn main() {
    run();
}


#[cfg(feature = "microram")]
#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    fail();
}

#[cfg(feature = "microram")]
#[lang = "eh_personality"]
extern "C" fn eh_personality() {}


#[cfg(not(feature = "microram"))]
mod cc_trace {
    use std::ffi::CStr;

    #[no_mangle]
    unsafe extern "C" fn __cc_trace(s: *const u8) {
        eprintln!("[TRACE] {:?}", CStr::from_ptr(s as *const i8));
    }

    #[no_mangle]
    unsafe extern "C" fn __cc_trace_exec(s: *const u8, arg0: usize, arg1: usize, arg2: usize, arg3: usize) {
        eprintln!("[TRACE] {:?}({:x}, {:x}, {:x}, {:x})", CStr::from_ptr(s as *const i8), arg0, arg1, arg2, arg3);
    }
}
