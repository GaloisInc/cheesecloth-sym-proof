//! Proof that grit runs for at least 1000 steps.
// The proof implementation returns `Err` when a rule fails to apply.  A bad proof will be caught
// eventually, but checking all `Result`s lets us catch problems sooner.
#![deny(unused_must_use)]
#![cfg_attr(feature = "deny_warnings", deny(warnings))]
#![cfg_attr(feature = "microram", no_std)]
#![cfg_attr(feature = "microram", no_main)]
#![cfg_attr(feature = "microram", feature(default_alloc_error_handler))]
#![cfg_attr(feature = "microram", feature(lang_items))]

extern crate alloc;
#[cfg(feature = "inline-secrets")] extern crate cheesecloth_sym_proof_secrets;

use core::mem;
use core::ptr;
use alloc::boxed::Box;
use alloc::vec;
#[cfg(feature = "microram")] use cheesecloth_alloc;
use cheesecloth_sym_proof_secret_decls as secret_decls;
use sym_proof::Word;
use sym_proof::advice;
use sym_proof::interp;
use sym_proof::kernel::Proof;
use sym_proof::logic::{Term, TermKind, Prop, Binder, ReachableProp, StatePred};
use sym_proof::micro_ram::{Program, NUM_REGS};
use sym_proof::symbolic::{self, MemState, MemSnapshot};

#[path = "../../gen/grit_program.rs"] mod program;

#[cfg(feature = "microram_hardcoded_snapshot")]
#[path = "../../gen/grit_hardcoded_snapshot.rs"] mod hardcoded_snapshot;


// Initial snapshot

#[derive(Clone, Debug)]
#[repr(C)]
pub struct CpuState {
    regs: [Word; NUM_REGS],
    pc: Word,
    cycle: Word,
}


#[cfg(feature = "microram_hardcoded_snapshot")]
mod emulate_snapshot_hardcoded {
    use sym_proof::{Addr, Word};
    use sym_proof::micro_ram::{self, NUM_REGS};
    use super::CpuState;
    use super::hardcoded_snapshot;

    #[no_mangle]
    extern "C" fn cc_load_snapshot_word(addr: u64) -> u64 {
        static mut COUNTER: usize = 0;
        unsafe {
            let (a, v) = hardcoded_snapshot::MEM_ADVICE[COUNTER];
            COUNTER += 1;
            assert!(addr == a);
            v
        }
    }

    pub static mut SNAPSHOT_CPU_STATE: CpuState = CpuState {
        pc: 0,
        cycle: 0,
        regs: [0; NUM_REGS],
    };

    pub unsafe fn init_snapshot() {
        unsafe {
            SNAPSHOT_CPU_STATE = CpuState {
                pc: hardcoded_snapshot::CPU_STATE_PC,
                cycle: hardcoded_snapshot::CPU_STATE_CYCLE,
                regs: hardcoded_snapshot::CPU_STATE_REGS,
            };
        }
    }
}
#[cfg(feature = "microram_hardcoded_snapshot")]
use self::emulate_snapshot_hardcoded::{init_snapshot, SNAPSHOT_CPU_STATE};

#[cfg(all(not(feature = "microram_hardcoded_snapshot"), not(feature = "microram")))]
mod emulate_snapshot {
    use std::cell::RefCell;
    use std::collections::BTreeMap;
    use sym_proof::{Addr, Word};
    use sym_proof::micro_ram::{self, NUM_REGS};
    use super::CpuState;

    thread_local! {
        static SNAPSHOT_MEM: RefCell<BTreeMap<Addr, Word>> = RefCell::new(BTreeMap::new());
    }

    thread_local! {
        static SNAPSHOT_MEM_ADVICE: RefCell<Vec<(Addr, Word)>> = RefCell::new(Vec::new());
    }

    #[no_mangle]
    extern "C" fn cc_load_snapshot_word(addr: u64) -> u64 {
        let value = SNAPSHOT_MEM.with(|rc| {
            rc.borrow().get(&addr).copied().unwrap()
        });
        SNAPSHOT_MEM_ADVICE.with(|rc| rc.borrow_mut().push((addr, value)));
        value
    }

    pub static mut SNAPSHOT_CPU_STATE: CpuState = CpuState {
        pc: 0,
        cycle: 0,
        regs: [0; NUM_REGS],
    };

    pub unsafe fn init_snapshot() {
        // Load the concrete state from disk so we don't need to rerun the concrete prefix.
        #[cfg(not(feature = "playback_concrete_state"))] {
            compile_error!("can't run proof interpreter without playback_concrete_state");
        }
        #[cfg(feature = "playback_concrete_state")]
        let conc_state: micro_ram::State = {
            use std::fs::File;
            use sym_proof::advice;
            let f = File::open(advice::advice_dir().join("concrete_state.cbor")).unwrap();
            serde_cbor::from_reader(f).unwrap()
        };

        unsafe {
            SNAPSHOT_CPU_STATE = CpuState {
                pc: conc_state.pc,
                cycle: conc_state.cycle,
                regs: conc_state.regs,
            };
            eprintln!("{:#?}", SNAPSHOT_CPU_STATE);
        }

        SNAPSHOT_MEM.with(|rc| {
            *rc.borrow_mut() = conc_state.mem;
        });
    }

    pub fn save_snapshot() {
        use std::fs::{self, File};
        use std::io::Write;
        use serde::Serialize;
        use sym_proof::advice;

        #[derive(Serialize)]
        struct Snapshot {
            pc: Word,
            cycle: Word,
            regs: Vec<Word>,
            mem: Vec<(Addr, Word)>,
        }

        let cpu = unsafe { &SNAPSHOT_CPU_STATE };
        let snap = Snapshot {
            pc: cpu.pc,
            cycle: cpu.cycle,
            regs: cpu.regs[..].to_owned(),
            mem: SNAPSHOT_MEM_ADVICE.with(|rc| rc.take()),
        };

        let dir = advice::advice_dir();
        fs::create_dir_all(&dir).unwrap();
        let mut f = File::create(dir.join("hardcoded_snapshot.cbor")).unwrap();
        serde_cbor::to_writer(f, &snap).unwrap();
    }
}
#[cfg(all(not(feature = "microram_hardcoded_snapshot"), not(feature = "microram")))]
use self::emulate_snapshot::{init_snapshot, SNAPSHOT_CPU_STATE};

#[cfg(all(not(feature = "microram_hardcoded_snapshot"), feature = "microram"))]
#[no_mangle]
extern "C" fn cc_load_snapshot_word(addr: u64) -> u64 {
    assert!(addr % mem::size_of::<u64>() as u64 == 0);
    unsafe { ptr::read_volatile(addr as usize as *mut u64) }
}
#[cfg(all(not(feature = "microram_hardcoded_snapshot"), feature = "microram"))]
extern "C" {
    #[link_name = "__spontaneous_jump_state"]
    static mut SNAPSHOT_CPU_STATE: CpuState;
}
#[cfg(all(not(feature = "microram_hardcoded_snapshot"), feature = "microram"))]
unsafe fn init_snapshot() {}


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
        let f = File::open(advice::advice_dir().join("linear.cbor")).unwrap();
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
    #[cfg(not(feature = "microram_hardcoded_snapshot"))]
    emulate_snapshot::save_snapshot();
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
    unsafe { init_snapshot() };

    secret_decls::validate();

    let prog = Program::new(&program::PROG_INSTRS, &program::PROG_CHUNKS);


    // ----------------------------------------
    // Set up the proof state
    // ----------------------------------------

    let mut pf = Proof::new(prog);


    // Set up initial proof context
    //
    // Unlike `proof_grit`, we don't wrap these in `advice::dont_record`.  In `proof_grit`, we want
    // to avoid recording the rule application.  Here, the rule application has already been
    // omitted, but we'd like to record any `Term`s, `AVec`s, etc. that may show up during the
    // application of this rule.

    // Arithmetic lemmas.

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
    let ok = min_cycles >= 1000;
    if !ok {
        fail();
    }

    exit();
}

#[cfg(not(feature = "microram"))]
fn main() {
    env_logger::init();
    unsafe { emulate_advice::load_advice() };
    run();
}

#[cfg(feature = "microram")]
#[no_mangle]
#[inline(never)]
pub extern "C" fn __spontaneous_jump_dest() {
    run();
}

#[cfg(all(feature = "microram", feature = "microram_hardcoded_snapshot"))]
#[no_mangle]
pub extern "C" fn main() {
    __spontaneous_jump_dest();
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
