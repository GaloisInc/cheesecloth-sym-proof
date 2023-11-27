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
use std::collections::HashMap;
use std::env;
use env_logger;
use log::trace;
use sym_proof::Addr;
use sym_proof::advice;
use sym_proof::interp;
use sym_proof::kernel::Proof;
use sym_proof::micro_ram::Program;
use sym_proof::micro_ram::import;
use sym_proof::tactics::Tactics;
use witness_checker::micro_ram::types::Advice;

fn run(path: &str) -> Result<(), String> {
    let exec = import::load_exec(path);

    let (instrs, chunks) = import::convert_code_split(&exec);
    let prog = Program::new(&instrs, &chunks);
    eprintln!("loaded code: {} instrs", prog.len());
    let init_state = import::convert_init_state(&exec);
    eprintln!("loaded memory: {} words", init_state.mem.len());
    trace!("initial regs = {:?}", init_state.regs);

    // Load advice
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
    eprintln!("loaded advice");
    
    // ----------------------------------------
    // Run the concrete prefix
    // ----------------------------------------

    let mut conc_state = init_state;
    // LBB831_734#20819 (pc=253846) is near the loop, but slighly after the start.
    let loop_label = ".LBB831_734#20819"; //What about .LBB713_45#19734
    // The loop starts at pc = 253854;
    //]let loop_addr = 253854; //
    let loop_addr = exec.labels[loop_label];
    eprintln!("Starting concrete execution until address: {} ", loop_addr);
    while conc_state.pc != loop_addr {
	let conc_pc : Addr = conc_state.pc;
        let instr = prog[conc_pc];
	let cyc = conc_state.cycle;
	// For some reason the cycle is off by one wrt advice
	let adv:Option<u64> =  advs.get(&(cyc + 1)).cloned();
        conc_state.step(instr, adv);
    }

    eprintln!("STOPed the first run of concrete execution. Pc {}. Cycle {}", conc_state.pc, conc_state.cycle);
    

    // TODO: remmove this looping and make it lean.
    let num_loops = 10;
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
	eprintln!{"Testing the loop: Loop took {} cycles", conc_state.cycle - last_cycle_seen};
	last_cycle_seen = conc_state.cycle;

	for (ri, &x) in conc_state.regs.iter().enumerate() {
	    reg_log[ri][li] = x;
	}
    }

    eprintln!("Log of registers during the loop ");
    for (i, &_x) in conc_state.regs.iter().enumerate() {
        eprintln!("{:2}: {:?}", i, reg_log[i]);
    }


    // ----------------------------------------
    // Set up the proof state
    // ----------------------------------------

    // Load advice first, so `AVec`s inside `Proof` can find their lengths.
    advice::load()?;

    let mut pf = Proof::new(prog);

    // TODO: add initial reach prop to `pf`

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

