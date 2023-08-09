use std::collections::HashMap;
use std::fs;
use std::iter;
use std::path::Path;
use witness_checker::mode::if_mode::{self, Mode};
use witness_checker::micro_ram::types::{self, VersionedMultiExec, ExecBody, RamInstr, RamState};
use crate::{Addr, Word, BinOp, WORD_BYTES};
use crate::micro_ram::{Instr, Opcode, MemWidth, Reg, Operand, NUM_REGS, State};


pub fn with_globals<R>(f: impl FnOnce() -> R) -> R {
    unsafe {
        if_mode::with_mode(Mode::MemorySafety, f)
    }
}

pub fn load_exec<P: AsRef<Path>>(path: P) -> ExecBody {
    let path = path.as_ref();
    let content = fs::read(path).unwrap();
    let parse_exec: VersionedMultiExec = match path.extension().and_then(|os| os.to_str()) {
        Some("yaml") => serde_yaml::from_slice(&content).unwrap(),
        Some("cbor") => serde_cbor::from_slice(&content).unwrap(),
        Some("json") => serde_json::from_slice(&content).unwrap(),
        _ => serde_cbor::from_slice(&content).unwrap(),
    };
    parse_exec.validate().unwrap();

    let mut multi_exec = parse_exec.inner;
    assert_eq!(multi_exec.execs.len(), 1);
    assert_eq!(multi_exec.mem_equiv.len(), 0);
    let (_, exec) = multi_exec.execs.into_iter().next().unwrap();

    assert!(exec.params.num_regs <= NUM_REGS);

    exec
}

pub fn convert_code(exec: &ExecBody) -> HashMap<Addr, Instr> {
    let mut m = HashMap::new();
    for cs in &exec.program {
        let base_addr = cs.start as Addr;
        for (i, &ram_instr) in cs.instrs.iter().enumerate() {
            let addr = base_addr + i as Addr;
            let instr = convert_instr(ram_instr).unwrap_or_else(|| {
                panic!("bad instr (opcode = {:?}) at {}", ram_instr.opcode(), addr);
            });
            let old = m.insert(addr, instr);
            assert!(old.is_none(), "code segment {} overlaps existing segment at {}", i, addr);
        }
    }
    m
}

pub fn convert_instr(ram_instr: RamInstr) -> Option<Instr> {
    let opcode = convert_opcode(ram_instr.opcode())?;
    let rd = ram_instr.dest;
    let r1 = ram_instr.op1;
    let op2 = if ram_instr.imm {
        Operand::Imm(ram_instr.op2)
    } else {
        Operand::Reg(ram_instr.op2 as Reg)
    };
    Some(Instr { opcode, rd, r1, op2 })
}

pub fn convert_opcode(ram_opcode: types::Opcode) -> Option<Opcode> {
    Some(match ram_opcode {
        types::Opcode::And => Opcode::Binary(BinOp::And),
        types::Opcode::Or => Opcode::Binary(BinOp::Or),
        types::Opcode::Xor => Opcode::Binary(BinOp::Xor),
        types::Opcode::Not => Opcode::Not,
        types::Opcode::Add => Opcode::Binary(BinOp::Add),
        types::Opcode::Sub => Opcode::Binary(BinOp::Sub),
        types::Opcode::Mull => Opcode::Binary(BinOp::Mull),
        types::Opcode::Umulh => Opcode::Binary(BinOp::Umulh),
        types::Opcode::Smulh => Opcode::Binary(BinOp::Smulh),
        types::Opcode::Udiv => Opcode::Binary(BinOp::Udiv),
        types::Opcode::Umod => Opcode::Binary(BinOp::Umod),
        types::Opcode::Shl => Opcode::Binary(BinOp::Shl),
        types::Opcode::Shr => Opcode::Binary(BinOp::Shr),

        types::Opcode::Cmpe => Opcode::Binary(BinOp::Cmpe),
        types::Opcode::Cmpa => Opcode::Binary(BinOp::Cmpa),
        types::Opcode::Cmpae => Opcode::Binary(BinOp::Cmpae),
        types::Opcode::Cmpg => Opcode::Binary(BinOp::Cmpg),
        types::Opcode::Cmpge => Opcode::Binary(BinOp::Cmpge),

        types::Opcode::Mov => Opcode::Mov,
        types::Opcode::Cmov => Opcode::Cmov,

        types::Opcode::Jmp => Opcode::Jmp,
        types::Opcode::Cjmp => Opcode::Cjmp,
        types::Opcode::Cnjmp => Opcode::Cnjmp,

        types::Opcode::Store1 => Opcode::Store(MemWidth::W1),
        types::Opcode::Store2 => Opcode::Store(MemWidth::W2),
        types::Opcode::Store4 => Opcode::Store(MemWidth::W4),
        types::Opcode::Store8 => Opcode::Store(MemWidth::W8),
        types::Opcode::Load1 => Opcode::Load(MemWidth::W1),
        types::Opcode::Load2 => Opcode::Load(MemWidth::W2),
        types::Opcode::Load4 => Opcode::Load(MemWidth::W4),
        types::Opcode::Load8 => Opcode::Load(MemWidth::W8),
        types::Opcode::Poison8 => Opcode::Poison(MemWidth::W8),

        types::Opcode::Read => return None,
        types::Opcode::Answer => Opcode::Answer,

        types::Opcode::Advise => Opcode::Advise,

        types::Opcode::Sink1 => return None,
        types::Opcode::Taint1 => return None,

        types::Opcode::Stutter => return None,
    })
}

pub fn convert_mem(exec: &ExecBody) -> HashMap<Addr, Word> {
    let mut m = HashMap::new();
    for ms in &exec.init_mem {
        let base_addr = ms.start as Addr * WORD_BYTES;
        let words = ms.data.iter().copied().chain(iter::repeat(0)).take(ms.len as usize);
        for (i, val) in words.enumerate() {
            let addr = base_addr + i as Addr * WORD_BYTES;
            let old = m.insert(addr, val);
            assert!(old.is_none(), "memory segment {} overlaps existing segment at {}", i, addr);
        }
    }
    m
}

pub fn convert_init_state(exec: &ExecBody) -> State {
    let ram_state = exec.provided_init_state.clone().unwrap_or_else(|| exec.initial_state());
    let mut state = convert_ram_state(&ram_state);
    state.mem = convert_mem(exec);
    state
}

/// Convert a `RamState`.  Note `RamState` doesn't include the state of memory, so the output's
/// `mem` field will be empty.
pub fn convert_ram_state(ram_state: &RamState) -> State {
    let pc = ram_state.pc;
    let mut regs = [0; NUM_REGS];
    regs[..ram_state.regs.len()].copy_from_slice(&ram_state.regs);
    let mem = Default::default();
    State { pc, cycle: 0, regs, mem }
}
