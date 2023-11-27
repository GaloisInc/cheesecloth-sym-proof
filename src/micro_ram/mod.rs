use core::convert::TryFrom;
use std::collections::HashMap;
use core::ops::Index;
use crate::{Word, WORD_BYTES, Addr, BinOp};


pub mod import;


pub type Reg = u8;

#[derive(Clone, Copy, Debug)]
pub struct Instr {
    pub opcode: Opcode,
    pub rd: Reg,
    pub r1: Reg,
    pub op2: Operand,
}

#[derive(Clone, Copy, Debug)]
pub enum Operand {
    Reg(Reg),
    Imm(Word),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Opcode {
    Binary(BinOp),
    Not,
    Mov,
    Cmov,
    Jmp,
    Cjmp,
    Cnjmp,
    Store(MemWidth),
    Load(MemWidth),
    Answer,
    Poison(MemWidth),
    Advise,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum MemWidth {
    W1,
    W2,
    W4,
    W8,
}

impl MemWidth {
    pub const WORD: MemWidth = MemWidth::W8;

    pub fn bytes(self) -> Word {
        match self {
            MemWidth::W1 => 1,
            MemWidth::W2 => 2,
            MemWidth::W4 => 4,
            MemWidth::W8 => 8,
        }
    }
}


#[derive(Clone, Copy, Debug)]
pub struct Program<'a> {
    instrs: &'a [Instr],
    chunks: &'a [ProgramChunk],
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ProgramChunk {
    /// Starting address in memory.
    pub start_addr: Word,
    /// Starting index in the `Program::instrs` array.
    pub start_index: usize,
    /// Number of instructions in this chunk.
    pub len: usize,
}

impl<'a> Program<'a> {
    pub fn new(instrs: &'a [Instr], chunks: &'a [ProgramChunk]) -> Program<'a> {
        dbg!(instrs.len());
        eprintln!("chunks = {chunks:?}");
        #[cfg(debug_assertions)] {
            // Chunks must be sorted and nonoverlapping.
            for (c1, c2) in chunks.iter().zip(chunks.iter().skip(1)) {
                let c1_len = Addr::try_from(c1.len).unwrap();
                let c1_end = c1.start_addr.checked_add(c1_len).unwrap();
                assert!(c1_end <= c2.start_addr, "chunks are out of order: {:?}, {:?}", c1, c2);
            }

            // The last chunk must not wrap around the end of the address space.
            if let Some(c) = chunks.last() {
                let c_len = Addr::try_from(c.len).unwrap();
                assert!(c.start_addr.checked_add(c_len).is_some());
            }

            // Every chunk's `start_index` and `len` must be in bounds for `instrs`.
            for c in chunks {
                let end_index = c.start_index.checked_add(c.len).unwrap();
                assert!(c.start_index <= instrs.len());
                assert!(end_index <= instrs.len());
            }
        }
        Program { instrs, chunks }
    }

    pub fn len(&self) -> usize {
        self.instrs.len()
    }

    pub fn get(&self, pc: Addr) -> Option<&Instr> {
        let chunk = self.chunks.iter().rfind(|c| c.start_addr <= pc)?;
        // If `try_from` fails, it must be the case that the `offset` would be out of bounds for
        // the chunk, which can't possibly have `len` in excess of `usize::MAX`.
        let offset = usize::try_from(pc - chunk.start_addr).ok()?;
        if offset >= chunk.len {
            return None;
        }
        let index = chunk.start_index + offset;
        Some(&self.instrs[index])
    }
}

impl Index<Addr> for Program<'_> {
    type Output = Instr;
    fn index(&self, pc: Addr) -> &Instr {
        self.get(pc).unwrap_or_else(|| panic!("no instruction at pc = {}", pc))
    }
}


pub const NUM_REGS: usize = 33;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct State {
    pub pc: Addr,
    pub cycle: Word,
    pub regs: [Word; NUM_REGS],
    pub mem: HashMap<Addr, Word>,
}

impl Default for State {
    fn default() -> State {
        State {
            pc: 0,
            cycle: 0,
            regs: [0; NUM_REGS],
            mem: HashMap::new(),
        }
    }
}

impl State {
    fn reg_value(&self, reg: Reg) -> Word {
        self.regs[reg as usize]
    }

    pub fn operand_value(&self, op: Operand) -> Word {
        match op {
            Operand::Reg(r) => self.reg_value(r),
            Operand::Imm(i) => i,
        }
    }

    fn set_reg(&mut self, reg: Reg, val: Word) {
        self.regs[reg as usize] = val;
    }

    fn mem_store(&mut self, w: MemWidth, addr: Addr, val: Word) {
        mem_store(&mut self.mem, w, addr, val);
    }

    fn mem_load(&self, w: MemWidth, addr: Addr) -> Word {
        mem_load(&self.mem, w, addr)
    }

    pub fn step(&mut self, instr: Instr, advice: Option<Word>) {
        let x = self.reg_value(instr.r1);
        let y = self.operand_value(instr.op2);

        match instr.opcode {
            Opcode::Binary(b) => {
                let z = b.eval(x, y);
                self.set_reg(instr.rd, z);
            },
            Opcode::Not => {
                self.set_reg(instr.rd, !y);
            },
            Opcode::Mov => {
                self.set_reg(instr.rd, y);
            },
            Opcode::Cmov => {
                if x != 0 {
                    self.set_reg(instr.rd, y);
                }
            },
            Opcode::Jmp => {
                self.pc = y;
                self.cycle += 1;
                return;
            },
            Opcode::Cjmp => {
                if x != 0 {
                    self.pc = y;
                    self.cycle += 1;
                    return;
                }
            },
            Opcode::Cnjmp => {
                if x == 0 {
                    self.pc = y;
                    self.cycle += 1;
                    return;
                }
            },
            Opcode::Store(w) => {
                self.mem_store(w, y, x);
            },
            Opcode::Load(w) => {
                let z = self.mem_load(w, y);
                self.set_reg(instr.rd, z);
            },
            Opcode::Answer => {
                return;
            },
            Opcode::Poison(w) => {
                // Same as `Store` - we don't track poison.
                self.mem_store(w, y, x);
            },
            Opcode::Advise => {
                let val = advice.unwrap_or_else(|| {
                    eprintln!("warning: missing advice");
                    0
                });
                self.set_reg(instr.rd, val);
            },
        }

        self.pc = self.pc.wrapping_add(1);
        self.cycle += 1;
    }
}


pub fn mem_store(mem: &mut HashMap<Addr, Word>, w: MemWidth, addr: Addr, val: Word) {
    let w = w.bytes();
    assert!(addr % w == 0, "misaligned access at address 0x{:x}", addr);
    debug_assert!(w <= WORD_BYTES);
    if w == WORD_BYTES {
        mem.insert(addr, val);
    } else {
        let offset_mask = WORD_BYTES as Addr - 1;
        let word_addr = addr & !offset_mask;
        let offset = addr & offset_mask;
        let offset_bits = offset * 8;

        let mask = (1 << (8 * w)) - 1;
        let x0 = mem.get(&word_addr).copied().unwrap_or(0);
        let x1 = x0 & !(mask << offset_bits) | ((val & mask) << offset_bits);
        mem.insert(word_addr, x1);
    }
}

pub fn mem_load(mem: &HashMap<Addr, Word>, w: MemWidth, addr: Addr) -> Word {
    let w = w.bytes();
    assert!(addr % w == 0, "misaligned access at address 0x{:x}", addr);
    debug_assert!(w <= WORD_BYTES);
    if w == WORD_BYTES {
        mem.get(&addr).copied().unwrap_or(0)
    } else {
        let offset_mask = WORD_BYTES as Addr - 1;
        let word_addr = addr & !offset_mask;
        let offset = addr & offset_mask;
        let offset_bits = offset * 8;

        let mask = (1 << (8 * w)) - 1;
        let x = mem.get(&word_addr).copied().unwrap_or(0);
        (x >> offset_bits) & mask
    }
}
