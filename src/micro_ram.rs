use std::collections::HashMap;
use std::mem;
use crate::{Word, WORD_BYTES, WORD_BITS, Addr, BinOp};


type Reg = u8;

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

#[derive(Clone, Copy, Debug)]
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

#[derive(Clone, Copy, Debug)]
pub enum MemWidth {
    W1,
    W2,
    W4,
    W8,
}

impl MemWidth {
    pub fn bytes(self) -> Word {
        match self {
            MemWidth::W1 => 1,
            MemWidth::W2 => 2,
            MemWidth::W4 => 4,
            MemWidth::W8 => 8,
        }
    }
}


pub const NUM_REGS: usize = 33;

#[derive(Clone, Debug)]
struct State {
    pub pc: Addr,
    pub regs: [Word; NUM_REGS],
    pub mem: HashMap<Addr, Word>,
}

impl Default for State {
    fn default() -> State {
        State {
            pc: 0,
            regs: [0; NUM_REGS],
            mem: HashMap::new(),
        }
    }
}

impl State {
    fn reg_value(&self, reg: Reg) -> Word {
        self.regs[reg as usize]
    }

    fn operand_value(&self, op: Operand) -> Word {
        match op {
            Operand::Reg(r) => self.reg_value(r),
            Operand::Imm(i) => i,
        }
    }

    fn set_reg(&mut self, reg: Reg, val: Word) {
        self.regs[reg as usize] = val;
    }

    fn mem_store(&mut self, w: MemWidth, addr: Addr, val: Word) {
        let w = w.bytes();
        assert!(addr % w == 0, "misaligned access at address 0x{:x}", addr);
        debug_assert!(w <= WORD_BYTES);
        if w == WORD_BYTES {
            self.mem.insert(addr, val);
        } else {
            let offset_mask = WORD_BYTES as Addr - 1;
            let word_addr = addr & !offset_mask;
            let offset = addr & offset_mask;
            let offset_bits = offset * 8;

            let mask = (1 << (8 * w)) - 1;
            let x0 = self.mem.get(&word_addr).copied().unwrap_or(0);
            let x1 = x0 & !(mask << offset_bits) | ((val & mask) << offset_bits);
            self.mem.insert(word_addr, x1);
        }
    }

    fn mem_load(&mut self, w: MemWidth, addr: Addr) -> Word {
        let w = w.bytes();
        assert!(addr % w == 0, "misaligned access at address 0x{:x}", addr);
        debug_assert!(w <= WORD_BYTES);
        if w == WORD_BYTES {
            self.mem.get(&addr).copied().unwrap_or(0)
        } else {
            let offset_mask = WORD_BYTES as Addr - 1;
            let word_addr = addr & !offset_mask;
            let offset = addr & offset_mask;
            let offset_bits = offset * 8;

            let mask = (1 << (8 * w)) - 1;
            let x = self.mem.get(&word_addr).copied().unwrap_or(0);
            (x >> offset_bits) & mask
        }
    }

    pub fn step(&mut self, instr: Instr) {
        let x = self.reg_value(instr.r1);
        let y = self.operand_value(instr.op2);

        match instr.opcode {
            Opcode::Binary(b) => {
                let z = match b {
                    BinOp::And => x & y,
                    BinOp::Or => x | y,
                    BinOp::Xor => x ^ y,
                    BinOp::Add => x.wrapping_add(y),
                    BinOp::Sub => x.wrapping_sub(y),
                    BinOp::Mull => x.wrapping_mul(y),
                    BinOp::Umulh => {
                        debug_assert_eq!(mem::size_of::<Word>(), 8);
                        let xx = x as u128;
                        let yy = y as u128;
                        let zz = xx * yy;
                        zz as u64
                    },
                    BinOp::Smulh => {
                        debug_assert_eq!(mem::size_of::<Word>(), 8);
                        let xx = x as i64 as i128;
                        let yy = y as i64 as i128;
                        let zz = xx * yy;
                        zz as u64
                    },
                    BinOp::Udiv => {
                        if y == 0 { 0 } else { x / y }
                    },
                    BinOp::Umod => {
                        if y == 0 { x } else { x / y }
                    },
                    BinOp::Shl => {
                        if y >= WORD_BITS { 0 } else { x << y as u32 }
                    },
                    BinOp::Shr => {
                        if y >= WORD_BITS { 0 } else { x >> y as u32 }
                    },
                    BinOp::Cmpe => (x == y) as Word,
                    BinOp::Cmpa => (x > y) as Word,
                    BinOp::Cmpae => (x >= y) as Word,
                    BinOp::Cmpg => ((x as i64) > (y as i64)) as Word,
                    BinOp::Cmpge => ((x as i64) >= (y as i64)) as Word,
                };
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
                return;
            },
            Opcode::Cjmp => {
                if x != 0 {
                    self.pc = y;
                    return;
                }
            },
            Opcode::Cnjmp => {
                if x == 0 {
                    self.pc = y;
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
                // Always provide zero as the advice.  This happens to work for the `advise`
                // instruction in `malloc`.
                self.set_reg(instr.rd, 0);
            },
        }

        self.pc = self.pc.wrapping_add(1);
    }
}
