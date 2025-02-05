use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use serde::{Serialize, Deserialize, Serializer, Deserializer};
use serde::de;
use crate::{Word, WORD_BYTES, Addr};
use crate::micro_ram::{Reg, Operand, Opcode, Instr, MemWidth, NUM_REGS};


#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub struct State {
    pub pc: Addr,
    pub cycle: Word,
    #[serde(serialize_with = "serialize_regs")]
    #[serde(deserialize_with = "deserialize_regs")]
    pub regs: [Word; NUM_REGS],
    pub mem: BTreeMap<Addr, Word>,
}

impl Default for State {
    fn default() -> State {
        State {
            pc: 0,
            cycle: 0,
            regs: [0; NUM_REGS],
            mem: BTreeMap::new(),
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

    pub fn mem_load(&self, w: MemWidth, addr: Addr) -> Word {
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
                    #[cfg(feature = "verbose")] {
                        std::eprintln!("warning: missing advice");
                    }
                    0
                });
                self.set_reg(instr.rd, val);
            },
        }

        self.pc = self.pc.wrapping_add(1);
        self.cycle += 1;
    }
}


pub fn mem_store(mem: &mut BTreeMap<Addr, Word>, w: MemWidth, addr: Addr, val: Word) {
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

pub fn mem_load(mem: &BTreeMap<Addr, Word>, w: MemWidth, addr: Addr) -> Word {
    mem_load_ex(w, addr, |a| mem.get(&a).copied().unwrap_or(0))
}

/// Given a function that loads a whole word from an aligned address, perform a load of arbitrary
/// width from an arbitrary address.
pub fn mem_load_ex(w: MemWidth, addr: Addr, get_word: impl FnOnce(Addr) -> Word) -> Word {
    let w = w.bytes();
    assert!(addr % w == 0, "misaligned access at address 0x{:x}", addr);
    debug_assert!(w <= WORD_BYTES);
    if w == WORD_BYTES {
        get_word(addr)
    } else {
        let offset_mask = WORD_BYTES as Addr - 1;
        let word_addr = addr & !offset_mask;
        let offset = addr & offset_mask;
        let offset_bits = offset * 8;

        let mask = (1 << (8 * w)) - 1;
        let x = get_word(word_addr);
        (x >> offset_bits) & mask
    }
}


fn serialize_regs<S>(regs: &[Word; NUM_REGS], serializer: S) -> Result<S::Ok, S::Error>
where S: Serializer {
    let v = regs.iter().copied().collect::<Vec<_>>();
    v.serialize(serializer)
}

fn deserialize_regs<'de, D>(deserializer: D) -> Result<[Word; NUM_REGS], D::Error>
where D: Deserializer<'de> {
    let v = <Vec<Word>>::deserialize(deserializer)?;
    if v.len() != NUM_REGS {
        return Err(de::Error::invalid_length(
                v.len(), &(&alloc::format!("a list of length {}", NUM_REGS) as &str)));
    }
    let mut arr = [0; NUM_REGS];
    for (x, y) in arr.iter_mut().zip(v.iter()) {
        *x = *y;
    }
    Ok(arr)
}
