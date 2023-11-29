use core::convert::TryFrom;
use core::ops::Index;
use crate::{Word, Addr, BinOp};


#[cfg(not(feature = "microram"))]
pub mod import;
pub mod state;


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
        // TODO: use advice for this lookup
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


pub use self::state::State;
