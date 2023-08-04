use std::collections::HashMap;
use std::mem;

use crate::micro_ram::NUM_REGS;


pub mod micro_ram;



pub type Word = u64;
pub const WORD_BYTES: Word = mem::size_of::<Word>() as Word;
pub const WORD_BITS: Word = WORD_BYTES * 8;
pub type Addr = Word;
pub type VarId = usize;


#[derive(Clone, Debug)]
pub enum Term {
    Const(Word),
    Var(VarId),
    Not(Box<Term>),
    Binary(BinOp, Box<(Term, Term)>),
    Mux(Box<(Term, Term, Term)>),
}

#[derive(Clone, Copy, Debug)]
pub enum BinOp {
    And,
    Or,
    Xor,
    Add,
    Sub,
    Mull,
    Umulh,
    Smulh,
    Udiv,
    Umod,
    Shl,
    Shr,
    Cmpe,
    Cmpa,
    Cmpae,
    Cmpg,
    Cmpge,
}


struct State {
    regs: [Term; NUM_REGS],
    mem: MemState,
    preds: Vec<Term>,
}

enum MemState {
    Concrete(MemConcrete),
    Map(MemMap),
    Snapshot(MemSnapshot),
    Log(MemLog),
    Multi(MemMulti),
}

struct MemConcrete {
    m: HashMap<Addr, Word>,
    max: Addr,
}

struct MemMap {
    m: HashMap<Addr, Term>,
    max: Addr,
}

struct MemSnapshot {
    base: Addr,
}

struct MemLog {
    l: Vec<(Term, Term)>,
}

/// Multiple disjoint regions of memory, each with a separate `MemState` representation.  Adding a
/// new region is legal only if it's provably disjoint from all existing regions.
///
/// When accessing a region, the region's base address is subtracted before accessing the child
/// `MemState`.  This allows things like using `MemConcrete` in a symbolic-base `objs` entry: the
/// symbolic base address is subtracted out, and the `MemConcrete` is accessed only at a concrete
/// offset.
struct MemMulti {
    /// Memory regions with concrete bounds.  Each entry is `(start, end, mem)`.
    conc: Vec<(u64, u64, MemState)>,
    /// Memory objects with symbolic addresses but concrete sizes.  Each entry is `(start, len, mem)`.
    objs: Vec<(VarId, u64, MemState)>,
    /// Fully symbolic memory regions.  Each entry is `(start, end, mem)`.
    sym: Vec<(Term, Term, MemState)>,
}
