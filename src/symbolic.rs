use std::collections::HashMap;
use std::fmt::{self, Write as _};
use std::rc::Rc;
use crate::{Word, Addr, BinOp};
use crate::micro_ram::{self, NUM_REGS, Instr, Opcode, MemWidth, Reg, Operand};


pub type VarId = usize;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Term(TermInner);

#[derive(Clone, PartialEq, Eq, Debug)]
enum TermInner {
    Const(Word),
    Var(VarId),
    Not(Rc<Term>),
    Binary(BinOp, Rc<(Term, Term)>),
    Mux(Rc<(Term, Term, Term)>),
}

impl Term {
    pub fn const_(x: Word) -> Term {
        Term(TermInner::Const(x))
    }

    pub fn as_const(&self) -> Option<Word> {
        match self.0 {
            TermInner::Const(x) => Some(x),
            _ => None,
        }
    }

    pub fn as_const_or_err(&self) -> Result<Word, String> {
        match self.0 {
            TermInner::Const(x) => Ok(x),
            ref t => Err(format!("expected const, but got {}", t)),
        }
    }

    pub fn not(t: Term) -> Term {
        if let Some(x) = t.as_const() {
            Term::const_(!x)
        } else {
            Term(TermInner::Not(Rc::new(t)))
        }
    }

    pub fn binary(op: BinOp, a: Term, b: Term) -> Term {
        if let (Some(x), Some(y)) = (a.as_const(), b.as_const()) {
            Term::const_(op.eval(x, y))
        } else {
            Term(TermInner::Binary(op, Rc::new((a, b))))
        }
    }

    pub fn mux(c: Term, t: Term, e: Term) -> Term {
        if let Some(c) = c.as_const() {
            if c != 0 {
                t
            } else {
                e
            }
        } else {
            Term(TermInner::Mux(Rc::new((c, t, e))))
        }
    }

    pub fn and(a: Term, b: Term) -> Term { Term::binary(BinOp::And, a, b) }
    pub fn or(a: Term, b: Term) -> Term { Term::binary(BinOp::Or, a, b) }
    pub fn xor(a: Term, b: Term) -> Term { Term::binary(BinOp::Xor, a, b) }
    pub fn add(a: Term, b: Term) -> Term { Term::binary(BinOp::Add, a, b) }
    pub fn sub(a: Term, b: Term) -> Term { Term::binary(BinOp::Sub, a, b) }
    pub fn mull(a: Term, b: Term) -> Term { Term::binary(BinOp::Mull, a, b) }
    pub fn umulh(a: Term, b: Term) -> Term { Term::binary(BinOp::Umulh, a, b) }
    pub fn smulh(a: Term, b: Term) -> Term { Term::binary(BinOp::Smulh, a, b) }
    pub fn udiv(a: Term, b: Term) -> Term { Term::binary(BinOp::Udiv, a, b) }
    pub fn umod(a: Term, b: Term) -> Term { Term::binary(BinOp::Umod, a, b) }
    pub fn shl(a: Term, b: Term) -> Term { Term::binary(BinOp::Shl, a, b) }
    pub fn shr(a: Term, b: Term) -> Term { Term::binary(BinOp::Shr, a, b) }
    pub fn cmpe(a: Term, b: Term) -> Term { Term::binary(BinOp::Cmpe, a, b) }
    pub fn cmpa(a: Term, b: Term) -> Term { Term::binary(BinOp::Cmpa, a, b) }
    pub fn cmpae(a: Term, b: Term) -> Term { Term::binary(BinOp::Cmpae, a, b) }
    pub fn cmpg(a: Term, b: Term) -> Term { Term::binary(BinOp::Cmpg, a, b) }
    pub fn cmpge(a: Term, b: Term) -> Term { Term::binary(BinOp::Cmpge, a, b) }
}

impl From<Word> for Term {
    fn from(x: Word) -> Term { Term::const_(x) }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for TermInner {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TermInner::Const(x) => write!(f, "{}", x),
            TermInner::Var(v) => write!(f, "x{}", v),
            TermInner::Not(ref t) => write!(f, "!{}", t),
            TermInner::Binary(op, ref xy) => {
                let (ref x, ref y) = **xy;
                match op {
                    BinOp::And => write!(f, "({} & {})", x, y),
                    BinOp::Or => write!(f, "({} | {})", x, y),
                    BinOp::Xor => write!(f, "({} ^ {})", x, y),
                    BinOp::Add => write!(f, "({} + {})", x, y),
                    BinOp::Sub => write!(f, "({} - {})", x, y),
                    BinOp::Mull => write!(f, "({} * {})", x, y),
                    BinOp::Umulh => write!(f, "umulh({}, {})", x, y),
                    BinOp::Smulh => write!(f, "smulh({}, {})", x, y),
                    BinOp::Udiv => write!(f, "({} / {})", x, y),
                    BinOp::Umod => write!(f, "({} % {})", x, y),
                    BinOp::Shl => write!(f, "({} << {})", x, y),
                    BinOp::Shr => write!(f, "({} >> {})", x, y),
                    BinOp::Cmpe => write!(f, "({} == {})", x, y),
                    BinOp::Cmpa => write!(f, "({} >u {})", x, y),
                    BinOp::Cmpae => write!(f, "({} >=u {})", x, y),
                    BinOp::Cmpg => write!(f, "({} >s {})", x, y),
                    BinOp::Cmpge => write!(f, "({} >=s {})", x, y),
                }
            },
            TermInner::Mux(ref cte) => write!(f, "mux({}, {}, {})", cte.0, cte.1, cte.2),
        }
    }
}


#[derive(Clone, Debug)]
pub struct VarCounter(VarId);

impl VarCounter {
    pub fn new() -> VarCounter {
        VarCounter(0)
    }

    pub fn var(&mut self) -> Term {
        let t = Term(TermInner::Var(self.0));
        self.0 += 1;
        t
    }
}


#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Pred {
    Nonzero(Term),
    Eq(Term, Term),
    /// `start <= x < end`
    InRange { x: Term, start: Term, end: Term },
}

impl fmt::Display for Pred {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Pred::Nonzero(ref t) => write!(f, "nonzero({})", t),
            Pred::Eq(ref a, ref b) => write!(f, "eq({}, {})", a, b),
            Pred::InRange { ref x, ref start, ref end } =>
                write!(f, "inrange({}, {}, {})", x, start, end),
        }
    }
}



#[derive(Clone, Debug)]
pub struct State {
    pub var_counter: VarCounter,
    pub pc: Word,
    pub regs: [Term; NUM_REGS],
    pub mem: MemState,
    pub preds: Vec<Pred>,
}

#[derive(Clone, Debug)]
pub enum MemState {
    Concrete(MemConcrete),
    Map(MemMap),
    Snapshot(MemSnapshot),
    Log(MemLog),
    Multi(MemMulti),
}

#[derive(Clone, Debug)]
pub struct MemConcrete {
    pub m: HashMap<Addr, Word>,
    pub max: Addr,
}

#[derive(Clone, Debug)]
pub struct MemMap {
    /// Map from byte address to value.  Each value is a single byte extracted from a `Word`-sized
    /// `Term`.  The `u8` gives the index of the byte in little-endian order.
    pub m: HashMap<Addr, (Term, u8)>,
    pub max: Addr,
}

#[derive(Clone, Debug)]
pub struct MemSnapshot {
    pub base: Addr,
}

#[derive(Clone, Debug)]
pub struct MemLog {
    pub l: Vec<(Term, Term, MemWidth)>,
}

/// Multiple disjoint regions of memory, each with a separate `MemState` representation.  Adding a
/// new region is legal only if it's provably disjoint from all existing regions.
///
/// When accessing a region, the region's base address is subtracted before accessing the child
/// `MemState`.  This allows things like using `MemConcrete` in a symbolic-base `objs` entry: the
/// symbolic base address is subtracted out, and the `MemConcrete` is accessed only at a concrete
/// offset.
#[derive(Clone, Debug)]
pub struct MemMulti {
    /// Memory regions with concrete bounds.  Each entry is `(start, end, mem)`.
    pub conc: Vec<(u64, u64, MemState)>,
    /// Memory objects with symbolic addresses but concrete sizes.  Each entry is `(start, len,
    /// mem)`.
    pub objs: Vec<(VarId, u64, MemState)>,
    /// Fully symbolic memory regions.  Each entry is `(start, end, mem)`.
    pub sym: Vec<(Term, Term, MemState)>,
}


pub trait Memory {
    /// Store to a concrete address.
    fn store_concrete(&mut self, w: MemWidth, addr: Addr, val: Term) -> Result<(), String>;
    fn load_concrete(&self, w: MemWidth, addr: Addr) -> Result<Term, String>;

    fn store(&mut self, w: MemWidth, addr: Term, val: Term) -> Result<(), String>;
    fn load(&self, w: MemWidth, addr: Term) -> Result<Term, String>;
}

impl Memory for MemState {
    fn store_concrete(&mut self, w: MemWidth, addr: Addr, val: Term) -> Result<(), String> {
        match *self {
            MemState::Concrete(ref mut m) => m.store_concrete(w, addr, val),
            MemState::Map(ref mut m) => m.store_concrete(w, addr, val),
            MemState::Snapshot(ref mut m) => m.store_concrete(w, addr, val),
            MemState::Log(ref mut m) => m.store_concrete(w, addr, val),
            MemState::Multi(ref mut m) => m.store_concrete(w, addr, val),
        }
    }
    fn load_concrete(&self, w: MemWidth, addr: Addr) -> Result<Term, String> {
        match *self {
            MemState::Concrete(ref m) => m.load_concrete(w, addr),
            MemState::Map(ref m) => m.load_concrete(w, addr),
            MemState::Snapshot(ref m) => m.load_concrete(w, addr),
            MemState::Log(ref m) => m.load_concrete(w, addr),
            MemState::Multi(ref m) => m.load_concrete(w, addr),
        }
    }

    fn store(&mut self, w: MemWidth, addr: Term, val: Term) -> Result<(), String> {
        match *self {
            MemState::Concrete(ref mut m) => m.store(w, addr, val),
            MemState::Map(ref mut m) => m.store(w, addr, val),
            MemState::Snapshot(ref mut m) => m.store(w, addr, val),
            MemState::Log(ref mut m) => m.store(w, addr, val),
            MemState::Multi(ref mut m) => m.store(w, addr, val),
        }
    }
    fn load(&self, w: MemWidth, addr: Term) -> Result<Term, String> {
        match *self {
            MemState::Concrete(ref m) => m.load(w, addr),
            MemState::Map(ref m) => m.load(w, addr),
            MemState::Snapshot(ref m) => m.load(w, addr),
            MemState::Log(ref m) => m.load(w, addr),
            MemState::Multi(ref m) => m.load(w, addr),
        }
    }
}

impl Memory for MemConcrete {
    fn store_concrete(&mut self, w: MemWidth, addr: Addr, val: Term) -> Result<(), String> {
        if addr >= self.max {
            return Err(format!("address 0x{:x} out of range; max is 0x{:x}", addr, self.max));
        }
        let val = val.as_const_or_err()
            .map_err(|e| format!("in MemConcrete::store_concrete: {e}"))?;
        micro_ram::mem_store(&mut self.m, w, addr, val);
        Ok(())
    }
    fn load_concrete(&self, w: MemWidth, addr: Addr) -> Result<Term, String> {
        if addr >= self.max {
            return Err(format!("address 0x{:x} out of range; max is 0x{:x}", addr, self.max));
        }
        let val = micro_ram::mem_load(&self.m, w, addr);
        Ok(Term::const_(val))
    }

    fn store(&mut self, w: MemWidth, addr: Term, val: Term) -> Result<(), String> {
        let addr = addr.as_const_or_err()
            .map_err(|e| format!("when evaluating addr: {e}"))?;
        self.store_concrete(w, addr, val)
    }
    fn load(&self, w: MemWidth, addr: Term) -> Result<Term, String> {
        let addr = addr.as_const_or_err()
            .map_err(|e| format!("when evaluating addr: {e}"))?;
        self.load_concrete(w, addr)
    }
}

impl Memory for MemMap {
    fn store_concrete(&mut self, w: MemWidth, addr: Addr, val: Term) -> Result<(), String> {
        todo!("MemMap NYI")
    }
    fn load_concrete(&self, w: MemWidth, addr: Addr) -> Result<Term, String> {
        todo!("MemMap NYI")
    }

    fn store(&mut self, w: MemWidth, addr: Term, val: Term) -> Result<(), String> {
        todo!("MemMap NYI")
    }
    fn load(&self, w: MemWidth, addr: Term) -> Result<Term, String> {
        todo!("MemMap NYI")
    }
}

impl Memory for MemSnapshot {
    fn store_concrete(&mut self, w: MemWidth, addr: Addr, val: Term) -> Result<(), String> {
        todo!("MemSnapshot NYI")
    }
    fn load_concrete(&self, w: MemWidth, addr: Addr) -> Result<Term, String> {
        todo!("MemSnapshot NYI")
    }

    fn store(&mut self, w: MemWidth, addr: Term, val: Term) -> Result<(), String> {
        todo!("MemSnapshot NYI")
    }
    fn load(&self, w: MemWidth, addr: Term) -> Result<Term, String> {
        todo!("MemSnapshot NYI")
    }
}

impl Memory for MemLog {
    fn store_concrete(&mut self, w: MemWidth, addr: Addr, val: Term) -> Result<(), String> {
        self.store(w, Term::const_(addr), val)
    }
    fn load_concrete(&self, w: MemWidth, addr: Addr) -> Result<Term, String> {
        Err("MemLog load_concrete NYI".into())
    }

    fn store(&mut self, w: MemWidth, addr: Term, val: Term) -> Result<(), String> {
        self.l.push((addr, val, w));
        Ok(())
    }
    fn load(&self, w: MemWidth, addr: Term) -> Result<Term, String> {
        Err("MemLog load NYI".into())
    }
}

impl Memory for MemMulti {
    fn store_concrete(&mut self, w: MemWidth, addr: Addr, val: Term) -> Result<(), String> {
        let &mut (start, end, ref mut mem) = self.conc.iter_mut()
            .find(|&&mut (start, end, _)| start <= addr && addr + w.bytes() <= end)
            .ok_or_else(|| format!("address 0x{addr:x} does not fall within a concrete region"))?;
        let off = addr - start;
        mem.store_concrete(w, off, val)
    }

    fn load_concrete(&self, w: MemWidth, addr: Addr) -> Result<Term, String> {
        let &(start, end, ref mem) = self.conc.iter()
            .find(|&&(start, end, _)| start <= addr && addr + w.bytes() <= end)
            .ok_or_else(|| format!("address 0x{addr:x} does not fall within a concrete region"))?;
        let off = addr - start;
        mem.load_concrete(w, off)
    }

    fn store(&mut self, w: MemWidth, addr: Term, val: Term) -> Result<(), String> {
        todo!("MemMulti NYI")
    }
    fn load(&self, w: MemWidth, addr: Term) -> Result<Term, String> {
        todo!("MemMulti NYI")
    }
}


impl State {
    pub fn new(
        var_counter: VarCounter,
        pc: Word,
        regs: [Term; NUM_REGS],
        mem: MemState,
        preds: Vec<Pred>,
    ) -> State {
        // TODO: make sure var_counter and VarIds in terms match up
        State { var_counter, pc, regs, mem, preds }
    }

    pub fn pc(&self) -> Word {
        self.pc
    }

    pub fn regs(&self) -> &[Term; NUM_REGS] {
        &self.regs
    }

    pub fn mem(&self) -> &MemState {
        &self.mem
    }

    pub fn preds(&self) -> &[Pred] {
        &self.preds
    }

    pub fn reg_value(&self, reg: Reg) -> Term {
        self.regs[reg as usize].clone()
    }

    pub fn operand_value(&self, op: Operand) -> Term {
        match op {
            Operand::Reg(r) => self.reg_value(r),
            Operand::Imm(i) => Term::const_(i),
        }
    }

    pub fn set_reg(&mut self, reg: Reg, val: Term) {
        self.regs[reg as usize] = val;
    }
}
