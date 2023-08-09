use std::array;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;
use crate::{Word, Addr, BinOp};
use crate::micro_ram::{self, NUM_REGS, MemWidth, Reg, Operand};


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

    pub fn is_const(&self) -> bool {
        self.as_const().is_some()
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
            return Term::const_(op.eval(x, y));
        }

        // Normalization rules
        match op {
            BinOp::Add => {
                // Put the constant on the right whenever possible.
                if matches!(a.0, TermInner::Const(_)) {
                    return Term::add(b, a);
                }
                // When adding to an existing `x + c`, fold the constants together.
                if let Some(bc) = b.as_const() {
                    if bc == 0 {
                        return a;
                    }
                    if let TermInner::Binary(BinOp::Add, ref xy) = a.0 {
                        let (ref x, ref y) = **xy;
                        if let Some(yc) = y.as_const() {
                            return Term::add(x.clone(), Term::const_(bc.wrapping_add(yc)));
                        }
                    }
                }
            },
            BinOp::Sub => {
                // Turn `x - c` into `x + (-c)`.
                if let Some(bc) = b.as_const() {
                    if bc == 0 {
                        return a;
                    }
                    return Term::add(a, Term::const_(bc.wrapping_neg()));
                }
            },
            _ => {},
        }

        Term(TermInner::Binary(op, Rc::new((a, b))))
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

    /// Build the term `a + n`.  If `a` has the form `b + m` where `m` is a constant, this folds
    /// the two additions together into `b + (n + m)`.
    pub fn increment(a: Term, n: Word) -> Term {
        if let TermInner::Binary(BinOp::Add, ref args) = a.0 {
            let (ref b, ref m) = **args;
            if let Some(m) = m.as_const() {
                return Term::add(b.clone(), Term::const_(n + m));
            }
        }
        Term::add(a, Term::const_(n))
    }

    pub fn subst<S: Subst>(&self, subst: &mut S) -> Term {
        if S::IS_IDENTITY {
            return self.clone();
        }

        match self.0 {
            TermInner::Var(v) => subst.subst(v).clone(),
            TermInner::Const(x) => Term::const_(x),
            TermInner::Not(ref a) => Term::not(a.subst(subst)),
            TermInner::Binary(op, ref ab) => {
                let (ref a, ref b) = **ab;
                Term::binary(op, a.subst(subst), b.subst(subst))
            },
            TermInner::Mux(ref abc) => {
                let (ref a, ref b, ref c) = **abc;
                Term::mux(a.subst(subst), b.subst(subst), c.subst(subst))
            },
        }
    }

    /// Substitute the variables of `a` using `a_subst`, substitute the variables of `b` using
    /// `b_subst`, and check if the resulting terms are equal.  This avoids constructing the
    /// intermediate terms when possible.
    pub fn check_eq_subst<AS, BS>(a: &Term, a_subst: &mut AS, b: &Term, b_subst: &mut BS) -> bool
    where AS: Subst, BS: Subst {
        match (&a.0, &b.0) {
            // Substitution cases.  We skip calling `subst` when `IS_IDENTITY` is set.
            (&TermInner::Var(av), &TermInner::Var(bv)) if !AS::IS_IDENTITY && !BS::IS_IDENTITY => {
                a_subst.subst(av) == b_subst.subst(bv)
            },
            (&TermInner::Var(av), _) if !AS::IS_IDENTITY =>
                Term::check_eq_subst(a_subst.subst(av), &mut IdentitySubsts::new(), b, b_subst),
            (_, &TermInner::Var(bv)) if !BS::IS_IDENTITY =>
                Term::check_eq_subst(a, a_subst, b_subst.subst(bv), &mut IdentitySubsts::new()),

            (&TermInner::Const(ax), &TermInner::Const(bx)) => ax == bx,
            // This `Var` case is only reachable when both `Subst`s are the identity.
            (&TermInner::Var(av), &TermInner::Var(bv)) => av == bv,
            (&TermInner::Not(ref at), &TermInner::Not(ref bt)) =>
                Term::check_eq_subst(at, a_subst, bt, b_subst),
            (&TermInner::Binary(a_op, ref ats), &TermInner::Binary(b_op, ref bts)) => {
                let (ref at1, ref at2) = **ats;
                let (ref bt1, ref bt2) = **bts;
                a_op == b_op
                    && Term::check_eq_subst(at1, a_subst, bt1, b_subst)
                    && Term::check_eq_subst(at2, a_subst, bt2, b_subst)
            },
            (&TermInner::Mux(ref ats), &TermInner::Mux(ref bts)) => {
                let (ref at1, ref at2, ref at3) = **ats;
                let (ref bt1, ref bt2, ref bt3) = **bts;
                Term::check_eq_subst(at1, a_subst, bt1, b_subst)
                    && Term::check_eq_subst(at2, a_subst, bt2, b_subst)
                    && Term::check_eq_subst(at3, a_subst, bt3, b_subst)
            },

            _ => false,
        }
    }

    pub fn eval(&self, vars: &[Word]) -> Word {
        match self.0 {
            TermInner::Var(v) => vars[v],
            TermInner::Const(x) => x,
            TermInner::Not(ref a) => !a.eval(vars),
            TermInner::Binary(op, ref ab) => {
                let (ref a, ref b) = **ab;
                op.eval(a.eval(vars), b.eval(vars))
            },
            TermInner::Mux(ref cte) => {
                let (ref c, ref t, ref e) = **cte;
                if c.eval(vars) != 0 {
                    t.eval(vars)
                } else {
                    e.eval(vars)
                }
            },
        }
    }
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
            TermInner::Const(x) => write!(f, "{}", x as i64),
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


pub trait Subst {
    const IS_IDENTITY: bool;
    fn subst(&mut self, v: VarId) -> &Term;
}

pub struct IdentitySubsts {
    storage: Term,
}

impl IdentitySubsts {
    pub fn new() -> IdentitySubsts {
        IdentitySubsts {
            storage: Term(TermInner::Var(0)),
        }
    }
}

impl Subst for IdentitySubsts {
    const IS_IDENTITY: bool = true;
    fn subst(&mut self, v: VarId) -> &Term {
        self.storage = Term(TermInner::Var(v));
        &self.storage
    }
}

pub struct SubstTable<F> {
    cache: Vec<Option<Term>>,
    f: F,
}

impl<F> SubstTable<F> {
    pub fn new(f: F) -> SubstTable<F> {
        SubstTable {
            cache: Vec::new(),
            f,
        }
    }
}

impl<F: FnMut(VarId) -> Term> Subst for SubstTable<F> {
    const IS_IDENTITY: bool = false;
    fn subst(&mut self, v: VarId) -> &Term {
        if v >= self.cache.len() {
            self.cache.resize_with(v + 1, || None);
        }
        if self.cache[v].is_none() {
            self.cache[v] = Some((self.f)(v));
        }
        self.cache[v].as_ref().unwrap()
    }
}


#[derive(Clone, Debug)]
pub struct VarCounter(VarId);

impl VarCounter {
    pub fn new() -> VarCounter {
        VarCounter(0)
    }

    pub fn fresh(&mut self) -> Term {
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

impl Pred {
    pub fn subst<S: Subst>(&self, subst: &mut S) -> Pred {
        if S::IS_IDENTITY {
            return self.clone();
        }

        match *self {
            Pred::Nonzero(ref t) => Pred::Nonzero(t.subst(subst)),
            Pred::Eq(ref a, ref b) => Pred::Eq(a.subst(subst), b.subst(subst)),
            Pred::InRange { ref x, ref start, ref end } => Pred::InRange {
                x: x.subst(subst),
                start: start.subst(subst),
                end: end.subst(subst),
            },
        }
    }

    pub fn check_eq_subst<AS, BS>(a: &Pred, a_subst: &mut AS, b: &Pred, b_subst: &mut BS) -> bool
    where AS: Subst, BS: Subst {
        match (a, b) {
            (&Pred::Nonzero(ref a1), &Pred::Nonzero(ref b1)) =>
                Term::check_eq_subst(a1, a_subst, b1, b_subst),
            (&Pred::Eq(ref a1, ref a2), &Pred::Eq(ref b1, ref b2)) =>
                Term::check_eq_subst(a1, a_subst, b1, b_subst)
                    && Term::check_eq_subst(a2, a_subst, b2, b_subst),
            (
                &Pred::InRange { x: ref a1, start: ref a2, end: ref a3 },
                &Pred::InRange { x: ref b1, start: ref b2, end: ref b3 },
            ) =>
                Term::check_eq_subst(a1, a_subst, b1, b_subst)
                    && Term::check_eq_subst(a2, a_subst, b2, b_subst)
                    && Term::check_eq_subst(a3, a_subst, b3, b_subst),

            _ => false,
        }
    }

    pub fn eval(&self, vars: &[Word]) -> bool {
        match *self {
            Pred::Nonzero(ref t) => t.eval(vars) != 0,
            Pred::Eq(ref a, ref b) => a.eval(vars) == b.eval(vars),
            Pred::InRange { ref x, ref start, ref end } => {
                let x = x.eval(vars);
                let start = start.eval(vars);
                let end = end.eval(vars);
                start <= x && x < end
            },
        }
    }
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


pub trait Memory {
    /// Store to a concrete address.
    fn store_concrete(&mut self, w: MemWidth, addr: Addr, val: Term) -> Result<(), String>;
    fn load_concrete(&self, w: MemWidth, addr: Addr) -> Result<Term, String>;

    fn store(&mut self, w: MemWidth, addr: Term, val: Term) -> Result<(), String>;
    fn load(&self, w: MemWidth, addr: Term) -> Result<Term, String>;
}

#[derive(Clone, Debug)]
pub enum MemState {
    Concrete(MemConcrete),
    Map(MemMap),
    Snapshot(MemSnapshot),
    Log(MemLog),
    Multi(MemMulti),
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

#[derive(Clone, Debug)]
pub struct MemConcrete {
    pub m: HashMap<Addr, Word>,
    pub max: Addr,
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

#[derive(Clone, Debug)]
pub struct MemMap {
    /// Map from byte address to value.  Each value is a single byte extracted from a `Word`-sized
    /// `Term`.  The `u8` gives the index of the byte in little-endian order.
    pub m: HashMap<Addr, (Term, u8)>,
    pub max: Addr,
}

impl Memory for MemMap {
    fn store_concrete(&mut self, w: MemWidth, addr: Addr, val: Term) -> Result<(), String> {
        let _ = (w, addr, val);
        todo!("MemMap NYI")
    }
    fn load_concrete(&self, w: MemWidth, addr: Addr) -> Result<Term, String> {
        let _ = (w, addr);
        todo!("MemMap NYI")
    }

    fn store(&mut self, w: MemWidth, addr: Term, val: Term) -> Result<(), String> {
        let _ = (w, addr, val);
        todo!("MemMap NYI")
    }
    fn load(&self, w: MemWidth, addr: Term) -> Result<Term, String> {
        let _ = (w, addr);
        todo!("MemMap NYI")
    }
}

#[derive(Clone, Debug)]
pub struct MemSnapshot {
    pub base: Addr,
}

impl Memory for MemSnapshot {
    fn store_concrete(&mut self, w: MemWidth, addr: Addr, val: Term) -> Result<(), String> {
        let _ = (w, addr, val);
        todo!("MemSnapshot NYI")
    }
    fn load_concrete(&self, w: MemWidth, addr: Addr) -> Result<Term, String> {
        let _ = (w, addr);
        todo!("MemSnapshot NYI")
    }

    fn store(&mut self, w: MemWidth, addr: Term, val: Term) -> Result<(), String> {
        let _ = (w, addr, val);
        todo!("MemSnapshot NYI")
    }
    fn load(&self, w: MemWidth, addr: Term) -> Result<Term, String> {
        let _ = (w, addr);
        todo!("MemSnapshot NYI")
    }
}

#[derive(Clone, Debug)]
pub struct MemLog {
    pub l: Vec<(Term, Term, MemWidth)>,
}

impl Memory for MemLog {
    fn store_concrete(&mut self, w: MemWidth, addr: Addr, val: Term) -> Result<(), String> {
        self.store(w, Term::const_(addr), val)
    }
    fn load_concrete(&self, w: MemWidth, addr: Addr) -> Result<Term, String> {
        let _ = (w, addr);
        Err("MemLog load_concrete NYI".into())
    }

    fn store(&mut self, w: MemWidth, addr: Term, val: Term) -> Result<(), String> {
        self.l.push((addr, val, w));
        Ok(())
    }
    fn load(&self, w: MemWidth, addr: Term) -> Result<Term, String> {
        let _ = (w, addr);
        Err("MemLog load NYI".into())
    }
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

impl Memory for MemMulti {
    fn store_concrete(&mut self, w: MemWidth, addr: Addr, val: Term) -> Result<(), String> {
        let &mut (start, _end, ref mut mem) = self.conc.iter_mut()
            .find(|&&mut (start, end, _)| start <= addr && addr + w.bytes() <= end)
            .ok_or_else(|| format!("address 0x{addr:x} does not fall within a concrete region"))?;
        let off = addr - start;
        mem.store_concrete(w, off, val)
    }

    fn load_concrete(&self, w: MemWidth, addr: Addr) -> Result<Term, String> {
        let &(start, _end, ref mem) = self.conc.iter()
            .find(|&&(start, end, _)| start <= addr && addr + w.bytes() <= end)
            .ok_or_else(|| format!("address 0x{addr:x} does not fall within a concrete region"))?;
        let off = addr - start;
        mem.load_concrete(w, off)
    }

    fn store(&mut self, w: MemWidth, addr: Term, val: Term) -> Result<(), String> {
        let _ = (w, addr, val);
        todo!("MemMulti NYI")
    }
    fn load(&self, w: MemWidth, addr: Term) -> Result<Term, String> {
        let _ = (w, addr);
        todo!("MemMulti NYI")
    }
}


/// A predicate on program states.  The predicate is parameterized over some variables `xs`, which
/// can be referenced using `Term::var` in the register or memory `Term`s.
///
/// A concrete state `s` satisfies the predicate when:
/// * `s.pc == self.pc`, and
/// * for all `i`, `s.regs[i] == eval(self.regs[i], xs)`, and
/// * `s.mem` satisfies the predicate `self.mem`.
///
/// TODO: Clarify details of the memory predicate
#[derive(Clone, Debug)]
pub struct State {
    pub pc: Word,
    pub cycle: Term,
    pub regs: [Term; NUM_REGS],
    pub mem: MemState,
}

impl State {
    pub fn new(
        pc: Word,
        cycle: Term,
        regs: [Term; NUM_REGS],
        mem: MemState,
    ) -> State {
        State { pc, cycle, regs, mem }
    }

    pub fn pc(&self) -> Word {
        self.pc
    }

    pub fn cycle(&self) -> &Term {
        &self.cycle
    }

    pub fn regs(&self) -> &[Term; NUM_REGS] {
        &self.regs
    }

    pub fn mem(&self) -> &MemState {
        &self.mem
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

    pub fn increment_cycle(&mut self) {
        self.cycle = Term::increment(self.cycle.clone(), 1);
    }

    pub fn subst<S: Subst>(&self, subst: &mut S) -> State {
        if S::IS_IDENTITY {
            return self.clone();
        }

        // FIXME: substitute mem
        eprintln!("ADMITTED: State::subst memory substitution");

        State {
            pc: self.pc,
            cycle: self.cycle.subst(subst),
            regs: array::from_fn(|i| self.regs[i].subst(subst)),
            mem: self.mem.clone(),
        }
    }

    pub fn check_eq_concrete(&self, vars: &[Word], conc: &micro_ram::State) -> Result<(), String> {
        if self.pc != conc.pc {
            return Err(format!("pc {} does not match concrete pc {}",
                self.pc, conc.pc));
        }

        for (i, (sym_reg, &conc_reg)) in self.regs.iter().zip(conc.regs.iter()).enumerate() {
            let sym_reg_val = sym_reg.eval(vars);
            if sym_reg_val != conc_reg {
                return Err(format!("symbolic r{} {} = {} does not match concrete r{} {}",
                    i, sym_reg, sym_reg_val, i, conc_reg));
            }
        }

        let cycle = self.cycle.eval(vars);
        if cycle != conc.cycle {
            return Err(format!("symbolic cycle {} = {} does not match concrete cycle {}",
                self.cycle, cycle, conc.cycle));
        }

        // FIXME: check mem
        eprintln!("ADMITTED: State::check_eq_concrete memory check");

        Ok(())
    }
}
