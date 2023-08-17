use std::array;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;
use crate::{Word, WORD_BYTES, Addr, BinOp};
use crate::micro_ram::{self, NUM_REGS, MemWidth, Reg, Operand};
use crate::logic::{Term, VarId, Subst, Prop};
use crate::logic::fold::{Fold, Folder};


pub trait Memory {
    fn store(&mut self, w: MemWidth, addr: Term, val: Term, props: &[Prop]) -> Result<(), String>;
    fn load(&self, w: MemWidth, addr: Term, props: &[Prop]) -> Result<Term, String>;
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
    fn store(&mut self, w: MemWidth, addr: Term, val: Term, props: &[Prop]) -> Result<(), String> {
        match *self {
            MemState::Concrete(ref mut m) => m.store(w, addr, val, props),
            MemState::Map(ref mut m) => m.store(w, addr, val, props),
            MemState::Snapshot(ref mut m) => m.store(w, addr, val, props),
            MemState::Log(ref mut m) => m.store(w, addr, val, props),
            MemState::Multi(ref mut m) => m.store(w, addr, val, props),
        }
    }
    fn load(&self, w: MemWidth, addr: Term, props: &[Prop]) -> Result<Term, String> {
        match *self {
            MemState::Concrete(ref m) => m.load(w, addr, props),
            MemState::Map(ref m) => m.load(w, addr, props),
            MemState::Snapshot(ref m) => m.load(w, addr, props),
            MemState::Log(ref m) => m.load(w, addr, props),
            MemState::Multi(ref m) => m.load(w, addr, props),
        }
    }
}

#[derive(Clone, Debug)]
pub struct MemConcrete {
    pub m: HashMap<Addr, Word>,
    pub max: Addr,
}

impl Memory for MemConcrete {
    fn store(&mut self, w: MemWidth, addr: Term, val: Term, _props: &[Prop]) -> Result<(), String> {
        let addr = addr.as_const_or_err()
            .map_err(|e| format!("when evaluating addr: {e}"))?;
        if addr + w.bytes() >= self.max {
            return Err(format!("address 0x{:x} out of range; max is 0x{:x}", addr, self.max));
        }
        let val = val.as_const_or_err()
            .map_err(|e| format!("in MemConcrete::store: {e}"))?;
        micro_ram::mem_store(&mut self.m, w, addr, val);
        Ok(())
    }
    fn load(&self, w: MemWidth, addr: Term, _props: &[Prop]) -> Result<Term, String> {
        let addr = addr.as_const_or_err()
            .map_err(|e| format!("when evaluating addr: {e}"))?;
        if addr + w.bytes() >= self.max {
            return Err(format!("address 0x{:x} out of range; max is 0x{:x}", addr, self.max));
        }
        let val = micro_ram::mem_load(&self.m, w, addr);
        Ok(Term::const_(val))
    }
}

#[derive(Clone, Debug)]
pub struct MemMap {
    /// Map from byte address to value.  Each value is a single byte extracted from a `Word`-sized
    /// `Term`.  The `u8` gives the index of the byte to extract in little-endian order.
    pub m: HashMap<Addr, (Term, u8)>,
    pub max: Addr,
}

impl Memory for MemMap {
    fn store(&mut self, w: MemWidth, addr: Term, val: Term, _props: &[Prop]) -> Result<(), String> {
        let addr = addr.as_const_or_err()
            .map_err(|e| format!("when evaluating addr: {e}"))?;
        if addr + w.bytes() >= self.max {
            return Err(format!("address 0x{:x} out of range; max is 0x{:x}", addr, self.max));
        }
        for offset in 0 .. w.bytes() {
            self.m.insert(addr + offset, (val.clone(), offset as u8));
        }
        Ok(())
    }

    fn load(&self, w: MemWidth, addr: Term, _props: &[Prop]) -> Result<Term, String> {
        let addr = addr.as_const_or_err()
            .map_err(|e| format!("when evaluating addr: {e}"))?;
        if addr + w.bytes() >= self.max {
            return Err(format!("address 0x{:x} out of range; max is 0x{:x}", addr, self.max));
        }

        // We currently require the load to match a store exactly, so each consecutive address must
        // contain the next consecutive byte in order (starting from zero), and all bytes should be
        // extracted from the same expression.
        let val = match self.m.get(&addr) {
            Some(&(ref t, offset)) => {
                if offset != 0 {
                    return Err(format!("NYI: load requires splicing bytes: \
                        at 0x{:x}, got offset {}, but expected 0", addr, offset));
                }
                t
            },
            None => {
                return Err(format!("failed to load from address 0x{:x}: uninitialized data",
                    addr));
            },
        };

        for offset in 1 .. w.bytes() {
            match self.m.get(&(addr + offset)) {
                Some(&(ref t, loaded_offset)) => {
                    if loaded_offset != offset as u8 {
                        return Err(format!("NYI: load requires splicing bytes: \
                            at 0x{:x}, got offset {}, but expected {}",
                            addr + offset, loaded_offset, offset));
                    }
                    if t != val {
                        return Err(format!("NYI: load requires splicing bytes: \
                            at 0x{:x}, got term {}, but expected {}",
                            addr + offset, t, val));
                    }
                },
                None => {
                    return Err(format!("failed to load from address 0x{:x}: uninitialized data",
                        addr + offset));
                },
            }
        }

        let mut val = val.clone();
        if w.bytes() < WORD_BYTES {
            val = Term::and(val, Term::const_((1 << (8 * w.bytes())) - 1));
        }

        Ok(val)
    }
}

#[derive(Clone, Debug)]
pub struct MemSnapshot {
    pub base: Addr,
}

impl Memory for MemSnapshot {
    fn store(&mut self, w: MemWidth, addr: Term, val: Term, _props: &[Prop]) -> Result<(), String> {
        let _ = (w, addr, val);
        todo!("MemSnapshot NYI")
    }
    fn load(&self, w: MemWidth, addr: Term, _props: &[Prop]) -> Result<Term, String> {
        let _ = (w, addr);
        todo!("MemSnapshot NYI")
    }
}

#[derive(Clone, Debug)]
pub struct MemLog {
    pub l: Vec<(Term, Term, MemWidth)>,
}

impl Memory for MemLog {
    fn store(&mut self, w: MemWidth, addr: Term, val: Term, _props: &[Prop]) -> Result<(), String> {
        self.l.push((addr, val, w));
        Ok(())
    }
    fn load(&self, w: MemWidth, addr: Term, _props: &[Prop]) -> Result<Term, String> {
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

enum MemRegionKind {
    Concrete,
    Object,
    Symbolic,
}

impl MemMulti {
    fn region(&self, kind: MemRegionKind, i: usize) -> &MemState {
        match kind {
            MemRegionKind::Concrete => &self.conc[i].2,
            MemRegionKind::Object => &self.objs[i].2,
            MemRegionKind::Symbolic => &self.sym[i].2,
        }
    }

    fn region_mut(&mut self, kind: MemRegionKind, i: usize) -> &mut MemState {
        match kind {
            MemRegionKind::Concrete => &mut self.conc[i].2,
            MemRegionKind::Object => &mut self.objs[i].2,
            MemRegionKind::Symbolic => &mut self.sym[i].2,
        }
    }

    fn find_region(&self, addr: Term, props: &[Prop]) -> Option<(Term, MemRegionKind, usize)> {
        if let Some(addr) = addr.as_const() {
            for (i, &(start, end, _)) in self.conc.iter().enumerate() {
                if start <= addr && addr < end {
                    return Some((Term::const_(addr - start), MemRegionKind::Concrete, i));
                }
            }
        }

        if let Some((var, offset)) = addr.as_var_plus_const() {
            for (i, &(base, len, _)) in self.objs.iter().enumerate() {
                if var == base && offset < len {
                    return Some((Term::const_(offset), MemRegionKind::Object, i));
                }
            }
        }

        // General case: look for predicates showing that `addr` falls within the range.
        let region_iter =
            self.conc.iter().enumerate().map(|(i, &(start, end, _))| {
                (Term::const_(start), Term::const_(end), MemRegionKind::Concrete, i)
            })
            .chain(self.objs.iter().enumerate().map(|(i, &(var, len, _))| {
                let var = Term::var_unchecked(var);
                (var.clone(), Term::add(var, Term::const_(len)), MemRegionKind::Object, i)
            }))
            .chain(self.sym.iter().enumerate().map(|(i, &(ref start, ref end, _))| {
                (start.clone(), end.clone(), MemRegionKind::Symbolic, i)
            }));
        for (start, end, kind, i) in region_iter {
            let lo = Prop::Nonzero(Term::cmpae(addr.clone(), start.clone()));
            let hi = Prop::Nonzero(Term::cmpa(end, addr.clone()));
            let found_lo = props.iter().any(|p| lo.check_eq(p));
            let found_hi = props.iter().any(|p| hi.check_eq(p));
            if found_lo && found_hi {
                return Some((Term::sub(addr, start), kind, i));
            }
        }

        None
    }
}

impl Memory for MemMulti {
    fn store(&mut self, w: MemWidth, addr: Term, val: Term, props: &[Prop]) -> Result<(), String> {
        let (offset, kind, i) = match self.find_region(addr.clone(), props) {
            Some(x) => x,
            None => return Err(format!("couldn't find a region containing address {}", addr)),
        };
        self.region_mut(kind, i).store(w, offset, val, props)
    }
    fn load(&self, w: MemWidth, addr: Term, props: &[Prop]) -> Result<Term, String> {
        let (offset, kind, i) = match self.find_region(addr.clone(), props) {
            Some(x) => x,
            None => return Err(format!("couldn't find a region containing address {}", addr)),
        };
        self.region(kind, i).load(w, offset, props)
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
    pub regs: [Term; NUM_REGS],
    pub mem: MemState,
}

impl State {
    pub fn new(
        pc: Word,
        regs: [Term; NUM_REGS],
        mem: MemState,
    ) -> State {
        State { pc, regs, mem }
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

    pub fn subst<S: Subst>(&self, subst: &mut S) -> State {
        if S::IS_IDENTITY {
            return self.clone();
        }

        // FIXME: substitute mem
        eprintln!("ADMITTED: State::subst memory substitution");

        State {
            pc: self.pc,
            regs: array::from_fn(|i| self.regs[i].subst(subst)),
            mem: self.mem.clone(),
        }
    }

    pub fn check_eq(&self, other: &State) -> bool {
        eprintln!("ADMITTED: MemState check_eq");
        self.pc == other.pc
            && self.regs == other.regs
    }

    /*
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

        // FIXME: check mem
        eprintln!("ADMITTED: State::check_eq_concrete memory check");

        Ok(())
    }
    */
}

impl Fold for State {
    fn fold_with<F: Folder + ?Sized>(&self, f: &mut F) -> Self {
        let State { pc, ref regs, ref mem } = *self;
        State {
            pc,
            regs: regs.fold_with(f),
            mem: {
                eprintln!("ADMITTED: Fold for MemState ({})", std::any::type_name::<F>());
                mem.clone()
            },
        }
    }
}
