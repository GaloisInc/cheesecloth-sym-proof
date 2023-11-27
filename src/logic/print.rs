use std::collections::HashSet;
use std::fmt;
use std::rc::Rc;
use crate::{BinOp, Addr};
use super::{VarId, Term, TermKind, Prop, ReachableProp, StatePred, Binder, VarCounter};
use crate::symbolic::{MemState, MemConcrete, MemMap, MemSnapshot, MemLog, MemMulti};



// Display impls for `Prop` and related types

#[derive(Clone, Debug)]
pub struct Printer {
    scope_depth: u32,
    verbose: bool,
}

impl Printer {
    pub fn new(scope_depth: u32) -> Printer {
        Printer {
            scope_depth,
            verbose: false,
        }
    }

    pub fn verbose(self, verbose: bool) -> Self {
        Printer { verbose, ..self }
    }

    pub fn display<'a, T: Print>(&self, x: &'a T) -> DisplayWithPrinter<'a, T> {
        DisplayWithPrinter { p: self.clone(), x }
    }

    pub fn enter_binder<R>(&self, f: impl FnOnce(&Self) -> R) -> R {
        let inner = Printer {
            scope_depth: self.scope_depth + 1,
            verbose: self.verbose,
        };
        f(&inner)
    }
}

/// Helper function for printing at an unknown binder depth.  This may produce confusing output,
/// since the variable names won't match what you would get with the binder depth set properly.
/// Mainly intended for debug prints and error messages; normal user-facing output goes through
/// `Proof::print`, which sets the binder depth correctly based on the current proof context.
pub fn debug_print<T: Print>(x: &T) -> DisplayWithPrinter<T> {
    Printer::new(0).display(x)
}

pub struct DisplayWithPrinter<'a, T> {
    p: Printer,
    x: &'a T,
}

impl<'a, T: Print> fmt::Display for DisplayWithPrinter<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.x.print(&self.p, f)
    }
}


pub trait Print {
    fn print(&self, p: &Printer, f: &mut fmt::Formatter) -> fmt::Result;
}

impl<T: Print> Print for &'_ T {
    fn print(&self, p: &Printer, f: &mut fmt::Formatter) -> fmt::Result {
        T::print(self, p, f)
    }
}

impl<T: Print> Print for Box<T> {
    fn print(&self, p: &Printer, f: &mut fmt::Formatter) -> fmt::Result {
        T::print(self, p, f)
    }
}

impl<T: Print> Print for Rc<T> {
    fn print(&self, p: &Printer, f: &mut fmt::Formatter) -> fmt::Result {
        T::print(self, p, f)
    }
}

impl Print for VarId {
    fn print(&self, p: &Printer, f: &mut fmt::Formatter) -> fmt::Result {
        let scope = self.scope();
        let index = self.index();
        if scope >= p.scope_depth {
            write!(f, "free_{}_{}", scope - p.scope_depth, index)
        } else {
            let level = p.scope_depth - 1 - scope;
            write!(f, "{}{}", (b'a' + level as u8) as char, index)
        }
    }
}


impl Print for Term {
    fn print(&self, p: &Printer, f: &mut fmt::Formatter) -> fmt::Result {
        self.kind().print(p, f)
    }
}

impl Print for TermKind {
    fn print(&self, p: &Printer, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TermKind::Const(x) => write!(f, "{}", x as i64),
            TermKind::Var(v) => v.print(p, f),
            TermKind::Not(t) => write!(f, "!{}", p.display(&t)),
            TermKind::Binary(op, x, y) => {
                let x = p.display(&x);
                let y = p.display(&y);
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
            TermKind::Mux(c, t, e) => {
                let c = p.display(&c);
                let t = p.display(&t);
                let e = p.display(&e);
                write!(f, "mux({}, {}, {})", c, t, e)
            },
        }
    }
}

impl Print for Prop {
    fn print(&self, p: &Printer, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Prop::Nonzero(t) => t.print(p, f),

            Prop::Forall(ref b) => {
                print_binder(p, f, BinderMode::Forall, &b.vars)?;

                p.enter_binder(|p| {
                    let (ref premises, ref conclusion) = b.inner;

                    for prop in premises.iter() {
                        write!(f, "({}) -> ", p.display(prop))?;
                    }
                    conclusion.print(p, f)
                })
            },

            Prop::Reachable(ref rp) => rp.print(p, f),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum BinderMode {
    Forall,
    Exists,
}

impl fmt::Display for BinderMode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            BinderMode::Forall => write!(f, "forall"),
            BinderMode::Exists => write!(f, "exists"),
        }
    }
}

fn print_binder(
    p: &Printer,
    f: &mut fmt::Formatter,
    mode: BinderMode,
    vars: &VarCounter,
) -> fmt::Result {
    match vars.len() {
        0 => Ok(()),
        1 => {
            p.enter_binder(|p| {
                let v = VarId::new(0, 0);
                write!(f, "{} {}, ", mode, p.display(&v))
            })
        },
        n => {
            p.enter_binder(|p| {
                let v0 = VarId::new(0, 0);
                let vn = VarId::new(0, n as u32 - 1);
                write!(f, "{} {} .. {}, ", mode, p.display(&v0), p.display(&vn))
            })
        },
    }
}

impl Print for ReachableProp {
    fn print(&self, p: &Printer, f: &mut fmt::Formatter) -> fmt::Result {
        let ReachableProp { ref pred, min_cycles } = *self;
        write!(
            f, "reach({}, {{{}}})",
            p.display(&min_cycles),
            p.display(&PrintBinder(BinderMode::Exists, pred)),
        )
    }
}

impl Print for StatePred {
    fn print(&self, p: &Printer, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "pc = {}", self.state.pc)?;

        let mut vars_mentioned_in_props = HashSet::new();
        for p in self.props.iter() {
            p.for_each_var(&mut |v| -> Option<()> {
                vars_mentioned_in_props.insert(v);
                None
            });
        }

        for (i, t) in self.state.regs.iter().enumerate() {
            if let Some(v) = t.as_var() {
                if !p.verbose && v.scope() == 0 && !vars_mentioned_in_props.contains(&v) {
                    // `v` is an unconstrained existential, so register `i` is unconstrained.
                    continue;
                }
            }
            write!(f, " /\\ r{} = {}", i, p.display(t))?;
        }

        for prop in self.props.iter() {
            write!(f, " /\\ {}", p.display(prop))?;
        }

        write!(f, " /\\ ")?;
        self.state.mem.print(p, f)?;

        Ok(())
    }
}

pub struct PrintBinder<'a, T>(pub BinderMode, pub &'a Binder<T>);

impl<'a, T> PrintBinder<'a, T> {
    pub fn forall(b: &'a Binder<T>) -> PrintBinder<'a, T> {
        PrintBinder(BinderMode::Forall, b)
    }

    pub fn exists(b: &'a Binder<T>) -> PrintBinder<'a, T> {
        PrintBinder(BinderMode::Exists, b)
    }
}

impl<'a, T: Print> Print for PrintBinder<'a, T> {
    fn print(&self, p: &Printer, f: &mut fmt::Formatter) -> fmt::Result {
        let PrintBinder(mode, binder) = *self;
        print_binder(p, f, mode, &binder.vars)?;
        p.enter_binder(|p| {
            binder.inner.print(p, f)
        })
    }
}


impl Print for MemState {
    fn print(&self, p: &Printer, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            MemState::Concrete(ref m) => m.print(p, f),
            MemState::Map(ref m) => m.print(p, f),
            MemState::Snapshot(ref m) => m.print(p, f),
            MemState::Log(ref m) => m.print(p, f),
            MemState::Multi(ref m) => m.print(p, f),
        }
    }
}

impl Print for MemConcrete {
    fn print(&self, _p: &Printer, f: &mut fmt::Formatter) -> fmt::Result {
        let mut kvs = self.m.iter().map(|(&k, &v)| (k, v)).collect::<Vec<_>>();
        kvs.sort();
        for (i, (k, v)) in kvs.into_iter().enumerate() {
            if i > 0 {
                write!(f, " /\\ ")?;
            }
            write!(f, "[{:x}] = {}", k, v)?;
        }
        Ok(())
    }
}

impl Print for MemMap {
    fn print(&self, p: &Printer, f: &mut fmt::Formatter) -> fmt::Result {
        let mut first = true;
        let mut emit = |addr: Addr, size: u8, value: Term, base: u8| -> fmt::Result {
            if first {
                first = false;
            } else {
                write!(f, " /\\ ")?;
            }
            if size == 1 {
                write!(f, "[{:x}] = ", addr)?;
            } else {
                write!(f, "[{:x},+{}] = ", addr, size)?;
            }
            if base == 0 {
                value.print(p, f)?;
            } else {
                write!(f, "(")?;
                value.print(p, f)?;
                write!(f, ")>>{}", base)?;
            }
            Ok(())
        };

        let mut addr = 0;
        let mut size = 0;
        let mut value = Term::const_(0);
        let mut base = 0;

        for (&k, &(v, b)) in self.m.iter() {
            if k == addr + size as Addr && v == value && b == base + size {
                size += 1;
            } else {
                emit(addr, size, value, base)?;
                addr = k;
                size = 1;
                value = v;
                base = b;
            }
        }

        if size > 0 {
            emit(addr, size, value, base)?;
        }
        Ok(())
    }
}

impl Print for MemSnapshot {
    fn print(&self, _p: &Printer, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "MemSnapshot @{:x}", self.base)
    }
}

impl Print for MemLog {
    fn print(&self, _p: &Printer, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "MemLog [{} entries]", self.l.len())
    }
}

impl Print for MemMulti {
    fn print(&self, _p: &Printer, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "MemMulti [{} parts]", self.conc.len() + self.objs.len() + self.sym.len())
    }
}
