use std::collections::HashSet;
use std::fmt;
use std::rc::Rc;
use crate::BinOp;
use super::{VarId, Term, TermKind, Prop, ReachableProp, StatePred, Binder, VarCounter};



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

        // Skip printing the memory state for now
        write!(f, " /\\ MEM")?;

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


/*
/// Helper for displaying the "forall x," or "exists y," part of a `Binder`.  Note that the
/// `Display` impl prints only the variable bindings, not the inner value.
struct DisplayBinder<'a> {
    vars: &'a VarCounter,
    mode: DisplayBinderMode,
}

enum DisplayBinderMode {
    Forall,
    Exists,
}

impl<'a> DisplayBinder<'a> {
    fn forall<T>(b: &'a Binder<T>) -> DisplayBinder<'a> {
        DisplayBinder {
            vars: &b.vars,
            mode: DisplayBinderMode::Forall,
        }
    }

    fn exists<T>(b: &'a Binder<T>) -> DisplayBinder<'a> {
        DisplayBinder {
            vars: &b.vars,
            mode: DisplayBinderMode::Exists,
        }
    }
}

impl fmt::Display for DisplayBinderMode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            DisplayBinderMode::Forall => write!(f, "forall"),
            DisplayBinderMode::Exists => write!(f, "exists"),
        }
    }
}

impl<'a> fmt::Display for DisplayBinder<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.vars.len() {
            0 => Ok(()),
            1 => {
                let v = VarId::new(self.vars.scope(), 0);
                write!(f, "{} {}, ", self.mode, v)
            },
            n => {
                let v0 = VarId::new(self.vars.scope(), 0);
                let vn = VarId::new(self.vars.scope(), n as u32 - 1);
                write!(f, "{} {} .. {}, ", self.mode, v0, vn)
            },
        }
    }
}


impl fmt::Display for StepProp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f, "{{{}}} ->({}) {{{}}}",
            DisplayBinderStatePred(&self.pre),
            self.min_cycles,
            DisplayBinderStatePred(&self.post),
        )
    }
}

struct DisplayBinderStatePred<'a>(&'a Binder<StatePred>);

impl fmt::Display for DisplayBinderStatePred<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", DisplayBinder::exists(self.0))?;
        write!(f, "pc = {}", self.0.inner.state.pc)?;

        let mut vars_mentioned_in_props = HashSet::new();
        for p in &self.0.inner.props {
            p.for_each_var(&mut |v| -> Option<()> {
                vars_mentioned_in_props.insert(v);
                None
            });
        }
        let exists_scope = self.0.vars.scope();
        let has_constrained_var = |t: &Term| {
            t.for_each_var(&mut |v| {
                if vars_mentioned_in_props.contains(&v) || v.scope() != exists_scope {
                    Some(())
                } else {
                    None
                }
            }).is_some()
        };

        for (i, t) in self.0.inner.state.regs.iter().enumerate() {
            if let Some(v) = t.as_var() {
                if v.scope() == exists_scope && !vars_mentioned_in_props.contains(&v) {
                    continue;
                }
            }
            write!(f, " /\\ r{} = {}", i, t)?;
        }

        for p in &self.0.inner.props {
            write!(f, " /\\ {}", p)?;
        }

        // Skip printing the memory state for now
        write!(f, " /\\ MEM")?;

        Ok(())
    }
}

impl fmt::Display for ReachableProp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f, "{{init}} ->({}) {{{}}}",
            self.min_cycles,
            DisplayBinderStatePred(&self.pred),
        )
    }
}
*/
