use std::rc::Rc;
use crate::{Word, BinOp};
use crate::logic::VarId;
use crate::logic::print::Printer;


/// An expression producing a value of type `Word`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Term(TermKind);

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TermKind {
    Const(Word),
    Var(VarId),
    Not(Rc<Term>),
    Binary(BinOp, Rc<(Term, Term)>),
    Mux(Rc<(Term, Term, Term)>),
}

impl Term {
    pub fn kind(&self) -> &TermKind {
        &self.0
    }

    pub fn const_(x: Word) -> Term {
        Term(TermKind::Const(x))
    }

    pub fn is_const(&self) -> bool {
        self.as_const().is_some()
    }

    pub fn as_const(&self) -> Option<Word> {
        match self.0 {
            TermKind::Const(x) => Some(x),
            _ => None,
        }
    }

    pub fn as_const_or_err(&self) -> Result<Word, String> {
        match self.0 {
            TermKind::Const(x) => Ok(x),
            ref t => Err(format!("expected const, but got {}", Printer::new(0).display(t))),
        }
    }

    /// Create a new `Var` with a specific `VarId`.  There are no checks to ensure that the `VarId`
    /// makes sense in context.  For generating fresh variables, use `VarCounter` instead.
    pub fn var_unchecked(v: VarId) -> Term {
        Term(TermKind::Var(v))
    }

    pub fn as_var(&self) -> Option<VarId> {
        match self.0 {
            TermKind::Var(v) => Some(v),
            _ => None,
        }
    }

    pub fn not(t: Term) -> Term {
        if let Some(x) = t.as_const() {
            Term::const_(!x)
        } else {
            Term(TermKind::Not(Rc::new(t)))
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
                if a.is_const() && !b.is_const() {
                    return Term::add(b, a);
                }
                // When adding to an existing `x + c`, fold the constants together.
                if let Some(bc) = b.as_const() {
                    if bc == 0 {
                        return a;
                    }
                    if let TermKind::Binary(BinOp::Add, ref xy) = a.0 {
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
            BinOp::Mull => {
                // Put the constant on the right whenever possible.
                if a.is_const() && !b.is_const() {
                    return Term::mull(b, a);
                }
                // Turn `(x + y) * c` into `x * c + y * c` if either `x` or `y` is a constant.
                if let Some(bc) = b.as_const() {
                    if bc == 0 {
                        return Term::const_(0);
                    }
                    if let TermKind::Binary(BinOp::Add, ref xy) = a.0 {
                        let (ref x, ref y) = **xy;
                        if x.is_const() || y.is_const() {
                            return Term::add(
                                Term::mull(x.clone(), b.clone()),
                                Term::mull(y.clone(), b.clone()),
                            );
                        }
                    }
                }
            },
            _ => {},
        }

        Term(TermKind::Binary(op, Rc::new((a, b))))
    }

    pub fn mux(c: Term, t: Term, e: Term) -> Term {
        if let Some(c) = c.as_const() {
            if c != 0 {
                t
            } else {
                e
            }
        } else {
            Term(TermKind::Mux(Rc::new((c, t, e))))
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
        if let TermKind::Binary(BinOp::Add, ref args) = a.0 {
            let (ref b, ref m) = **args;
            if let Some(m) = m.as_const() {
                return Term::add(b.clone(), Term::const_(n + m));
            }
        }
        Term::add(a, Term::const_(n))
    }

    /* TODO: using a slice for `vars` doesn't work with multiple var scopes
    pub fn eval(&self, vars: &[Word]) -> Word {
        match self.0 {
            TermKind::Var(v) => vars[v],
            TermKind::Const(x) => x,
            TermKind::Not(ref a) => !a.eval(vars),
            TermKind::Binary(op, ref ab) => {
                let (ref a, ref b) = **ab;
                op.eval(a.eval(vars), b.eval(vars))
            },
            TermKind::Mux(ref cte) => {
                let (ref c, ref t, ref e) = **cte;
                if c.eval(vars) != 0 {
                    t.eval(vars)
                } else {
                    e.eval(vars)
                }
            },
        }
    }
    */

    pub fn as_var_plus_const(&self) -> Option<(VarId, Word)> {
        match self.0 {
            TermKind::Var(v) => Some((v, 0)),
            TermKind::Binary(BinOp::Add, ref xy) => {
                let v = xy.0.as_var()?;
                let c = xy.1.as_const()?;
                Some((v, c))
            },
            _ => None,
        }
    }

    /// Apply `f` to each `VarId` mentioned in `self`.  `f` should return `None` to keep traversing
    /// or `Some(x)` to break out; in the latter case, the return value of `for_each_var` will also
    /// be `Some(x)`.
    pub fn for_each_var<T>(&self, f: &mut impl FnMut(VarId) -> Option<T>) -> Option<T> {
        match self.0 {
            TermKind::Const(_) => None,
            TermKind::Var(v) => {
                f(v)
            },
            TermKind::Not(ref t) => {
                t.for_each_var(f)
            },
            TermKind::Binary(_, ref ts) => {
                let (ref t1, ref t2) = **ts;
                t1.for_each_var(f)
                    .or_else(|| t2.for_each_var(f))
            },
            TermKind::Mux(ref ts) => {
                let (ref t1, ref t2, ref t3) = **ts;
                t1.for_each_var(f)
                    .or_else(|| t2.for_each_var(f))
                    .or_else(|| t3.for_each_var(f))
            },
        }
    }
}

impl From<Word> for Term {
    fn from(x: Word) -> Term { Term::const_(x) }
}
