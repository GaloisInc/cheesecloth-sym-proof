use std::ops::Deref;
use std::rc::Rc;
use crate::{Word, BinOp};
use crate::logic::fold::Fold;
use crate::logic::print::Printer;
use crate::logic::shift::ShiftExt;
use crate::logic::subst::SubstExt;
use crate::symbolic;


pub mod fold;
pub mod print;
pub mod shift;
pub mod subst;
pub mod visit;
pub mod wf;


#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct VarId(u32);

impl VarId {
    const SCOPE_BITS: u8 = 8;
    const SCOPE_START: u8 = 32 - Self::SCOPE_BITS;
    const SCOPE_MASK: u32 = !0 << Self::SCOPE_START;

    pub const MAX_INDEX: u32 = !0 >> Self::SCOPE_BITS;

    pub fn new(scope: u32, index: u32) -> VarId {
        assert!(index & Self::SCOPE_MASK == 0);
        VarId(index | (scope << Self::SCOPE_START))
    }

    pub fn scope(self) -> u32 {
        self.0 >> Self::SCOPE_START
    }

    pub fn index(self) -> u32 {
        self.0 & !Self::SCOPE_MASK
    }
}


#[derive(Clone, PartialEq, Eq, Debug)]
pub struct VarCounter(VarId);

impl VarCounter {
    pub fn new() -> VarCounter {
        VarCounter(VarId::new(0, 0))
    }

    pub fn fresh_var(&mut self) -> VarId {
        assert!(self.0.index() < VarId::MAX_INDEX);
        let v = self.0;
        self.0.0 = self.0.0.wrapping_add(1);
        v
    }

    pub fn fresh(&mut self) -> Term {
        Term::var_unchecked(self.fresh_var())
    }

    pub fn len(&self) -> usize {
        self.0.index() as usize
    }
}


#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Binder<T> {
    pub vars: VarCounter,
    pub inner: T,
}

impl<T> Binder<T> {
    pub fn from_parts(vars: VarCounter, inner: T) -> Binder<T> {
        Binder { vars, inner }
    }

    pub fn new(f: impl FnOnce(&mut VarCounter) -> T) -> Binder<T> {
        let mut vars = VarCounter::new();
        let inner = f(&mut vars);
        Binder { vars, inner }
    }

    pub fn try_new(
        f: impl FnOnce(&mut VarCounter) -> Result<T, String>,
    ) -> Result<Binder<T>, String> {
        let mut vars = VarCounter::new();
        let inner = f(&mut vars)?;
        Ok(Binder { vars, inner })
    }

    pub fn as_ref(&self) -> Binder<&T> {
        Binder::from_parts(self.vars.clone(), &self.inner)
    }

    pub fn map<'a, F: FnOnce(&'a T) -> U, U>(&'a self, f: F) -> Binder<U> {
        Binder::from_parts(self.vars.clone(), f(&self.inner))
    }

    pub fn iter(self) -> impl Iterator<Item = Binder<<T as IntoIterator>::Item>>
    where T: IntoIterator {
        let vars = self.vars.clone();
        self.inner.into_iter().map(move |x| Binder::from_parts(vars.clone(), x))
    }

    pub fn subst(&self, terms: &[Term]) -> T
    where T: Fold {
        assert_eq!(terms.len(), self.vars.len());
        self.inner.subst(terms)
    }

    /// Like `subst`, but works on `Binder<&T>` instead of `Binder<T>`.
    pub fn subst_ref(&self, terms: &[Term]) -> <T as Deref>::Target
    where T: Deref, <T as Deref>::Target: Fold {
        assert_eq!(terms.len(), self.vars.len());
        self.inner.subst(terms)
    }
}


/// An expression producing a value of type `Word`.
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
            ref t => Err(format!("expected const, but got {}", Printer::new(0).display(t))),
        }
    }

    /// Create a new `Var` with a specific `VarId`.  There are no checks to ensure that the `VarId`
    /// makes sense in context.  For generating fresh variables, use `VarCounter` instead.
    pub fn var_unchecked(v: VarId) -> Term {
        Term(TermInner::Var(v))
    }

    pub fn as_var(&self) -> Option<VarId> {
        match self.0 {
            TermInner::Var(v) => Some(v),
            _ => None,
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
                if a.is_const() && !b.is_const() {
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
                    if let TermInner::Binary(BinOp::Add, ref xy) = a.0 {
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

    /* TODO: using a slice for `vars` doesn't work with multiple var scopes
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
    */

    pub fn as_var_plus_const(&self) -> Option<(VarId, Word)> {
        match self.0 {
            TermInner::Var(v) => Some((v, 0)),
            TermInner::Binary(BinOp::Add, ref xy) => {
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
            TermInner::Const(_) => None,
            TermInner::Var(v) => {
                f(v)
            },
            TermInner::Not(ref t) => {
                t.for_each_var(f)
            },
            TermInner::Binary(_, ref ts) => {
                let (ref t1, ref t2) = **ts;
                t1.for_each_var(f)
                    .or_else(|| t2.for_each_var(f))
            },
            TermInner::Mux(ref ts) => {
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
            storage: Term(TermInner::Var(VarId(0))),
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
    cache: Vec<Vec<Option<Term>>>,
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
        let scope = v.scope() as usize;
        if scope >= self.cache.len() {
            self.cache.resize_with(scope + 1, || Vec::new());
        }
        let index = v.index() as usize;
        if index >= self.cache[scope].len() {
            self.cache[scope].resize_with(index + 1, || None);
        }
        if self.cache[scope][index].is_none() {
            self.cache[scope][index] = Some((self.f)(v));
        }
        self.cache[scope][index].as_ref().unwrap()
    }
}


#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Prop {
    /// `t != 0`
    Nonzero(Term),
    /// `forall xs, Ps(xs) -> Q(xs)`
    Forall(Binder<(Vec<Prop>, Box<Prop>)>),
    /// ```
    /// forall s,
    /// (exists x, pre(s, x)) =>
    /// (exists s' x' n, post(s', x') /\ s ->n s' /\ n >= N)
    /// ```
    Step(StepProp),
    /// `exists s x n, pred(s, x) /\ reachable(s, n) /\ n >= min_cycles`
    Reachable(ReachableProp),
}

/// ```
/// forall s,
/// (exists x, pre(s, x)) =>
/// (exists s' x' n, post(s', x') /\ s ->n s' /\ n >= min_cycles)
/// ```
///
/// `s` and `s'` are not represented specifically; the `forall s` and `exists s'` parts are "built
/// in" so that we don't need to support arbitrary quantification over states (`Prop::Forall` only
/// allows quantifying over `Word`s).  `n` also isn't represented explicitly.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct StepProp {
    pub pre: Binder<StatePred>,
    pub post: Binder<StatePred>,
    /// Note `min_cycles` is not under a binder - it must be expressed in terms of variables
    /// already in scope.
    pub min_cycles: Term,
}

/// ```
/// exists s x n, pred(s, x) /\ reachable(s, n) /\ n >= min_cycles
/// ```
///
/// In other words, there is an execution of length at least `min_cycles` that ends in a state
/// matching `pred`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ReachableProp {
    pub pred: Binder<StatePred>,
    pub min_cycles: Term,
}

/// A predicate `P(s)` on states.  The predicate holds if `s == state` and all `props` hold.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct StatePred {
    pub state: symbolic::State,
    pub props: Vec<Prop>,
}

impl Prop {
    pub fn implies(premises: Vec<Prop>, conclusion: Prop) -> Prop {
        Prop::Forall(Binder::new(|_| (premises.shift(), Box::new(conclusion.shift()))))
    }

    pub fn implies1(premise: Prop, conclusion: Prop) -> Prop {
        Prop::implies(vec![premise], conclusion)
    }

    pub fn for_each_var<T>(&self, f: &mut impl FnMut(VarId) -> Option<T>) -> Option<T> {
        match *self {
            Prop::Nonzero(ref t) => t.for_each_var(f),
            Prop::Forall(ref b) => {
                let (ref ps, ref p) = b.inner;
                for p in ps {
                    if let Some(x) = p.for_each_var(f) {
                        return Some(x);
                    }
                }
                p.for_each_var(f)
            },
            // TODO: implement these cases?
            Prop::Step(_) => None,
            Prop::Reachable(_) => None,
        }
    }
}
