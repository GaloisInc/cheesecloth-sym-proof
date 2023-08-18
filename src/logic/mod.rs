use std::array;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::ops::Deref;
use std::rc::Rc;
use crate::{Word, WORD_BYTES, Addr, BinOp};
use crate::logic::fold::Fold;
use crate::logic::print::Printer;
use crate::logic::shift::ShiftExt;
use crate::logic::subst::SubstExt;
use crate::micro_ram::{self, NUM_REGS, MemWidth, Reg, Operand};
use crate::symbolic;


pub mod fold;
pub mod print;
pub mod shift;
pub mod subst;


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


#[derive(Clone, Debug)]
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


#[derive(Clone, Debug)]
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
    pub fn for_each_var<T>(&self, mut f: &mut impl FnMut(VarId) -> Option<T>) -> Option<T> {
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


#[derive(Clone, Debug)]
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
#[derive(Clone, Debug)]
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
#[derive(Clone, Debug)]
pub struct ReachableProp {
    pub pred: Binder<StatePred>,
    pub min_cycles: Term,
}

/// A predicate `P(s)` on states.  The predicate holds if `s == state` and all `props` hold.
#[derive(Clone, Debug)]
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

    pub fn check_eq(&self, other: &Prop) -> bool {
        match (self, other) {
            (&Prop::Nonzero(ref t1), &Prop::Nonzero(ref t2)) => t1 == t2,
            (&Prop::Forall(ref b1), &Prop::Forall(ref b2)) => {
                b1.vars.len() == b2.vars.len()
                    && b1.inner.0.len() == b2.inner.0.len()
                    && b1.inner.0.iter().zip(b2.inner.0.iter()).all(|(x, y)| x.check_eq(y))
                    && b1.inner.1.check_eq(&b2.inner.1)
            },
            (&Prop::Step(ref sp1), &Prop::Step(ref sp2)) => sp1.check_eq(sp2),
            (&Prop::Reachable(_), &Prop::Reachable(_)) => false, // TODO
            _ => false,
        }
    }

    pub fn for_each_var<T>(&self, mut f: &mut impl FnMut(VarId) -> Option<T>) -> Option<T> {
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

impl StepProp {
    pub fn check_eq(&self, other: &StepProp) -> bool {
        let f = |x: &Binder<StatePred>, y: &Binder<StatePred>| -> bool {
            x.vars.len() == y.vars.len()
                && x.inner.check_eq(&y.inner)
        };
        f(&self.pre, &other.pre)
            && f(&self.post, &other.post)
            && self.min_cycles == other.min_cycles
    }
}

impl StatePred {
    pub fn check_eq(&self, other: &StatePred) -> bool {
        self.state.check_eq(&other.state)
            && self.props.len() == other.props.len()
            && self.props.iter().zip(other.props.iter()).all(|(x, y)| x.check_eq(y))
    }
}


pub trait Comparator {
    fn compare_vars(&mut self, v1: VarId, v2: VarId) -> bool {
        default_compare_vars(self, v1, v2)
    }
    fn compare_terms(&mut self, t1: &Term, t2: &Term) -> bool {
        default_compare_terms(self, t1, t2)
    }
    fn compare_props(&mut self, p1: &Prop, p2: &Prop) -> bool {
        default_compare_props(self, p1, p2)
    }
    fn compare_binders<T>(
        &mut self,
        b1: &Binder<T>,
        b2: &Binder<T>, 
        f: impl FnOnce(&mut Self, &T, &T) -> bool,
    ) -> bool {
        default_compare_binders(self, b1, b2, f)
    }
    fn compare_slices<T>(
        &mut self,
        s1: &[T],
        s2: &[T], 
        f: impl FnMut(&mut Self, &T, &T) -> bool,
    ) -> bool {
        default_compare_slices(self, s1, s2, f)
    }
    fn compare_step_props(&mut self, sp1: &StepProp, sp2: &StepProp) -> bool {
        default_compare_step_props(self, sp1, sp2)
    }
    fn compare_reachable_props(&mut self, rp1: &ReachableProp, rp2: &ReachableProp) -> bool {
        default_compare_reachable_props(self, rp1, rp2)
    }
    fn compare_state_preds(&mut self, sp1: &StatePred, sp2: &StatePred) -> bool {
        default_compare_state_preds(self, sp1, sp2)
    }
    fn compare_states(&mut self, s1: &symbolic::State, s2: &symbolic::State) -> bool {
        default_compare_states(self, s1, s2)
    }
}

fn default_compare_vars<C: Comparator + ?Sized>(_cmp: &mut C, v1: VarId, v2: VarId) -> bool {
    v1 == v2
}

fn default_compare_terms<C: Comparator + ?Sized>(cmp: &mut C, t1: &Term, t2: &Term) -> bool {
    match (&t1.0, &t2.0) {
        (&TermInner::Const(x1), &TermInner::Const(x2)) => x1 == x2,
        (&TermInner::Var(v1), &TermInner::Var(v2)) => cmp.compare_vars(v1, v2),
        (&TermInner::Not(ref a1), &TermInner::Not(ref a2)) => cmp.compare_terms(a1, a2),
        (&TermInner::Binary(_, ref ab1), &TermInner::Binary(_, ref ab2)) => {
            let (ref a1, ref b1) = **ab1;
            let (ref a2, ref b2) = **ab2;
            cmp.compare_terms(a1, a2)
                && cmp.compare_terms(b1, b2)
        },
        (&TermInner::Mux(ref abc1), &TermInner::Mux(ref abc2)) => {
            let (ref a1, ref b1, ref c1) = **abc1;
            let (ref a2, ref b2, ref c2) = **abc2;
            cmp.compare_terms(a1, a2)
                && cmp.compare_terms(b1, b2)
                && cmp.compare_terms(c1, c2)
        },
        _ => false,
    }
}

fn default_compare_props<C: Comparator + ?Sized>(cmp: &mut C, p1: &Prop, p2: &Prop) -> bool {
    match (p1, p2) {
        (&Prop::Nonzero(ref t1), &Prop::Nonzero(ref t2)) => cmp.compare_terms(t1, t2),
        (&Prop::Forall(ref b1), &Prop::Forall(ref b2)) => {
            cmp.compare_binders(b1, b2, |cmp, ab1, ab2| {
                let (ref a1, ref b1) = *ab1;
                let (ref a2, ref b2) = *ab2;
                cmp.compare_slices(a1, a2, |cmp, x1, x2| cmp.compare_props(x1, x2))
                    && cmp.compare_props(b1, b2)
            })
        },
        (&Prop::Step(ref sp1), &Prop::Step(ref sp2)) => {
            cmp.compare_step_props(sp1, sp2)
        },
        (&Prop::Reachable(ref rp1), &Prop::Reachable(ref rp2)) => {
            cmp.compare_reachable_props(rp1, rp2)
        },
        _ => false,
    }
}

fn default_compare_binders<C: Comparator + ?Sized, T>(
    cmp: &mut C,
    b1: &Binder<T>,
    b2: &Binder<T>, 
    f: impl FnOnce(&mut C, &T, &T) -> bool,
) -> bool {
    b1.vars.len() == b2.vars.len()
        && f(cmp, &b1.inner, &b2.inner)
}

fn default_compare_slices<C: Comparator + ?Sized, T>(
    cmp: &mut C,
    s1: &[T],
    s2: &[T], 
    mut f: impl FnMut(&mut C, &T, &T) -> bool,
) -> bool {
    s1.len() == s2.len()
        && s1.iter().zip(s2.iter()).all(|(x1, x2)| f(cmp, x1, x2))
}

fn default_compare_step_props<C: Comparator + ?Sized>(
    cmp: &mut C,
    sp1: &StepProp,
    sp2: &StepProp,
) -> bool {
    let StepProp { pre: ref pre1, post: ref post1, min_cycles: ref min_cycles1 } = *sp1;
    let StepProp { pre: ref pre2, post: ref post2, min_cycles: ref min_cycles2 } = *sp2;
    cmp.compare_binders(pre1, pre2, |cmp, pred1, pred2| {
        cmp.compare_state_preds(pred1, pred2)
    })
        && cmp.compare_binders(post1, post2, |cmp, postd1, postd2| {
            cmp.compare_state_preds(postd1, postd2)
        })
        && cmp.compare_terms(min_cycles1, min_cycles2)
}

fn default_compare_reachable_props<C: Comparator + ?Sized>(
    cmp: &mut C,
    rp1: &ReachableProp,
    rp2: &ReachableProp,
) -> bool {
    let ReachableProp { pred: ref pred1, min_cycles: ref min_cycles1 } = *rp1;
    let ReachableProp { pred: ref pred2, min_cycles: ref min_cycles2 } = *rp2;
    cmp.compare_binders(pred1, pred2, |cmp, pred1, pred2| {
        cmp.compare_state_preds(pred1, pred2)
    })
        && cmp.compare_terms(min_cycles1, min_cycles2)
}

fn default_compare_state_preds<C: Comparator + ?Sized>(
    cmp: &mut C,
    sp1: &StatePred,
    sp2: &StatePred,
) -> bool {
    let StatePred { state: ref state1, props: ref props1 } = *sp1;
    let StatePred { state: ref state2, props: ref props2 } = *sp2;
    cmp.compare_states(state1, state2)
        && cmp.compare_slices(props1, props2, |cmp, p1, p2| cmp.compare_props(p1, p2))
}

fn default_compare_states<C: Comparator + ?Sized>(
    cmp: &mut C,
    s1: &symbolic::State,
    s2: &symbolic::State,
) -> bool {
    let symbolic::State { pc: pc1, regs: ref regs1, mem: ref mem1 } = *s1;
    let symbolic::State { pc: pc2, regs: ref regs2, mem: ref mem2 } = *s2;
    pc1 == pc2
        && regs1.iter().zip(regs2.iter()).all(|(t1, t2)| cmp.compare_terms(t1, t2))
        && {
            eprintln!("ADMITTED: symbolic::State mem comparison");
            true
        }
}


/// Equality modulo alpha-renaming of binders.
pub struct EqAlpha {
    scope_map: Vec<(u32, u32)>,
}

impl EqAlpha {
    pub fn new() -> EqAlpha {
        EqAlpha {
            scope_map: Vec::new(),
        }
    }

    pub fn compare_props(p1: &Prop, p2: &Prop) -> bool {
        Self::new().compare_props(p1, p2)
    }
}

impl Comparator for EqAlpha {
    fn compare_vars(&mut self, v1: VarId, v2: VarId) -> bool {
        v1 == v2
    }

    fn compare_binders<T>(
        &mut self,
        b1: &Binder<T>,
        b2: &Binder<T>, 
        f: impl FnOnce(&mut Self, &T, &T) -> bool,
    ) -> bool {
        if b1.vars.len() != b2.vars.len() {
            return false;
        }
        f(self, &b1.inner, &b2.inner)
    }
}
