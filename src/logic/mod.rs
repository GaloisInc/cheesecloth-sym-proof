use std::ops::Deref;
use crate::logic::fold::Fold;
use crate::logic::shift::ShiftExt;
use crate::logic::subst::SubstExt;
use crate::symbolic;


pub mod fold;
pub mod print;
pub mod rename_vars;
pub mod shift;
pub mod subst;
pub mod term;
pub mod visit;
pub mod wf;

pub use self::term::{Term, TermKind};


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
            storage: Term::var_unchecked(VarId(0)),
        }
    }
}

impl Subst for IdentitySubsts {
    const IS_IDENTITY: bool = true;
    fn subst(&mut self, v: VarId) -> &Term {
        self.storage = Term::var_unchecked(v);
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
    Forall(Binder<(Box<[Prop]>, Box<Prop>)>),
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
    pub props: Box<[Prop]>,
}

impl Prop {
    pub fn implies(premises: Box<[Prop]>, conclusion: Prop) -> Prop {
        Prop::Forall(Binder::new(|_| (premises.shift(), Box::new(conclusion.shift()))))
    }

    pub fn implies1(premise: Prop, conclusion: Prop) -> Prop {
        Prop::implies(Box::new([premise]), conclusion)
    }

    pub fn for_each_var<T>(&self, f: &mut impl FnMut(VarId) -> Option<T>) -> Option<T> {
        match *self {
            Prop::Nonzero(ref t) => t.for_each_var(f),
            Prop::Forall(ref b) => {
                let (ref ps, ref p) = b.inner;
                for p in ps.iter() {
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
