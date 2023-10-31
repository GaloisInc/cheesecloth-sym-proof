use std::array;
use super::{VarId, Term, TermKind, Prop, StepProp, ReachableProp, StatePred, Binder};


pub trait Folder {
    fn fold_var_id(&mut self, x: VarId) -> VarId {
        default_fold_var_id(self, x)
    }
    fn fold_term(&mut self, x: &Term) -> Term {
        default_fold_term(self, x)
    }
    fn fold_binder<T>(&mut self, x: &Binder<T>, f: impl FnOnce(&mut Self, &T) -> T) -> Binder<T> {
        default_fold_binder(self, x, f)
    }
}

pub fn default_fold_var_id<F: Folder + ?Sized>(_f: &mut F, x: VarId) -> VarId {
    x
}

pub fn default_fold_term<F: Folder + ?Sized>(f: &mut F, x: &Term) -> Term {
    match *x.kind() {
        TermKind::Const(x) => Term::const_(x),
        TermKind::Var(v) => Term::var_unchecked(v.fold_with(f)),
        TermKind::Not(t) => Term::not(t.fold_with(f)),
        TermKind::Binary(op, a, b) => {
            Term::binary(op, a.fold_with(f), b.fold_with(f))
        },
        TermKind::Mux(a, b, c) => {
            Term::mux(a.fold_with(f), b.fold_with(f), c.fold_with(f))
        },
    }
}

pub fn default_fold_binder<F: Folder + ?Sized, T>(
    f: &mut F,
    x: &Binder<T>,
    func: impl FnOnce(&mut F, &T) -> T,
) -> Binder<T> {
    Binder::from_parts(x.vars.clone(), func(f, &x.inner))
}


pub trait Fold: Sized {
    fn fold_with<F: Folder + ?Sized>(&self, f: &mut F) -> Self;
}

impl Fold for VarId {
    fn fold_with<F: Folder + ?Sized>(&self, f: &mut F) -> Self {
        f.fold_var_id(*self)
    }
}

impl Fold for Term {
    fn fold_with<F: Folder + ?Sized>(&self, f: &mut F) -> Self {
        f.fold_term(self)
    }
}

impl Fold for Prop {
    fn fold_with<F: Folder + ?Sized>(&self, f: &mut F) -> Self {
        match *self {
            Prop::Nonzero(t) => Prop::Nonzero(t.fold_with(f)),
            Prop::Forall(ref b) => {
                Prop::Forall(f.fold_binder(b, |f, x| {
                    let (ref ps, ref q) = *x;
                    (ps.fold_with(f), q.fold_with(f))
                }))
            },
            Prop::Step(ref sp) => Prop::Step(sp.fold_with(f)),
            Prop::Reachable(ref rp) => Prop::Reachable(rp.fold_with(f)),
        }
    }
}

impl Fold for StepProp {
    fn fold_with<F: Folder + ?Sized>(&self, f: &mut F) -> Self {
        let StepProp { ref pre, ref post, min_cycles } = *self;
        StepProp {
            pre: pre.fold_with(f),
            post: post.fold_with(f),
            min_cycles: min_cycles.fold_with(f),
        }
    }
}

impl Fold for ReachableProp {
    fn fold_with<F: Folder + ?Sized>(&self, f: &mut F) -> Self {
        let ReachableProp { ref pred, min_cycles } = *self;
        ReachableProp {
            pred: pred.fold_with(f),
            min_cycles: min_cycles.fold_with(f),
        }
    }
}

impl Fold for StatePred {
    fn fold_with<F: Folder + ?Sized>(&self, f: &mut F) -> Self {
        let StatePred { ref state, ref props } = *self;
        StatePred {
            state: state.fold_with(f),
            props: props.fold_with(f),
        }
    }
}

impl<T: Fold> Fold for Binder<T> {
    fn fold_with<F: Folder + ?Sized>(&self, f: &mut F) -> Self {
        f.fold_binder(self, |f, x| x.fold_with(f))
    }
}


impl<T: Fold> Fold for Box<T> {
    fn fold_with<F: Folder + ?Sized>(&self, f: &mut F) -> Self {
        Box::new(T::fold_with(self, f))
    }
}

impl<T: Fold> Fold for Box<[T]> {
    fn fold_with<F: Folder + ?Sized>(&self, f: &mut F) -> Self {
        self.iter().map(|x| x.fold_with(f)).collect()
    }
}

impl<T: Fold> Fold for Vec<T> {
    fn fold_with<F: Folder + ?Sized>(&self, f: &mut F) -> Self {
        self.iter().map(|x| x.fold_with(f)).collect()
    }
}

impl<T: Fold, const N: usize> Fold for [T; N] {
    fn fold_with<F: Folder + ?Sized>(&self, f: &mut F) -> Self {
        array::from_fn(|i| self[i].fold_with(f))
    }
}
