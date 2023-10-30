use super::{VarId, Term, TermInner, Prop, StepProp, ReachableProp, StatePred, Binder};


pub trait Visitor {
    fn visit_var_id(&mut self, x: VarId) {
        default_visit_var_id(self, x)
    }
    fn visit_term(&mut self, x: &Term) {
        default_visit_term(self, x)
    }
    fn visit_binder<T>(&mut self, x: &Binder<T>, f: impl FnOnce(&mut Self, &T)) {
        default_visit_binder(self, x, f)
    }
}

pub fn default_visit_var_id<F: Visitor + ?Sized>(_f: &mut F, _x: VarId) {
}

pub fn default_visit_term<F: Visitor + ?Sized>(f: &mut F, x: &Term) {
    match *x.inner() {
        TermInner::Const(_x) => {},
        TermInner::Var(v) => v.visit_with(f),
        TermInner::Not(ref t) => t.visit_with(f),
        TermInner::Binary(_op, ref ts) => {
            let (ref a, ref b) = **ts;
            a.visit_with(f);
            b.visit_with(f);
        },
        TermInner::Mux(ref ts) => {
            let (ref a, ref b, ref c) = **ts;
            a.visit_with(f);
            b.visit_with(f);
            c.visit_with(f);
        },
    }
}

pub fn default_visit_binder<F: Visitor + ?Sized, T>(
    f: &mut F,
    x: &Binder<T>,
    func: impl FnOnce(&mut F, &T),
) {
    func(f, &x.inner)
}


pub trait Visit: Sized {
    fn visit_with<F: Visitor + ?Sized>(&self, f: &mut F);
}

impl Visit for VarId {
    fn visit_with<F: Visitor + ?Sized>(&self, f: &mut F) {
        f.visit_var_id(*self);
    }
}

impl Visit for Term {
    fn visit_with<F: Visitor + ?Sized>(&self, f: &mut F) {
        f.visit_term(self);
    }
}

impl Visit for Prop {
    fn visit_with<F: Visitor + ?Sized>(&self, f: &mut F) {
        match *self {
            Prop::Nonzero(ref t) => t.visit_with(f),
            Prop::Forall(ref b) => {
                f.visit_binder(b, |f, x| {
                    let (ref ps, ref q) = *x;
                    ps.visit_with(f);
                    q.visit_with(f);
                })
            },
            Prop::Step(ref sp) => sp.visit_with(f),
            Prop::Reachable(ref rp) => rp.visit_with(f),
        }
    }
}

impl Visit for StepProp {
    fn visit_with<F: Visitor + ?Sized>(&self, f: &mut F) {
        let StepProp { ref pre, ref post, ref min_cycles } = *self;
        f.visit_binder(pre, |f, sp| sp.visit_with(f));
        f.visit_binder(post, |f, sp| sp.visit_with(f));
        min_cycles.visit_with(f);
    }
}

impl Visit for ReachableProp {
    fn visit_with<F: Visitor + ?Sized>(&self, f: &mut F) {
        let ReachableProp { ref pred, ref min_cycles } = *self;
        f.visit_binder(pred, |f, sp| sp.visit_with(f));
        min_cycles.visit_with(f);
    }
}

impl Visit for StatePred {
    fn visit_with<F: Visitor + ?Sized>(&self, f: &mut F) {
        let StatePred { ref state, ref props } = *self;
        state.visit_with(f);
        props.visit_with(f);
    }
}

impl<T: Visit> Visit for Box<T> {
    fn visit_with<F: Visitor + ?Sized>(&self, f: &mut F) {
        T::visit_with(self, f);
    }
}

impl<T: Visit> Visit for Vec<T> {
    fn visit_with<F: Visitor + ?Sized>(&self, f: &mut F) {
        for x in self {
            x.visit_with(f);
        }
    }
}

impl<T: Visit, const N: usize> Visit for [T; N] {
    fn visit_with<F: Visitor + ?Sized>(&self, f: &mut F) {
        for x in self {
            x.visit_with(f);
        }
    }
}
