use std::collections::HashMap;
use std::hash::Hash;
use crate::logic::{VarId, Term, TermKind, Prop, ReachableProp, StatePred, Binder};
use crate::logic::shift::ShiftExt;
use crate::micro_ram::MemWidth;


pub trait EqShifted {
    /// Check whether `self == other.shift_by(amount)`, without actually constructing
    /// `other.shift_by(amount)`.
    fn eq_shifted(&self, other: &Self, amount: u32) -> bool;
}

impl EqShifted for VarId {
    fn eq_shifted(&self, other: &Self, amount: u32) -> bool {
        *self == other.shift_by(amount)
    }
}

impl EqShifted for Term {
    fn eq_shifted(&self, other: &Self, amount: u32) -> bool {
        match (self.kind(), other.kind()) {
            (TermKind::Const(x1), TermKind::Const(x2)) => x1 == x2,
            (TermKind::Var(v1), TermKind::Var(v2)) => v1.eq_shifted(&v2, amount),
            (TermKind::Not(a1), TermKind::Not(a2)) => a1.eq_shifted(&a2, amount),
            (TermKind::Binary(op1, a1, b1), TermKind::Binary(op2, a2, b2)) => {
                op1 == op2
                && a1.eq_shifted(&a2, amount)
                && b1.eq_shifted(&b2, amount)
            },
            (TermKind::Mux(a1, b1, c1), TermKind::Mux(a2, b2, c2)) => {
                a1.eq_shifted(&a2, amount)
                && b1.eq_shifted(&b2, amount)
                && c1.eq_shifted(&c2, amount)
            },
            _ => false,
        }
    }
}

impl EqShifted for Prop {
    fn eq_shifted(&self, other: &Self, amount: u32) -> bool {
        match (self, other) {
            (&Prop::Nonzero(t1), &Prop::Nonzero(t2)) => t1.eq_shifted(&t2, amount),
            (&Prop::Forall(ref b1), &Prop::Forall(ref b2)) => b1.eq_shifted(b2, amount),
            (&Prop::Reachable(ref rp1), &Prop::Reachable(ref rp2)) => rp1.eq_shifted(rp2, amount),
            _ => false,
        }
    }
}

impl EqShifted for ReachableProp {
    fn eq_shifted(&self, other: &Self, amount: u32) -> bool {
        let ReachableProp { ref pred, min_cycles } = *self;
        pred.eq_shifted(&other.pred, amount)
            && min_cycles.eq_shifted(&other.min_cycles, amount)
    }
}

impl EqShifted for StatePred {
    fn eq_shifted(&self, other: &Self, amount: u32) -> bool {
        let StatePred { ref state, ref props } = *self;
        state.eq_shifted(&other.state, amount)
            && props.eq_shifted(&other.props, amount)
    }
}

impl<T: EqShifted> EqShifted for Binder<T> {
    fn eq_shifted(&self, other: &Self, amount: u32) -> bool {
        let Binder { ref vars, ref inner } = *self;
        vars == &other.vars
            && inner.eq_shifted(&other.inner, amount)
    }
}

impl<T: EqShifted + ?Sized> EqShifted for Box<T> {
    fn eq_shifted(&self, other: &Self, amount: u32) -> bool {
        T::eq_shifted(self, other, amount)
    }
}

impl<T: EqShifted> EqShifted for [T] {
    fn eq_shifted(&self, other: &Self, amount: u32) -> bool {
        if self.len() != other.len() {
            return false;
        }
        for (x1, x2) in self.iter().zip(other.iter()) {
            if !x1.eq_shifted(x2, amount) {
                return false;
            }
        }
        true
    }
}

impl<T: EqShifted> EqShifted for Vec<T> {
    fn eq_shifted(&self, other: &Self, amount: u32) -> bool {
        <[T]>::eq_shifted(self, other, amount)
    }
}

impl<K: Eq + Hash, V: EqShifted> EqShifted for HashMap<K, V> {
    fn eq_shifted(&self, other: &Self, amount: u32) -> bool {
        if self.len() != other.len() {
            return false;
        }
        for (k, v1) in self {
            let v2 = match other.get(k) {
                Some(x) => x,
                None => return false,
            };
            if !v1.eq_shifted(v2, amount) {
                return false;
            }
        }
        true
    }
}

impl<T: EqShifted, const N: usize> EqShifted for [T; N] {
    fn eq_shifted(&self, other: &Self, amount: u32) -> bool {
        <[T]>::eq_shifted(self, other, amount)
    }
}

impl<A: EqShifted, B: EqShifted> EqShifted for (A, B) {
    fn eq_shifted(&self, other: &Self, amount: u32) -> bool {
        self.0.eq_shifted(&other.0, amount)
            && self.1.eq_shifted(&other.1, amount)
    }
}

impl<A: EqShifted, B: EqShifted, C: EqShifted> EqShifted for (A, B, C) {
    fn eq_shifted(&self, other: &Self, amount: u32) -> bool {
        self.0.eq_shifted(&other.0, amount)
            && self.1.eq_shifted(&other.1, amount)
            && self.2.eq_shifted(&other.2, amount)
    }
}

impl EqShifted for u8 {
    fn eq_shifted(&self, other: &Self, _amount: u32) -> bool {
        self == other
    }
}

impl EqShifted for u64 {
    fn eq_shifted(&self, other: &Self, _amount: u32) -> bool {
        self == other
    }
}

impl EqShifted for MemWidth {
    fn eq_shifted(&self, other: &Self, _amount: u32) -> bool {
        self == other
    }
}
