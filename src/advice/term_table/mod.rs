use std::collections::HashMap;
use std::convert::TryInto;
use std::io::{Read, Write};
use crate::BinOp;
use crate::logic::{Term, TermKind, VarId};
use serde::{Serialize, Deserialize};


pub mod recording;
pub mod playback;


/// A raw representation of a `TermKind`.  This is `repr(C)` so it can be used in secret inputs.
///
/// In cases where `TermKind` contains a `Term` pointer, `RawTermKind` may represent the term
/// either as an index or as a pointer.  `recording` uses indices, while `playback` uses pointers.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Serialize, Deserialize)]
pub struct RawTermKind {
    tag: usize,
    x: usize,
    y: usize,
    z: usize,
}

impl RawTermKind {
    const TAG_CONST: usize = 0;
    const TAG_VAR: usize = 1;
    const TAG_NOT: usize = 2;
    const TAG_BINARY: usize = 3;
    const TAG_MUX: usize = 4;
}


impl RawTermKind {
    fn to_term_kind(&self, mut convert_term: impl FnMut(usize) -> Term) -> TermKind {
        match self.tag {
            RawTermKind::TAG_CONST => {
                let x = self.x.try_into().unwrap();
                TermKind::Const(x)
            },
            RawTermKind::TAG_VAR => {
                let v = VarId::from_raw(self.x.try_into().unwrap());
                TermKind::Var(v)
            },
            RawTermKind::TAG_NOT => {
                let a = convert_term(self.x);
                TermKind::Not(a)
            },
            RawTermKind::TAG_BINARY => {
                let op = BinOp::from_raw(self.x.try_into().unwrap());
                let a = convert_term(self.y);
                let b = convert_term(self.z);
                TermKind::Binary(op, a, b)
            },
            RawTermKind::TAG_MUX => {
                let a = convert_term(self.x);
                let b = convert_term(self.y);
                let c = convert_term(self.z);
                TermKind::Mux(a, b, c)
            },
            _ => panic!("bad tag in {:?}", self),
        }
    }

    fn from_term_kind(kind: TermKind, mut convert_term: impl FnMut(Term) -> usize) -> RawTermKind {
        let [tag, x, y, z] = match kind {
            TermKind::Const(x) => [
                RawTermKind::TAG_CONST,
                x.try_into().unwrap(),
                0,
                0,
            ],
            TermKind::Var(v) => [
                RawTermKind::TAG_VAR,
                v.as_raw().try_into().unwrap(),
                0,
                0,
            ],
            TermKind::Not(a) => [
                RawTermKind::TAG_NOT,
                convert_term(a),
                0,
                0,
            ],
            TermKind::Binary(op, a, b) => [
                RawTermKind::TAG_BINARY,
                op.as_raw().try_into().unwrap(),
                convert_term(a),
                convert_term(b),
            ],
            TermKind::Mux(a, b, c) => [
                RawTermKind::TAG_MUX,
                convert_term(a),
                convert_term(b),
                convert_term(c),
            ],
        };
        RawTermKind { tag, x, y, z }
    }

    /// Modify all sub-`Term` pointers in-place by applying `f` to each one.
    fn adjust_pointers(&mut self, mut f: impl FnMut(usize) -> usize) {
        match self.tag {
            RawTermKind::TAG_CONST => {
                // No pointers
            },
            RawTermKind::TAG_VAR => {
                // No pointers
            },
            RawTermKind::TAG_NOT => {
                self.x = f(self.x);
            },
            RawTermKind::TAG_BINARY => {
                self.y = f(self.y);
                self.z = f(self.z);
            },
            RawTermKind::TAG_MUX => {
                self.x = f(self.x);
                self.y = f(self.y);
                self.z = f(self.z);
            },
            _ => panic!("bad tag in {:?}", self),
        }
    }
}
