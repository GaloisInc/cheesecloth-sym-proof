use core::convert::{TryFrom, TryInto};
use crate::BinOp;
use crate::logic::{Term, TermKind, VarId};
use serde::{Serialize, Deserialize};


#[cfg(not(feature = "microram"))]
pub mod recording;
#[cfg(not(feature = "microram"))]
pub mod playback;

#[cfg(feature = "microram")]
pub mod playback_microram;
#[cfg(feature = "microram")]
pub use self::playback_microram as playback;



/// A raw representation of a `TermKind`.  This is `repr(C)` so it can be used in secret inputs.
///
/// In cases where `TermKind` contains a `Term` pointer, `RawTermKind` may represent the term
/// either as an index or as a pointer.  `recording` uses indices, while `playback` uses pointers.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Serialize, Deserialize)]
#[serde(from = "SerializeRawTermKind", into = "SerializeRawTermKind")]
pub struct RawTermKind {
    pub tag: usize,
    pub x: *const u8,
    pub y: *const u8,
    pub z: *const u8,
}
unsafe impl Sync for RawTermKind {}

impl RawTermKind {
    const TAG_CONST: usize = 0;
    const TAG_VAR: usize = 1;
    const TAG_NOT: usize = 2;
    const TAG_BINARY: usize = 3;
    const TAG_MUX: usize = 4;
}


#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Serialize, Deserialize)]
pub struct SerializeRawTermKind {
    pub tag: usize,
    pub x: usize,
    pub y: usize,
    pub z: usize,
}

impl From<RawTermKind> for SerializeRawTermKind {
    fn from(k: RawTermKind) -> SerializeRawTermKind {
        SerializeRawTermKind {
            tag: k.tag,
            x: k.x as usize,
            y: k.y as usize,
            z: k.z as usize,
        }
    }
}

impl From<SerializeRawTermKind> for RawTermKind {
    fn from(k: SerializeRawTermKind) -> RawTermKind {
        RawTermKind {
            tag: k.tag,
            x: k.x as *const u8,
            y: k.y as *const u8,
            z: k.z as *const u8,
        }
    }
}


impl RawTermKind {
    #[cfg_attr(not(feature = "playback_term_table"), allow(dead_code))]
    fn to_term_kind(&self, mut convert_term: impl FnMut(*const u8) -> Term) -> TermKind {
        match self.tag {
            RawTermKind::TAG_CONST => {
                let x = (self.x as usize).try_into().unwrap();
                TermKind::Const(x)
            },
            RawTermKind::TAG_VAR => {
                let v = VarId::from_raw((self.x as usize).try_into().unwrap());
                TermKind::Var(v)
            },
            RawTermKind::TAG_NOT => {
                let a = convert_term(self.x);
                TermKind::Not(a)
            },
            RawTermKind::TAG_BINARY => {
                let op = BinOp::from_raw((self.x as usize).try_into().unwrap());
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

    fn from_term_kind(
        kind: TermKind,
        mut convert_term: impl FnMut(Term) -> *const u8,
    ) -> RawTermKind {
        let (tag, x, y, z) = match kind {
            TermKind::Const(x) => (
                RawTermKind::TAG_CONST,
                usize::try_from(x).unwrap() as *const u8,
                0 as *const u8,
                0 as *const u8,
            ),
            TermKind::Var(v) => (
                RawTermKind::TAG_VAR,
                usize::try_from(v.as_raw()).unwrap() as *const u8,
                0 as *const u8,
                0 as *const u8,
            ),
            TermKind::Not(a) => (
                RawTermKind::TAG_NOT,
                convert_term(a),
                0 as *const u8,
                0 as *const u8,
            ),
            TermKind::Binary(op, a, b) => (
                RawTermKind::TAG_BINARY,
                usize::try_from(op.as_raw()).unwrap() as *const u8,
                convert_term(a),
                convert_term(b),
            ),
            TermKind::Mux(a, b, c) => (
                RawTermKind::TAG_MUX,
                convert_term(a),
                convert_term(b),
                convert_term(c),
            ),
        };
        RawTermKind { tag, x, y, z }
    }

    /// Modify all sub-`Term` pointers in-place by applying `f` to each one.
    fn adjust_pointers(&mut self, mut f: impl FnMut(*const u8) -> *const u8) {
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
