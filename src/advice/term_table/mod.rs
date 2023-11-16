use std::collections::HashMap;
use std::convert::TryInto;
use std::io::{Read, Write};
use crate::logic::{Term, TermKind};
use serde::{Serialize, Deserialize};


pub mod recording;
pub mod playback;


#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Serialize, Deserialize)]
struct RawTermKind {
    tag: usize,
    x: usize,
    y: usize,
    z: usize,
}

impl RawTermKind {
    pub const TAG_CONST: usize = 0;
    pub const TAG_VAR: usize = 1;
    pub const TAG_NOT: usize = 2;
    pub const TAG_BINARY: usize = 3;
    pub const TAG_MUX: usize = 4;
}


#[derive(Debug, Default, Serialize, Deserialize)]
struct Table {
    terms: Vec<RawTermKind>,
    #[serde(skip)]
    ptr_index: HashMap<*const TermKind, usize>,
    kind_index: HashMap<RawTermKind, usize>,
}

impl Table {
    pub fn record(&mut self, t: Term) {
        let kind = self.term_kind_to_raw(*t.kind());
        let idx = self.terms.len();
        self.terms.push(kind);

        let old = self.ptr_index.insert(t.as_ptr(), idx);
        assert!(old.is_none(), "duplicate ptr_index entry for {:?}", t);

        let old = self.kind_index.insert(kind, idx);
        assert!(old.is_none(), "duplicate kind_index entry for {:?}", t);
    }

    pub fn term_index(&self, t: Term) -> usize {
        match self.ptr_index.get(&t.as_ptr()) {
            Some(&x) => x,
            None => panic!("missing entry for {:?}", t),
        }
    }

    fn term_kind_to_raw(&self, tk: TermKind) -> RawTermKind {
        let [tag, x, y, z] = match tk {
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
                self.term_index(a),
                0,
                0,
            ],
            TermKind::Binary(op, a, b) => [
                RawTermKind::TAG_BINARY,
                op.as_raw().try_into().unwrap(),
                self.term_index(a),
                self.term_index(b),
            ],
            TermKind::Mux(a, b, c) => [
                RawTermKind::TAG_MUX,
                self.term_index(a),
                self.term_index(b),
                self.term_index(c),
            ],
        };
        RawTermKind { tag, x, y, z }
    }

    pub fn len(&self) -> usize {
        self.terms.len()
    }

    pub fn get_index(&self, i: usize) -> &RawTermKind {
        &self.terms[i]
    }

    pub fn load(&mut self, r: impl Read) -> serde_cbor::Result<()> {
        // Don't overwrite existing entries.  The `playback` module hands out `&'static` references
        // to its entries, and overwriting the `Vec` would invalidate them.
        assert!(self.terms.len() == 0, "term_table is already initialized");
        let table = serde_cbor::from_reader(r)?;
        *self = table;
        Ok(())
    }

    pub fn finish(&self, w: impl Write) -> serde_cbor::Result<()> {
        serde_cbor::to_writer(w, self)
    }
}
