use core::cell::RefCell;
use alloc::vec::Vec;
use std::collections::HashMap;
use std::io::Write;
use std::thread_local;
use serde_cbor;
use crate::logic::Term;
use super::RawTermKind;

thread_local! {
    static TABLE: RefCell<Table> = Default::default();
}

#[derive(Default)]
struct Table {
    /// Record of terms seen so far.  Sub-`Term`s are represented using indices into this table.
    terms: Vec<RawTermKind>,
    /// Map from `term.as_ptr()` to the index where the term appears in `self.terms`.
    ptr_index: HashMap<*const (), usize>,
}

impl Table {
    fn get_index(&self, t: Term) -> usize {
        self.ptr_index.get(&t.as_ptr()).copied()
            .unwrap_or_else(|| panic!("term {:?} is not present in the recording table", t))
    }
}

pub fn record(t: Term) {
    TABLE.with(|table| {
        let mut table = table.borrow_mut();

        let raw = RawTermKind::from_term_kind(t.kind(), |t| table.get_index(t));
        let idx = table.terms.len();
        table.terms.push(raw);

        let old = table.ptr_index.insert(t.as_ptr(), idx);
        assert!(old.is_none(), "duplicate ptr_index entry for {:?}", t);
    });
}

pub fn term_index(t: Term) -> usize {
    TABLE.with(|table| {
        table.borrow().get_index(t)
    })
}

pub fn finish(w: impl Write) -> serde_cbor::Result<()> {
    TABLE.with(|table| {
        let table = table.borrow();
        serde_cbor::to_writer(w, &table.terms)
    })
}
