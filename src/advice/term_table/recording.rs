use std::cell::RefCell;
use std::io::Write;
use serde_cbor;
use crate::logic::Term;
use super::{RawTermKind, Table};

thread_local! {
    static TABLE: RefCell<Table> = Default::default();
}

pub fn record(t: Term) {
    TABLE.with(|table| table.borrow_mut().record(t))
}

pub fn term_index(t: Term) -> usize {
    TABLE.with(|table| table.borrow().term_index(t))
}

pub fn finish(w: impl Write) -> serde_cbor::Result<()> {
    TABLE.with(|table| table.borrow().finish(w))
}
