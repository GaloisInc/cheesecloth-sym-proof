use std::cell::RefCell;
use std::io::Read;
use serde_cbor;
use crate::logic::Term;
use super::{RawTermKind, Table};

thread_local! {
    static TABLE: RefCell<Table> = Default::default();
}

pub fn len() -> usize {
    TABLE.with(|table| table.borrow().len())
}

pub fn get_index(index: usize) -> Term {
    TABLE.with(|table| {
        todo!()
    })
}

pub fn load(r: impl Read) -> serde_cbor::Result<()> {
    todo!()
}
