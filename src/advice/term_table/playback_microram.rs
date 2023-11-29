//! MicroRAM version of `term_table::playback`.  This exposes the same API, except instead of
//! having a `load` function to initialize the table, the table is provided as an `extern "C"`
//! symbol defined in a secret segment.
use core::cell::RefCell;
use alloc::boxed::Box;
use core::mem;
use serde_cbor;
use crate::logic::TermKind;
use super::RawTermKind;


// TODO
const TERM_TABLE_CAPACITY: usize = 65536;

extern "C" {
    static TERM_TABLE: [RawTermKind; TERM_TABLE_CAPACITY];
    static TERM_TABLE_LEN: usize;
}

// FIXME: validate TABLE_LEN <= TABLE_CAPACITY
// FIXME: validate entries in TABLE

pub fn len() -> usize {
    unsafe { TERM_TABLE_LEN }
}

fn table() -> &'static [RawTermKind] {
    unsafe {
        &*TERM_TABLE.get_unchecked(..TERM_TABLE_LEN)
    }
}

pub fn get_index(index: usize) -> &'static RawTermKind {
    &table()[index]
}

/// Convert a `RawTermKind` to a `TermKind`.  This is safe only for `RawTermKind`s returned by
/// `playback::get_index` or `playback::get_kind`.
pub unsafe fn term_kind_from_raw(raw: RawTermKind) -> TermKind {
    unsafe {
        use crate::logic::Term;
        return raw.to_term_kind(|ptr_usize| {
            Term::from_raw(&*(ptr_usize as *const RawTermKind))
        });
    }
}
