//! MicroRAM version of `term_table::playback`.  This exposes the same API, except instead of
//! having a `load` function to initialize the table, the table is provided as an `extern "C"`
//! symbol defined in a secret segment.
use core::cell::RefCell;
use core::mem;
use alloc::boxed::Box;
use cheesecloth_sym_proof_secret_decls as secret_decls;
use crate::logic::TermKind;
use super::RawTermKind;


/*
pub fn len() -> usize {
    unsafe { TERM_TABLE_LEN }
}
*/

pub fn len() -> usize {
    secret_decls::table().len()
}

fn get_index_helper(index: usize) -> &'static secret_decls::RawTermKind {
    &secret_decls::table()[index]
}

pub fn get_index(index: usize) -> &'static RawTermKind {
    unsafe {
        let ptr = get_index_helper(index);
        // This transmute is valid because `RawTermKind` is a `repr(transparent)` wrapper around
        // `secret_decls::RawTermKind`.
        mem::transmute::<&'static secret_decls::RawTermKind, &'static RawTermKind>(ptr)
    }
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
