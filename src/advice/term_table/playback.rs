use std::cell::RefCell;
use std::collections::HashMap;
use std::convert::TryInto;
use std::io::Read;
use std::mem;
use serde_cbor;
use crate::BinOp;
use crate::logic::{Term, TermKind, VarId};
use super::RawTermKind;

thread_local! {
    static TABLE: RefCell<Table> = Default::default();
}

#[derive(Default)]
struct Table {
    /// Table of preallocated terms.  Sub-`Term`s are represented as pointers to other elements in
    /// this table.
    terms: Box<[RawTermKind]>,
    /// Map from `RawTermKind` to the position where that `RawTermKind` appears in `self.terms`.
    kind_index: HashMap<RawTermKind, usize>,
}

impl Table {
    unsafe fn get_static(&self, index: usize) -> &'static RawTermKind {
        let raw_ref = &self.terms[index];
        unsafe { mem::transmute::<&RawTermKind, &'static RawTermKind>(raw_ref) }
    }
}

pub fn len() -> usize {
    TABLE.with(|table| table.borrow().terms.len())
}

/// This function is **unsound**: the references returned from this function claim to be `'static`,
/// but they actually live only as long as the thread.  It's unsafe to pass the returned reference
/// to another thread.
pub fn get_index(index: usize) -> &'static RawTermKind {
    TABLE.with(|table| {
        let table = table.borrow();
        unsafe { table.get_static(index) }
    })
}

/// This function is **unsound**: the references returned from this function claim to be `'static`,
/// but they actually live only as long as the thread.  It's unsafe to pass the returned reference
/// to another thread.
pub fn get_kind(kind: TermKind) -> &'static RawTermKind {
    TABLE.with(|table| {
        let table = table.borrow();
        let raw = RawTermKind::from_term_kind(kind, |t| t.as_ptr() as usize);
        let index = table.kind_index.get(&raw).copied()
            .unwrap_or_else(|| panic!("failed to find {:?} ({:?}) in table", kind, raw));
        unsafe { table.get_static(index) }
    })
}

/// Convert a `RawTermKind` to a `TermKind`.  This is safe only for `RawTermKind`s returned by
/// `playback::get_index` or `playback::get_kind`.
pub unsafe fn term_kind_from_raw(raw: RawTermKind) -> TermKind {
    #[cfg(feature = "playback_term_table")]
    unsafe {
        return raw.to_term_kind(|ptr_usize| {
            Term::from_raw(&*(ptr_usize as *const RawTermKind))
        });
    }
    #[cfg(not(feature = "playback_term_table"))] {
        unreachable!("impossible: term_table::playback method was called, \
            but playback_term_table feature is disabled?");
    }
}

pub fn load(r: impl Read) -> serde_cbor::Result<()> {
    TABLE.with(|table| {
        let mut table = table.borrow_mut();
        // Don't overwrite existing entries.  This module hands out `&'static` references to table
        // entries, and overwriting the `Vec` would invalidate them.
        assert!(table.terms.len() == 0, "playback term_table has already been initialized");

        unsafe {
            let mut terms: Box<[RawTermKind]> = serde_cbor::from_reader(r)?;

            // When loaded from disk, the `terms` table uses indices for all sub-`Term` pointers.
            // Here we adjust it to use pointers to other elements of `terms` instead.
            let base = terms.as_ptr();
            for raw in terms.iter_mut() {
                raw.adjust_pointers(|idx| {
                    base.add(idx) as usize
                });
            }

            // Now that all the `RawTermKind`s have been rewritten into their final forms, generate
            // the the `kind_index` map.
            let kind_index = terms.iter().enumerate().map(|(i, &raw)| (raw, i)).collect();

            *table = Table { terms, kind_index };
            // Once `terms` is loaded into `*table`, it's unsafe to overwrite it.
        }

        Ok(())
    })
}
