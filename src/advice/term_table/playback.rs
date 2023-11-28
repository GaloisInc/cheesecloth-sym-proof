use core::cell::RefCell;
use alloc::boxed::Box;
#[cfg(not(feature = "playback_term_intern_index"))] use std::collections::HashMap;
use std::io::Read;
use std::thread_local;
use core::mem;
use serde_cbor;
use crate::logic::TermKind;
use super::RawTermKind;

thread_local! {
    static TABLE: RefCell<Table> = Default::default();
}

#[derive(Default)]
struct Table {
    /// Table of preallocated terms.  Sub-`Term`s are represented as pointers to other elements in
    /// this table.
    terms: Box<[RawTermKind]>,
    #[cfg(not(feature = "playback_term_intern_index"))]
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

// If `playback_term_intern_index` is enabled, then `Term::intern` should use advice instead of
// calling this method.
#[cfg(not(feature = "playback_term_intern_index"))]
pub fn kind_to_index(kind: TermKind) -> usize {
    TABLE.with(|table| {
        let table = table.borrow();
        let raw = RawTermKind::from_term_kind(kind, |t| t.as_ptr() as usize);
        table.kind_index.get(&raw).copied()
            .unwrap_or_else(|| panic!("failed to find {:?} ({:?}) in table", kind, raw))
    })
}

/// Convert a `RawTermKind` to a `TermKind`.  This is safe only for `RawTermKind`s returned by
/// `playback::get_index` or `playback::get_kind`.
pub unsafe fn term_kind_from_raw(raw: RawTermKind) -> TermKind {
    #[cfg(feature = "playback_term_table")]
    unsafe {
        use crate::logic::Term;
        return raw.to_term_kind(|ptr_usize| {
            Term::from_raw(&*(ptr_usize as *const RawTermKind))
        });
    }
    #[cfg(not(feature = "playback_term_table"))] {
        let _ = raw;
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

            #[cfg(not(feature = "playback_term_intern_index"))] {
                // Now that all the `RawTermKind`s have been rewritten into their final forms,
                // generate the the `kind_index` map.
                let mut kind_index = HashMap::with_capacity(terms.len());
                for (i, &raw) in terms.iter().enumerate() {
                    let old = kind_index.insert(raw, i);
                    assert!(old.is_none(), "duplicate entry for {:?} at index {}", raw, i);
                }

                *table = Table { terms, kind_index };
            }
            #[cfg(feature = "playback_term_intern_index")] {
                *table = Table { terms };
            }

            // Once `terms` is loaded into `*table`, it's unsafe to overwrite it.
        }

        Ok(())
    })
}
