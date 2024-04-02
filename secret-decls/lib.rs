#![no_std]
use core::mem;

pub const TERM_TABLE_CAPACITY: usize = 65536;

/// An entry in the secret term table.  This is identical to `sym_proof`'s `RawTermKind`, but we can't use that type directly because it would create a circular dependency.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
#[repr(C)]
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

extern "C" {
    static TERM_TABLE: [RawTermKind; TERM_TABLE_CAPACITY];
    static TERM_TABLE_LEN: usize;
}

pub fn validate() {
    unsafe {
        assert!(TERM_TABLE_LEN <= TERM_TABLE_CAPACITY);

        let start: *const RawTermKind = TERM_TABLE.as_ptr();
        let end = start.add(TERM_TABLE.len());
        let is_in_bounds = |ptr: *const u8| {
            (start as usize) <= (ptr as usize) && (ptr as usize) < (end as usize)
        };
        let is_aligned = |ptr: *const u8| {
            (ptr as usize - start as usize) % mem::size_of::<RawTermKind>() == 0
        };
        let is_valid = |ptr: *const u8| {
            is_in_bounds(ptr) && is_aligned(ptr)
        };
        for rtk in &TERM_TABLE[..TERM_TABLE_LEN] {
            match rtk.tag {
                RawTermKind::TAG_CONST => {},
                RawTermKind::TAG_VAR => {},
                RawTermKind::TAG_NOT => {
                    assert!(rtk.x.is_null() || is_valid(rtk.x));
                },
                RawTermKind::TAG_BINARY => {
                    // `op` (`rtk.x`) is checked at use time.
                    assert!(rtk.y.is_null() || is_valid(rtk.y));
                    assert!(rtk.z.is_null() || is_valid(rtk.z));
                },
                RawTermKind::TAG_MUX => {
                    assert!(rtk.x.is_null() || is_valid(rtk.x));
                    assert!(rtk.y.is_null() || is_valid(rtk.y));
                    assert!(rtk.z.is_null() || is_valid(rtk.z));
                },
                _ => panic!("bad tag"),
            }
        }
    }
}

pub fn table() -> &'static [RawTermKind] {
    unsafe {
        &TERM_TABLE[..TERM_TABLE_LEN]
    }
}
