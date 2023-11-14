// The proof implementation returns `Err` when a rule fails to apply.  A bad proof will be caught
// eventually, but checking all `Result`s lets us catch problems sooner.
#![deny(unused_must_use)]
use std::mem;


pub mod advice;
pub mod micro_ram;
pub mod kernel;
pub mod logic;
pub mod symbolic;
pub mod tactics;



pub type Word = u64;
pub const WORD_BYTES: Word = mem::size_of::<Word>() as Word;
pub const WORD_BITS: Word = WORD_BYTES * 8;
pub type Addr = Word;


macro_rules! define_bin_op {
    ($($Variant:ident,)*) => {
        #[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
        pub enum BinOp {
            $($Variant,)*
        }

        impl BinOp {
            pub const COUNT: u8 = 0 $(+ { let _ = Self::$Variant; 1 })*;

            pub fn as_raw(self) -> u8 {
                #![allow(unused)]
                let mut i = 0;
                $(
                    if self == Self::$Variant {
                        return i;
                    }
                    i += 1;
                )*
                unreachable!()
            }

            pub fn from_raw(raw: u8) -> Self {
                #![allow(unused)]
                assert!(raw < Self::COUNT, "discriminant {} is out of range", raw);
                let mut i = raw;
                $(
                    if i == 0 {
                        return Self::$Variant;
                    }
                    i -= 1;
                )*
                unreachable!()
            }
        }

    };
}

define_bin_op! {
    And,
    Or,
    Xor,
    Add,
    Sub,
    Mull,
    Umulh,
    Smulh,
    Udiv,
    Umod,
    Shl,
    Shr,
    Cmpe,
    Cmpa,
    Cmpae,
    Cmpg,
    Cmpge,
}

impl BinOp {
    pub fn eval(self, x: Word, y: Word) -> Word {
        match self {
            BinOp::And => x & y,
            BinOp::Or => x | y,
            BinOp::Xor => x ^ y,
            BinOp::Add => x.wrapping_add(y),
            BinOp::Sub => x.wrapping_sub(y),
            BinOp::Mull => x.wrapping_mul(y),
            BinOp::Umulh => {
                debug_assert_eq!(mem::size_of::<Word>(), 8);
                let xx = x as u128;
                let yy = y as u128;
                let zz = (xx * yy) >> 64;
                zz as u64
            },
            BinOp::Smulh => {
                debug_assert_eq!(mem::size_of::<Word>(), 8);
                let xx = x as i64 as i128;
                let yy = y as i64 as i128;
                let zz = (xx * yy) >> 64;
                zz as u64
            },
            BinOp::Udiv => {
                if y == 0 { 0 } else { x / y }
            },
            BinOp::Umod => {
                if y == 0 { x } else { x % y }
            },
            BinOp::Shl => {
                if y >= WORD_BITS { 0 } else { x << y as u32 }
            },
            BinOp::Shr => {
                if y >= WORD_BITS { 0 } else { x >> y as u32 }
            },
            BinOp::Cmpe => (x == y) as Word,
            BinOp::Cmpa => (x > y) as Word,
            BinOp::Cmpae => (x >= y) as Word,
            BinOp::Cmpg => ((x as i64) > (y as i64)) as Word,
            BinOp::Cmpge => ((x as i64) >= (y as i64)) as Word,
        }
    }
}
