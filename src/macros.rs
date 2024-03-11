

macro_rules! define_numbered_enum {
    (
        $(#[$attr:meta])*
        $vis:vis enum $Enum:ident {
            $($Variant:ident,)*
        }
    ) => {
        $(#[$attr])*
        $vis enum $Enum {
            $($Variant,)*
        }

        impl $Enum {
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




#[cfg(feature = "verbose")]
macro_rules! die {
    ($($args:tt)*) => {
        panic!("proof failed: {}", format_args!($($args)*))
    };
}

// TODO: microram version, which just triggers an assertion fail and doesn't panic
#[cfg(not(feature = "verbose"))]
macro_rules! die {
    ($($args:tt)*) => {
        {
            let _ = format_args!($($args)*);
            panic!("proof failed")
        }
    };
}

macro_rules! require {
    ($cond:expr) => {
        require!($cond, stringify!($cond))
    };
    ($cond:expr, $($args:tt)*) => {
        if !$cond {
            die!($($args)*);
        }
    };
}

macro_rules! require_eq {
    ($x:expr, $y:expr) => {
        require!($x == $y)
    };
    ($x:expr, $y:expr, $($args:tt)*) => {
        require!(
            $x == $y,
            "{} (when checking {} == {}, {:?} != {:?})",
            format_args!($($args)*),
            stringify!($x),
            stringify!($y),
            $x,
            $y,
        )
    };
}
