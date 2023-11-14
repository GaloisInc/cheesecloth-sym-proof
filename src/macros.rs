

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

