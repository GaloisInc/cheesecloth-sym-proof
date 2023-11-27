use crate::{Word, BinOp};
use crate::logic::VarId;
use crate::logic::print::Printer;


mod imp_interner {
    #![cfg_attr(feature = "playback_term_table", allow(dead_code))]
    use core::cell::RefCell;
    use std::collections::HashSet;
    use core::hash::{Hash, Hasher};
    use core::marker::PhantomData;
    use core::mem::{self, ManuallyDrop};
    use bumpalo::Bump;
    use crate::logic::term::TermKind;

    #[derive(Default)]
    struct Interner {
        storage: ManuallyDrop<Bump>,
        hash: ManuallyDrop<HashSet<&'static TermKind>>,
    }

    impl Drop for Interner {
        fn drop(&mut self) {
            unsafe {
                // Drop `hash` first to avoid dangling references into `storage`.
                ManuallyDrop::drop(&mut self.hash);
                // Dropping `storage` doesn't run `Drop` on the values inside, so nothing will
                // observe the dangling internal references as the arena deallocates each of its
                // chunks.
                ManuallyDrop::drop(&mut self.storage);
            }
        }
    }

    thread_local! {
        static INTERNER: RefCell<Interner> = RefCell::new(Interner::default());
    }


    /// An expression producing a value of type `Word`.
    #[derive(Copy, Clone, Debug)]
    pub struct Term(
        &'static TermKind,
        /// Make this type `!Send` and `!Sync`, so one thread can't obtain a `Term` allocated in
        /// a different thread's interner.
        PhantomData<*mut u8>,
    );

    impl PartialEq for Term {
        fn eq(&self, other: &Term) -> bool {
            self.0 as *const TermKind == other.0 as *const TermKind
        }

        fn ne(&self, other: &Term) -> bool {
            self.0 as *const TermKind != other.0 as *const TermKind
        }
    }

    impl Eq for Term {}

    impl Hash for Term {
        fn hash<H: Hasher>(&self, state: &mut H) {
            (self.0 as *const TermKind).hash(state)
        }
    }

    impl Term {
        pub fn intern(kind: TermKind) -> Term {
            INTERNER.with(|interner| {
                let mut interner = interner.borrow_mut();
                match interner.hash.get(&kind) {
                    Some(x) => Term(x, PhantomData),
                    None => {
                        let alloc = interner.storage.alloc(kind);
                        let alloc = unsafe {
                            // Extend the lifetime to `'static`.  The allocation is in a
                            // thread-local, so it will remain live until the end of the current
                            // thread.  `Term` is also `!Send`, so the reference won't outlive the
                            // current thread.
                            //
                            // However, this is still UNSOUND if `Term`s are stored into other
                            // `thread_local!` variables.  The order in which different
                            // `thread_local`s are dropped is not specified, so it's possible that
                            // the interner is dropped, then another `thread_local` is dropped, and
                            // the second `thread_local` observes the now-dangling `Term`s.  We
                            // work around this by not having any other `thread_local`s that could
                            // inspect `Term`s in their destructors.
                            mem::transmute::<&TermKind, &'static TermKind>(alloc)
                        };
                        interner.hash.insert(alloc);
                        let t = Term(alloc, PhantomData);
                        #[cfg(feature = "recording_term_table")] {
                            crate::advice::term_table::recording::record(t);
                        }
                        t
                    },
                }
            })
        }

        pub fn kind(&self) -> TermKind {
            *self.0
        }

        /// Get a raw pointer that uniquely identifies this `Term`.
        ///
        /// This returns `*const ()` because the underlying pointee type may be either `TermKind`
        /// or `RawTermKind`, depending on which `Term` implementation is in use.
        pub fn as_ptr(&self) -> *const () {
            self.0 as *const TermKind as *const ()
        }
    }
}

mod imp_prealloc {
    #![cfg_attr(not(feature = "playback_term_table"), allow(dead_code))]
    use core::hash::{Hash, Hasher};
    use core::marker::PhantomData;
    #[allow(unused)] use crate::advice::{PlaybackStreamTag, RecordingStreamTag};
    use crate::advice::term_table::RawTermKind;
    use crate::advice::term_table::playback;
    use crate::logic::term::TermKind;


    /// An expression producing a value of type `Word`.
    #[derive(Copy, Clone, Debug)]
    pub struct Term(
        &'static RawTermKind,
        /// Make this type `!Send` and `!Sync`, so one thread can't obtain a `Term` allocated in
        /// a different thread's interner.
        PhantomData<*mut u8>,
    );

    impl PartialEq for Term {
        fn eq(&self, other: &Term) -> bool {
            self.0 as *const RawTermKind == other.0 as *const RawTermKind
        }

        fn ne(&self, other: &Term) -> bool {
            self.0 as *const RawTermKind != other.0 as *const RawTermKind
        }
    }

    impl Eq for Term {}

    impl Hash for Term {
        fn hash<H: Hasher>(&self, state: &mut H) {
            (self.0 as *const RawTermKind).hash(state)
        }
    }

    impl Term {
        pub fn intern(kind: TermKind) -> Term {
            #[cfg(not(feature = "playback_term_intern_index"))] {
                let index = playback::kind_to_index(kind);
                #[cfg(feature = "recording_term_intern_index")] {
                    crate::advice::recording::term_intern_index::Tag.record(&index);
                }
                return Self::from_table_index(index);
            }

            #[cfg(feature = "playback_term_intern_index")] {
                let index = crate::advice::playback::term_intern_index::Tag.playback::<usize>();
                let t = Self::from_table_index(index);
                require_eq!(t.kind(), kind, "bad advice: wrong index for interned term");
                t
            }
        }

        pub fn from_table_index(index: usize) -> Term {
            Term(playback::get_index(index), PhantomData)
        }

        /// This should only be called by `term_table::playback`.  `*raw` must be valid to pass to
        /// `playback::term_kind_from_raw`.
        pub unsafe fn from_raw(raw: &'static RawTermKind) -> Term {
            Term(raw, PhantomData)
        }

        pub fn kind(&self) -> TermKind {
            unsafe {
                playback::term_kind_from_raw(*self.0)
            }
        }

        /// Get a raw pointer that uniquely identifies this `Term`.
        ///
        /// This returns `*const ()` because the underlying pointee type may be either `TermKind`
        /// or `RawTermKind`, depending on which `Term` implementation is in use.
        pub fn as_ptr(&self) -> *const () {
            self.0 as *const RawTermKind as *const ()
        }
    }
}


#[cfg(not(feature = "playback_term_table"))]
pub use imp_interner::Term;
#[cfg(feature = "playback_term_table")]
pub use imp_prealloc::Term;

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum TermKind {
    Const(Word),
    Var(VarId),
    Not(Term),
    Binary(BinOp, Term, Term),
    Mux(Term, Term, Term),
}

impl Term {
    pub fn const_(x: Word) -> Term {
        Term::intern(TermKind::Const(x))
    }

    pub fn is_const(&self) -> bool {
        self.as_const().is_some()
    }

    pub fn as_const(&self) -> Option<Word> {
        match self.kind() {
            TermKind::Const(x) => Some(x),
            _ => None,
        }
    }

    pub fn as_const_or_err(&self) -> Result<Word, String> {
        match self.kind() {
            TermKind::Const(x) => Ok(x),
            ref t => Err(format!("expected const, but got {}", Printer::new(0).display(t))),
        }
    }

    /// Create a new `Var` with a specific `VarId`.  There are no checks to ensure that the `VarId`
    /// makes sense in context.  For generating fresh variables, use `VarCounter` instead.
    pub fn var_unchecked(v: VarId) -> Term {
        Term::intern(TermKind::Var(v))
    }

    pub fn as_var(&self) -> Option<VarId> {
        match self.kind() {
            TermKind::Var(v) => Some(v),
            _ => None,
        }
    }

    pub fn not(t: Term) -> Term {
        if let Some(x) = t.as_const() {
            Term::const_(!x)
        } else {
            Term::intern(TermKind::Not(t))
        }
    }

    pub fn binary(op: BinOp, a: Term, b: Term) -> Term {
        if let (Some(x), Some(y)) = (a.as_const(), b.as_const()) {
            return Term::const_(op.eval(x, y));
        }

        // Normalization rules
        match op {
            BinOp::Add => {
                // Put the constant on the right whenever possible.
                if a.is_const() && !b.is_const() {
                    return Term::add(b, a);
                }
                // When adding to an existing `x + c`, fold the constants together.
                if let Some(bc) = b.as_const() {
                    if bc == 0 {
                        return a;
                    }
                    if let TermKind::Binary(BinOp::Add, x, y) = a.kind() {
                        if let Some(yc) = y.as_const() {
                            return Term::add(x, Term::const_(bc.wrapping_add(yc)));
                        }
                    }
                }
            },
            BinOp::Sub => {
                // Turn `x - c` into `x + (-c)`.
                if let Some(bc) = b.as_const() {
                    if bc == 0 {
                        return a;
                    }
                    return Term::add(a, Term::const_(bc.wrapping_neg()));
                }
            },
            BinOp::Mull => {
                // Put the constant on the right whenever possible.
                if a.is_const() && !b.is_const() {
                    return Term::mull(b, a);
                }
                // Turn `(x + y) * c` into `x * c + y * c` if either `x` or `y` is a constant.
                if let Some(bc) = b.as_const() {
                    if bc == 0 {
                        return Term::const_(0);
                    }
                    if let TermKind::Binary(BinOp::Add, x, y) = a.kind() {
                        if x.is_const() || y.is_const() {
                            return Term::add(
                                Term::mull(x, b),
                                Term::mull(y, b),
                            );
                        }
                    }
                }
            },
            _ => {},
        }

        Term::intern(TermKind::Binary(op, a, b))
    }

    pub fn mux(c: Term, t: Term, e: Term) -> Term {
        if let Some(c) = c.as_const() {
            if c != 0 {
                t
            } else {
                e
            }
        } else {
            Term::intern(TermKind::Mux(c, t, e))
        }
    }

    pub fn and(a: Term, b: Term) -> Term { Term::binary(BinOp::And, a, b) }
    pub fn or(a: Term, b: Term) -> Term { Term::binary(BinOp::Or, a, b) }
    pub fn xor(a: Term, b: Term) -> Term { Term::binary(BinOp::Xor, a, b) }
    pub fn add(a: Term, b: Term) -> Term { Term::binary(BinOp::Add, a, b) }
    pub fn sub(a: Term, b: Term) -> Term { Term::binary(BinOp::Sub, a, b) }
    pub fn mull(a: Term, b: Term) -> Term { Term::binary(BinOp::Mull, a, b) }
    pub fn umulh(a: Term, b: Term) -> Term { Term::binary(BinOp::Umulh, a, b) }
    pub fn smulh(a: Term, b: Term) -> Term { Term::binary(BinOp::Smulh, a, b) }
    pub fn udiv(a: Term, b: Term) -> Term { Term::binary(BinOp::Udiv, a, b) }
    pub fn umod(a: Term, b: Term) -> Term { Term::binary(BinOp::Umod, a, b) }
    pub fn shl(a: Term, b: Term) -> Term { Term::binary(BinOp::Shl, a, b) }
    pub fn shr(a: Term, b: Term) -> Term { Term::binary(BinOp::Shr, a, b) }
    pub fn cmpe(a: Term, b: Term) -> Term { Term::binary(BinOp::Cmpe, a, b) }
    pub fn cmpa(a: Term, b: Term) -> Term { Term::binary(BinOp::Cmpa, a, b) }
    pub fn cmpae(a: Term, b: Term) -> Term { Term::binary(BinOp::Cmpae, a, b) }
    pub fn cmpg(a: Term, b: Term) -> Term { Term::binary(BinOp::Cmpg, a, b) }
    pub fn cmpge(a: Term, b: Term) -> Term { Term::binary(BinOp::Cmpge, a, b) }

    /// Build the term `a + n`.  If `a` has the form `b + m` where `m` is a constant, this folds
    /// the two additions together into `b + (n + m)`.
    pub fn increment(a: Term, n: Word) -> Term {
        if let TermKind::Binary(BinOp::Add, b, m) = a.kind() {
            if let Some(m) = m.as_const() {
                return Term::add(b, Term::const_(n + m));
            }
        }
        Term::add(a, Term::const_(n))
    }

    pub fn as_var_plus_const(&self) -> Option<(VarId, Word)> {
        match self.kind() {
            TermKind::Var(v) => Some((v, 0)),
            TermKind::Binary(BinOp::Add, x, y) => {
                let v = x.as_var()?;
                let c = y.as_const()?;
                Some((v, c))
            },
            _ => None,
        }
    }

    /// Apply `f` to each `VarId` mentioned in `self`.  `f` should return `None` to keep traversing
    /// or `Some(x)` to break out; in the latter case, the return value of `for_each_var` will also
    /// be `Some(x)`.
    pub fn for_each_var<T>(&self, f: &mut impl FnMut(VarId) -> Option<T>) -> Option<T> {
        match self.kind() {
            TermKind::Const(_) => None,
            TermKind::Var(v) => {
                f(v)
            },
            TermKind::Not(t) => {
                t.for_each_var(f)
            },
            TermKind::Binary(_, t1, t2) => {
                t1.for_each_var(f)
                    .or_else(|| t2.for_each_var(f))
            },
            TermKind::Mux(t1, t2, t3) => {
                t1.for_each_var(f)
                    .or_else(|| t2.for_each_var(f))
                    .or_else(|| t3.for_each_var(f))
            },
        }
    }
}

impl From<Word> for Term {
    fn from(x: Word) -> Term { Term::const_(x) }
}
