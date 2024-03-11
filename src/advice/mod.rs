use core::any;
use core::array;
use core::cell::Cell;
use core::convert::{TryFrom, TryInto};
use core::mem::{self, MaybeUninit};
use alloc::boxed::Box;
use alloc::vec::Vec;
#[cfg(not(feature = "microram_api"))] use std::io::{Read, Write};
#[cfg(not(feature = "microram_api"))] use std::panic::{self, UnwindSafe};
use log::trace;
use crate::{Word, BinOp};
use crate::logic::{Term, VarId, VarCounter, Binder, Prop, ReachableProp, StatePred};
use crate::micro_ram::MemWidth;
use crate::symbolic::{self, MemState, MemConcrete, MemMap, MemSnapshot, MemLog, MemMulti};


pub mod map;
pub mod term_table;
pub mod vec;


pub type Value = u64;

#[cfg(feature = "microram_api")]
extern "C" {
    fn __cc_advise(max: Value) -> Value;
}


#[allow(dead_code)]
struct FakeThreadLocal<T>(pub T);

unsafe impl<T> Sync for FakeThreadLocal<T> {}

impl<T> FakeThreadLocal<T> {
    #[allow(dead_code)]
    pub fn with<R>(&self, f: impl FnOnce(&T) -> R) -> R {
        f(&self.0)
    }
}


#[cfg(not(feature = "microram_api"))]
use std::thread_local;

#[cfg(feature = "microram_api")]
macro_rules! thread_local {
    (
        static $NAME:ident: $Ty:ty = $init:expr;
    ) => {
        static $NAME: $crate::advice::FakeThreadLocal<$Ty> =
            $crate::advice::FakeThreadLocal($init);
    };
}


thread_local! {
    static RECORDING_ENABLED: Cell<bool> = Cell::new(true);
}

/// Temporarily disable recording for the duration of the closure.
pub fn dont_record<R>(f: impl FnOnce() -> R) -> R {
    let old = RECORDING_ENABLED.with(|c| c.replace(false));
    let r = f();
    RECORDING_ENABLED.with(|c| c.set(old));
    r
}

pub fn is_recording() -> bool {
    RECORDING_ENABLED.with(|c| c.get())
}


pub struct RecordingStream {
    buf: Vec<Value>,
}

impl RecordingStream {
    pub const fn new() -> RecordingStream {
        RecordingStream {
            buf: Vec::new(),
        }
    }

    pub fn put(&mut self, v: Value) {
        if is_recording() {
            self.buf.push(v);
        }
    }

    #[cfg(not(feature = "microram_api"))]
    pub fn finish(self, w: impl Write) -> serde_cbor::Result<()> {
        serde_cbor::to_writer(w, &self.buf)
    }

    fn snapshot(&self) -> usize {
        self.buf.len()
    }

    fn rewind(&mut self, snap: usize) {
        self.buf.truncate(snap);
    }
}

pub trait RecordingStreamTag: Sized + Copy {
    fn with<R>(self, f: impl FnOnce(&mut RecordingStream) -> R) -> R;

    fn put(self, v: Value) {
        self.with(|rs| {
            trace!("{}: put {} at index {}", any::type_name::<Self>(), v, rs.buf.len());
            rs.put(v);
        })
    }

    fn put_cast<T: TryInto<Value>>(self, v: T) {
        self.put(v.try_into().ok().unwrap());
    }

    #[cfg(not(feature = "microram_api"))]
    fn finish(self, w: impl Write) -> serde_cbor::Result<()> {
        self.with(|rs| mem::replace(rs, RecordingStream::new()).finish(w))
    }

    fn record<T: Record + ?Sized>(self, x: &T) {
        x.record_into(self);
    }
}

macro_rules! recording_stream {
    ($name:ident) => {
        pub mod $name {
            use core::cell::RefCell;
            #[cfg(not(feature = "microram_api"))] use std::thread_local;
            use crate::advice::{RecordingStream, RecordingStreamTag};

            thread_local! {
                static STREAM: RefCell<RecordingStream> = RefCell::new(RecordingStream::new());
            }

            #[derive(Clone, Copy, Debug, Default)]
            pub struct Tag;

            impl RecordingStreamTag for Tag {
                fn with<R>(self, f: impl FnOnce(&mut RecordingStream) -> R) -> R {
                    STREAM.with(|c| f(&mut c.borrow_mut()))
                }
            }
        }
    };
}


/// Like `RecordingStream`, but the advice stream is divided into chunks.  Instead of recording
/// values in order, the caller allocates chunks and later records values into each chunk.  When
/// `finish` is called, the final witness stream is assembled based on the order of chunk
/// allocation.  For example:
///
/// ```ignore
/// let mut crs = ChunkedRecordingStream::new();
/// let a = crs.add_chunk();
/// let b = crs.add_chunk();
/// crs.get_mut(a).put(1);
/// crs.get_mut(b).put(2);
/// crs.get_mut(a).put(3);
/// crs.finish(...);
/// ```
///
/// The output advice stream is `[1, 3, 2]`, since chunk `a` contains `[1, 3]` and chunk `b`
/// contains `[2]`.
pub struct ChunkedRecordingStream {
    chunks: Vec<RecordingStream>,
    /// IDs of chunks that will not be included in the output.  When `add_chunk` is called while
    /// `!is_recording()`, a chunk is created, but the chunk is also added to this set.
    omit_chunks: Vec<ChunkId>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct ChunkId(usize);

impl ChunkedRecordingStream {
    pub const fn new() -> ChunkedRecordingStream {
        ChunkedRecordingStream {
            chunks: Vec::new(),
            omit_chunks: Vec::new(),
        }
    }

    pub fn add_chunk(&mut self) -> ChunkId {
        let id = ChunkId(self.chunks.len());
        self.chunks.push(RecordingStream::new());
        if !is_recording() {
            self.omit_chunks.push(id);
        }
        id
    }

    pub fn get(&self, id: ChunkId) -> &RecordingStream {
        &self.chunks[id.0]
    }

    pub fn get_mut(&mut self, id: ChunkId) -> &mut RecordingStream {
        &mut self.chunks[id.0]
    }

    #[cfg(not(feature = "microram_api"))]
    pub fn finish(self, w: impl Write) -> serde_cbor::Result<()> {
        use std::collections::HashSet;
        let omit = self.omit_chunks.into_iter().collect::<HashSet<_>>();
        let buf = self.chunks.into_iter().enumerate()
            .filter(|&(i, _)| !omit.contains(&ChunkId(i)))
            .flat_map(|(_, rs)| rs.buf.into_iter())
            .collect::<Vec<_>>();
        serde_cbor::to_writer(w, &buf)
    }

    fn snapshot(&self) -> Vec<usize> {
        self.chunks.iter().map(|rs| rs.snapshot()).collect()
    }

    fn rewind(&mut self, snap: Vec<usize>) {
        self.chunks.truncate(snap.len());
        for (chunk, snap) in self.chunks.iter_mut().zip(snap.into_iter()) {
            chunk.rewind(snap);
        }
    }
}

pub trait ChunkedRecordingStreamTag: Sized + Copy {
    type ChunkTag: RecordingStreamTag;

    fn with<R>(self, f: impl FnOnce(&mut ChunkedRecordingStream) -> R) -> R;

    fn mk_chunk_tag(self, id: ChunkId) -> Self::ChunkTag;

    fn add_chunk(self) -> Self::ChunkTag {
        let id = self.with(|crs| crs.add_chunk());
        self.mk_chunk_tag(id)
    }

    #[cfg(not(feature = "microram_api"))]
    fn finish(self, w: impl Write) -> serde_cbor::Result<()> {
        self.with(|crs| mem::replace(crs, ChunkedRecordingStream::new()).finish(w))
    }

}

macro_rules! chunked_recording_stream {
    ($name:ident) => {
        pub mod $name {
            use core::cell::RefCell;
            #[cfg(not(feature = "microram_api"))] use std::thread_local;
            use crate::advice::{
                RecordingStream, RecordingStreamTag,
                ChunkedRecordingStream, ChunkedRecordingStreamTag, ChunkId,
            };

            thread_local! {
                static STREAM: RefCell<ChunkedRecordingStream> =
                    RefCell::new(ChunkedRecordingStream::new());
            }

            #[derive(Clone, Copy, Debug)]
            pub struct Tag;

            impl ChunkedRecordingStreamTag for Tag {
                type ChunkTag = ChunkTag;

                fn with<R>(self, f: impl FnOnce(&mut ChunkedRecordingStream) -> R) -> R {
                    STREAM.with(|c| f(&mut *c.borrow_mut()))
                }

                fn mk_chunk_tag(self, id: ChunkId) -> Self::ChunkTag {
                    ChunkTag(id)
                }
            }

            #[derive(Clone, Copy, Debug)]
            pub struct ChunkTag(ChunkId);

            impl RecordingStreamTag for ChunkTag {
                fn with<R>(self, f: impl FnOnce(&mut RecordingStream) -> R) -> R {
                    STREAM.with(|c| f(c.borrow_mut().get_mut(self.0)))
                }
            }
        }
    };
}


pub struct PlaybackStream {
    buf: Vec<Value>,
    pos: usize,
    inited: bool,
}

impl PlaybackStream {
    pub const fn new() -> PlaybackStream {
        PlaybackStream {
            buf: Vec::new(),
            pos: 0,
            inited: false,
        }
    }

    #[cfg(not(feature = "microram_api"))]
    pub fn load(&mut self, r: impl Read) -> serde_cbor::Result<()> {
        assert!(!self.inited, "stream has already been initialized");
        let buf = serde_cbor::from_reader(r)?;
        self.buf = buf;
        self.pos = 0;
        self.inited = true;
        Ok(())
    }

    #[cfg(not(feature = "microram_api"))]
    pub fn take(&mut self) -> Value {
        assert!(self.inited, "tried to read from uninitialized stream");
        assert!(self.pos < self.buf.len(), "tried to read past end of stream (at {})", self.pos);
        let v = self.buf[self.pos];
        #[cfg(feature = "recording_linear")] {
            recording::linear::Tag.put(v);
        }
        self.pos += 1;
        v
    }

    #[cfg(not(feature = "microram_api"))]
    pub fn take_bounded(&mut self, max: Value) -> Value {
        let v = self.take();
        assert!(v <= max);
        v
    }

    #[cfg(feature = "microram_api")]
    pub fn take(&mut self) -> Value {
        self.take_bounded(Value::MAX)
    }

    #[cfg(feature = "microram_api")]
    pub fn take_bounded(&mut self, max: Value) -> Value {
        unsafe { __cc_advise(max) }
    }
}

pub trait PlaybackStreamTag: Sized + Copy {
    fn with<R>(self, f: impl FnOnce(&mut PlaybackStream) -> R) -> R;

    #[cfg(not(feature = "microram_api"))]
    fn load(self, r: impl Read) -> serde_cbor::Result<()> {
        self.with(|ps| ps.load(r))
    }

    fn take(self) -> Value {
        self.with(|ps| {
            let v = ps.take();
            trace!("{}: take {} from index {}", any::type_name::<Self>(), v, ps.pos - 1);
            v
        })
    }

    fn take_bounded(self, max: Value) -> Value {
        self.with(|ps| {
            let v = ps.take_bounded(max);
            trace!("{}: take {} from index {}", any::type_name::<Self>(), v, ps.pos - 1);
            v
        })
    }

    fn take_cast<T: TryFrom<Value>>(self) -> T {
        self.take().try_into().ok().unwrap()
    }

    fn take_bounded_cast<T>(self, max: T) -> T
    where T: TryFrom<Value>, Value: TryFrom<T> {
        let max = Value::try_from(max).ok().unwrap();
        self.take_bounded(max).try_into().ok().unwrap()
    }

    fn take_index<T>(self, xs: &[T]) -> usize {
        assert!(xs.len() > 0, "can't choose from empty list");
        self.take_bounded_cast(xs.len() - 1)
    }

    fn take_elem<'a, T>(self, xs: &'a [T]) -> &'a T {
        let idx = self.take_index(xs);
        &xs[idx]
    }

    fn take_index_and_elem<'a, T>(self, xs: &'a [T]) -> (usize, &'a T) {
        let idx = self.take_index(xs);
        (idx, &xs[idx])
    }

    fn playback<T: Playback>(self) -> T {
        T::playback_from(self)
    }
}

macro_rules! playback_stream_inner {
    ($name:ident) => {
        pub mod $name {
            use core::cell::RefCell;
            #[cfg(not(feature = "microram_api"))] use std::thread_local;
            use crate::advice::{PlaybackStream, PlaybackStreamTag};

            thread_local! {
                static STREAM: RefCell<PlaybackStream> = RefCell::new(PlaybackStream::new());
            }

            #[derive(Clone, Copy, Debug, Default)]
            pub struct Tag;

            impl PlaybackStreamTag for Tag {
                fn with<R>(self, f: impl FnOnce(&mut PlaybackStream) -> R) -> R {
                    STREAM.with(|c| f(&mut c.borrow_mut()))
                }
            }
        }
    };
}

#[cfg(not(feature = "playback_linear"))]
macro_rules! playback_stream {
    ($name:ident) => { playback_stream_inner!($name); };
}

// With `playback_linear` enabled, all playback streams are replace with aliases for `linear`.
#[cfg(feature = "playback_linear")]
macro_rules! playback_stream {
    (linear) => { playback_stream_inner!(linear); };
    ($name:ident) => {
        pub mod $name {
            pub use super::linear::Tag;
        }
    };
}


pub trait Record: core::fmt::Debug {
    fn record_into(&self, rs: impl RecordingStreamTag);
}

pub trait Playback: core::fmt::Debug {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self;
}


macro_rules! impl_record_playback_for_primitive {
    ($T:ty) => {
        impl Record for $T {
            fn record_into(&self, rs: impl RecordingStreamTag) {
                rs.put_cast(*self);
            }
        }

        impl Playback for $T {
            fn playback_from(ps: impl PlaybackStreamTag) -> Self {
                if Value::try_from(<$T>::MAX).is_ok() {
                    ps.take_bounded_cast(<$T>::MAX)
                } else {
                    ps.take_cast()
                }
            }
        }
    };
}

impl_record_playback_for_primitive!(u8);
impl_record_playback_for_primitive!(u16);
impl_record_playback_for_primitive!(u32);
impl_record_playback_for_primitive!(u64);
impl_record_playback_for_primitive!(usize);

impl Record for bool {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        rs.put_cast(*self);
    }
}

impl Playback for bool {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        ps.take_bounded(1) != 0
    }
}


impl<T: Record + ?Sized> Record for &'_ T {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        rs.record::<T>(self)
    }
}

impl<T: Record + ?Sized> Record for Box<T> {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        rs.record::<T>(self)
    }
}

impl<T: Playback> Playback for Box<T> {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        Box::new(ps.playback::<T>())
    }
}


impl<T: Record> Record for [T] {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        rs.record(&self.len());
        for x in self {
            rs.record(x);
        }
    }
}

impl<T: Playback> Playback for Box<[T]> {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        ps.playback::<Vec<T>>().into_boxed_slice()
    }
}

impl<T: Record> Record for Vec<T> {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        rs.record::<[T]>(self)
    }
}

impl<T: Playback> Playback for Vec<T> {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        let len = ps.playback::<usize>();
        let mut v = Vec::with_capacity(len);
        for _ in 0 .. len {
            v.push(ps.playback::<T>());
        }
        v
    }
}


impl<T: Record> Record for Option<T> {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        match *self {
            None => {
                rs.put(0);
            },
            Some(ref x) => {
                rs.put(1);
                rs.record::<T>(x);
            },
        }
    }
}

impl<T: Playback> Playback for Option<T> {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        match ps.take_bounded(1) {
            0 => None,
            1 => {
                let x = ps.playback::<T>();
                Some(x)
            },
            _ => unreachable!(),
        }
    }
}


impl<T: Record, const N: usize> Record for [T; N] {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        // Don't go through `record::<[T]>` since we don't need a length prefix.
        for x in self {
            rs.record::<T>(x);
        }
    }
}

impl<T: Playback, const N: usize> Playback for [T; N] {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        unsafe {
            let mut arr = MaybeUninit::<[T; N]>::uninit();
            let ptr = arr.as_mut_ptr() as *mut T;
            for i in 0 .. N {
                ptr.add(i).write(ps.playback());
            }
            arr.assume_init()
        }
    }
}



macro_rules! impl_record_playback_for_tuple {
    ($($A:ident)*) => {
        impl<$($A: Record,)*> Record for ($($A,)*) {
            // `rs` is unused in the zero-element case
            #[allow(unused)]
            fn record_into(&self, rs: impl RecordingStreamTag) {
                #![allow(bad_style)]
                let ($(ref $A,)*) = *self;
                $( rs.record::<$A>($A); )*
            }
        }

        impl<$($A: Playback,)*> Playback for ($($A,)*) {
            // `rs` is unused in the zero-element case
            #[allow(unused)]
            fn playback_from(ps: impl PlaybackStreamTag) -> Self {
                #![allow(bad_style)]
                $( let $A = ps.playback::<$A>(); )*
                ($($A,)*)
            }
        }
    };
}

impl_record_playback_for_tuple!();
impl_record_playback_for_tuple!(A);
impl_record_playback_for_tuple!(A B);
impl_record_playback_for_tuple!(A B C);
impl_record_playback_for_tuple!(A B C D);
impl_record_playback_for_tuple!(A B C D E);
impl_record_playback_for_tuple!(A B C D E F);
impl_record_playback_for_tuple!(A B C D E F G);
impl_record_playback_for_tuple!(A B C D E F G H);
impl_record_playback_for_tuple!(A B C D E F G H I);
impl_record_playback_for_tuple!(A B C D E F G H I J);
impl_record_playback_for_tuple!(A B C D E F G H I J K);
impl_record_playback_for_tuple!(A B C D E F G H I J K L);


impl Record for VarId {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        rs.record(&self.as_raw());
    }
}

impl Playback for VarId {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        VarId::from_raw(ps.playback())
    }
}

impl Record for VarCounter {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        rs.record(&self.as_raw());
    }
}

impl Playback for VarCounter {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        VarCounter::from_raw(ps.playback())
    }
}

impl<T: Record> Record for Binder<T> {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        rs.record(&self.vars);
        rs.record::<T>(&self.inner);
    }
}

impl<T: Playback> Playback for Binder<T> {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        let vars = ps.playback::<VarCounter>();
        let inner = ps.playback::<T>();
        Binder::from_parts(vars, inner)
    }
}

impl Record for BinOp {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        rs.record(&self.as_raw());
    }
}

impl Playback for BinOp {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        BinOp::from_raw(ps.playback())
    }
}

impl Record for MemWidth {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        match *self {
            MemWidth::W1 => rs.put(0),
            MemWidth::W2 => rs.put(1),
            MemWidth::W4 => rs.put(2),
            MemWidth::W8 => rs.put(3),
        }
    }
}

impl Playback for MemWidth {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        match ps.take_bounded(4) {
            0 => MemWidth::W1,
            1 => MemWidth::W2,
            2 => MemWidth::W4,
            3 => MemWidth::W8,
            _ => unreachable!(),
        }
    }
}


impl Record for Term {
    fn record_into(&self, _rs: impl RecordingStreamTag) {
        #[cfg(feature = "recording_terms")] {
            use crate::logic::term::TermKind;
            let rs = recording::terms::Tag;
            match self.kind() {
                TermKind::Const(x) => {
                    rs.put(0);
                    rs.record(&x);
                },
                TermKind::Var(v) => {
                    rs.put(1);
                    rs.record(&v);
                },
                TermKind::Not(a) => {
                    rs.put(2);
                    rs.record(&a);
                },
                TermKind::Binary(op, a, b) => {
                    rs.put(3);
                    rs.record(&op);
                    rs.record(&a);
                    rs.record(&b);
                },
                TermKind::Mux(a, b, c) => {
                    rs.put(4);
                    rs.record(&a);
                    rs.record(&b);
                    rs.record(&c);
                },
            }
            return;
        }

        #[cfg(feature = "recording_term_index")] {
            // The intended workflow is to run with `recording_terms`, then later run again with
            // `playback_terms` and `recording_term_index` to convert explicit terms to term
            // indices.
            panic!("recording directly into `term_index` is not supported");
        }
    }
}

thread_local! {
    static PLAYBACK_TERM_IS_TOP_LEVEL: Cell<bool> = Cell::new(true);
}

/// Enter playback of a term.  The callback argument is `true` if the term being played back is at
/// top level, or `false` if we were already in the process of playing back a term.
#[cfg(feature = "playback_terms")]
fn playback_enter_term<R>(f: impl FnOnce(bool) -> R) -> R {
    let is_top_level = PLAYBACK_TERM_IS_TOP_LEVEL.with(|c| c.replace(false));
    let r = f(is_top_level);
    PLAYBACK_TERM_IS_TOP_LEVEL.with(|c| c.set(is_top_level));
    r
}

impl Playback for Term {
    fn playback_from(_ps: impl PlaybackStreamTag) -> Self {
        #[cfg(feature = "playback_terms")] {
            return playback_enter_term(|is_top_level| {
                let ps = playback::terms::Tag;
                let t = match ps.take_bounded(4) {
                    0 => {
                        let x = ps.playback::<Word>();
                        Term::const_(x)
                    },
                    1 => {
                        let v = ps.playback::<VarId>();
                        Term::var_unchecked(v)
                    },
                    2 => {
                        let a = ps.playback::<Term>();
                        Term::not(a)
                    },
                    3 => {
                        let op = ps.playback::<BinOp>();
                        let a = ps.playback::<Term>();
                        let b = ps.playback::<Term>();
                        Term::binary(op, a, b)
                    },
                    4 => {
                        let a = ps.playback::<Term>();
                        let b = ps.playback::<Term>();
                        let c = ps.playback::<Term>();
                        Term::mux(a, b, c)
                    },
                    _ => unreachable!(),
                };

                #[cfg(feature = "recording_term_index")] {
                    if is_top_level {
                        let rs = recording::term_index::Tag;
                        let index = term_table::recording::term_index(t);
                        rs.put_cast(index);
                    }
                }

                t
            });
        }

        #[cfg(feature = "playback_term_index")] {
            let rs = playback::term_index::Tag;
            let bound = term_table::playback::len();
            let index = rs.take_bounded_cast::<usize>(bound);
            return Term::from_table_index(index);
        }

        #[cfg(not(any(feature = "playback_terms", feature = "playback_term_index")))] {
            panic!("no term playback mode is enabled");
        }
    }
}


impl Record for Prop {
    fn record_into(&self, _rs: impl RecordingStreamTag) {
        let rs = recording::props::Tag;
        match *self {
            Prop::Nonzero(t) => {
                rs.put(0);
                rs.record(&t);
            },
            Prop::Forall(ref bnd) => {
                rs.put(1);
                rs.record(bnd);
            },
            Prop::Reachable(ref rp) => {
                rs.put(2);
                rs.record(rp);
            },
        }
    }
}

impl Playback for Prop {
    fn playback_from(_ps: impl PlaybackStreamTag) -> Self {
        let ps = playback::props::Tag;
        match ps.take_bounded(2) {
            0 => {
                let t = ps.playback::<Term>();
                Prop::Nonzero(t)
            },
            1 => {
                let bnd = ps.playback();
                Prop::Forall(bnd)
            },
            2 => {
                let rp = ps.playback::<ReachableProp>();
                Prop::Reachable(rp)
            },
            _ => unreachable!(),
        }
    }
}


impl Record for ReachableProp {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        let ReachableProp { ref pred, min_cycles } = *self;
        rs.record(pred);
        rs.record(&min_cycles);
    }
}

impl Playback for ReachableProp {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        let pred = ps.playback::<Binder<StatePred>>();
        let min_cycles = ps.playback::<Term>();
        ReachableProp { pred, min_cycles }
    }
}


impl Record for StatePred {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        let StatePred { ref state, ref props } = *self;
        rs.record(state);
        rs.record(props);
    }
}

impl Playback for StatePred {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        let state = ps.playback::<symbolic::State>();
        let props = ps.playback();
        StatePred { state, props }
    }
}


impl Record for symbolic::State {
    fn record_into(&self, _rs: impl RecordingStreamTag) {
        let rs = recording::states::Tag;
        let symbolic::State {
            pc, ref regs, ref mem,
            #[cfg(feature = "debug_symbolic")] conc_st: _,
        } = *self;
        rs.record(&pc);
        rs.record(regs);
        rs.record(mem);
    }
}

impl Playback for symbolic::State {
    fn playback_from(_ps: impl PlaybackStreamTag) -> Self {
        let ps = playback::states::Tag;
        let pc = ps.playback::<Word>();
        let regs = ps.playback();
        let mem = ps.playback::<MemState>();
        symbolic::State {
            pc, regs, mem,
            #[cfg(feature = "debug_symbolic")] conc_st: None,
        }
    }
}


impl Record for MemState {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        match *self {
            MemState::Concrete(ref m) => {
                rs.put(0);
                rs.record(m);
            },
            MemState::Map(ref m) => {
                rs.put(1);
                rs.record(m);
            },
            MemState::Snapshot(ref m) => {
                rs.put(2);
                rs.record(m);
            },
            MemState::Log(ref m) => {
                rs.put(3);
                rs.record(m);
            },
            MemState::Multi(ref m) => {
                rs.put(4);
                rs.record(m);
            },
        }
    }
}

impl Playback for MemState {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        match ps.take_bounded(4) {
            0 => MemState::Concrete(ps.playback()),
            1 => MemState::Map(ps.playback()),
            2 => MemState::Snapshot(ps.playback()),
            3 => MemState::Log(ps.playback()),
            4 => MemState::Multi(ps.playback()),
            _ => unreachable!(),
        }
    }
}


impl Record for MemConcrete {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        let _ = rs;
        todo!()
    }
}

impl Playback for MemConcrete {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        let _ = ps;
        todo!()
    }
}

impl Record for MemMap {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        let MemMap { ref m } = *self;
        rs.record(m);
    }
}

impl Playback for MemMap {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        let m = ps.playback();
        MemMap { m }
    }
}

impl Record for MemSnapshot {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        let MemSnapshot { base } = *self;
        rs.record(&base);
    }
}

impl Playback for MemSnapshot {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        let base = ps.playback();
        MemSnapshot { base }
    }
}

impl Record for MemLog {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        let MemLog { ref l } = *self;
        rs.record(l);
    }
}

impl Playback for MemLog {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        let l = ps.playback();
        MemLog { l }
    }
}

impl Record for MemMulti {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        let _ = rs;
        todo!()
    }
}

impl Playback for MemMulti {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        let _ = ps;
        todo!()
    }
}


pub mod recording {
    recording_stream!(rules);
    recording_stream!(props);
    recording_stream!(states);
    recording_stream!(terms);
    recording_stream!(term_index);
    recording_stream!(term_intern_index);
    recording_stream!(search_index);
    chunked_recording_stream!(avec_len);
    chunked_recording_stream!(amap_keys);
    recording_stream!(amap_access);
    recording_stream!(linear);
}

pub mod playback {
    playback_stream!(rules);
    playback_stream!(props);
    playback_stream!(states);
    playback_stream!(terms);
    playback_stream!(term_index);
    playback_stream!(term_intern_index);
    playback_stream!(search_index);
    playback_stream!(avec_len);
    playback_stream!(amap_keys);
    playback_stream!(amap_access);
    playback_stream!(linear);
}


#[cfg(not(feature = "microram"))]
pub fn advice_dir() -> std::path::PathBuf {
    std::env::var_os("SYM_PROOF_ADVICE_DIR").map_or_else(
        || "advice".into(),
        |v| v.into(),
    )
}

#[cfg(not(feature = "microram_api"))]
mod load_finish {
    // Helper functions in this module are used only when certain features are enabled.
    #![allow(dead_code)]
    #![allow(unused_imports)]
    use alloc::borrow::ToOwned;
    use alloc::string::{String, ToString};
    use std::env;
    use std::eprintln;
    use std::fs::{self, File};
    use std::path::{Path, PathBuf};
    use super::{
        recording, playback, term_table, advice_dir, PlaybackStreamTag, RecordingStreamTag,
        ChunkedRecordingStreamTag,
    };


    fn load_file(name: impl AsRef<Path>, ps: impl PlaybackStreamTag) -> Result<(), String> {
        let path = advice_dir().join(name);
        let f = File::open(&path).map_err(|x| x.to_string())?;
        ps.load(f).map_err(|x| x.to_string())?;
        eprintln!("loaded advice: {path:?}");
        Ok(())
    }

    fn load_term_table_from_file(name: impl AsRef<Path>) -> Result<(), String> {
        let path = advice_dir().join(name);
        let f = File::open(&path).map_err(|x| x.to_string())?;
        term_table::playback::load(f).map_err(|x| x.to_string())?;
        eprintln!("loaded advice: {path:?}");
        Ok(())
    }

    #[cfg(not(feature = "playback_linear"))]
    pub fn load() -> Result<(), String> {
        #[cfg(feature = "playback_rules")] {
            load_file("rules.cbor", playback::rules::Tag)?;
            load_file("props.cbor", playback::props::Tag)?;
            load_file("states.cbor", playback::states::Tag)?;
        }
        #[cfg(feature = "playback_terms")] {
            load_file("terms.cbor", playback::terms::Tag)?;
        }
        #[cfg(feature = "playback_term_table")] {
            load_term_table_from_file("term_table.cbor")?;
        }
        #[cfg(feature = "playback_term_index")] {
            load_file("term_index.cbor", playback::term_index::Tag)?;
        }
        #[cfg(feature = "playback_term_intern_index")] {
            load_file("term_intern_index.cbor", playback::term_intern_index::Tag)?;
        }
        #[cfg(feature = "playback_search_index")] {
            load_file("search_index.cbor", playback::search_index::Tag)?;
        }
        #[cfg(feature = "playback_avec_len")] {
            load_file("avec_len.cbor", playback::avec_len::Tag)?;
        }
        #[cfg(feature = "playback_amap_keys")] {
            load_file("amap_keys.cbor", playback::amap_keys::Tag)?;
        }
        #[cfg(feature = "playback_amap_access")] {
            load_file("amap_access.cbor", playback::amap_access::Tag)?;
        }

        Ok(())
    }

    #[cfg(feature = "playback_linear")]
    pub fn load() -> Result<(), String> {
        load_file("linear.cbor", playback::linear::Tag)?;
        #[cfg(feature = "playback_term_table")] {
            load_term_table_from_file("term_table.cbor")?;
        }
        Ok(())
    }


    fn finish_file(name: impl AsRef<Path>, rs: impl RecordingStreamTag) -> Result<(), String> {
        let dir = advice_dir();
        fs::create_dir_all(&dir).map_err(|x| x.to_string())?;
        let path = dir.join(name);
        let f = File::create(&path).map_err(|x| x.to_string())?;
        rs.finish(f).map_err(|x| x.to_string())?;
        eprintln!("saved advice: {path:?}");
        Ok(())
    }

    fn finish_file_chunked(
        name: impl AsRef<Path>,
        crs: impl ChunkedRecordingStreamTag,
    ) -> Result<(), String> {
        let dir = advice_dir();
        fs::create_dir_all(&dir).map_err(|x| x.to_string())?;
        let path = dir.join(name);
        let f = File::create(&path).map_err(|x| x.to_string())?;
        crs.finish(f).map_err(|x| x.to_string())?;
        eprintln!("saved advice: {path:?}");
        Ok(())
    }

    pub fn finish() -> Result<(), String> {
        #[cfg(feature = "recording_rules")] {
            finish_file("rules.cbor", recording::rules::Tag)?;
            finish_file("props.cbor", recording::props::Tag)?;
            finish_file("states.cbor", recording::states::Tag)?;
        }
        #[cfg(feature = "recording_terms")] {
            finish_file("terms.cbor", recording::terms::Tag)?;
        }
        #[cfg(feature = "recording_term_table")] {
            let name = "term_table.cbor";
            let dir = advice_dir();
            fs::create_dir_all(&dir).map_err(|x| x.to_string())?;
            let path = dir.join(name);
            let f = File::create(&path).map_err(|x| x.to_string())?;
            term_table::recording::finish(f).map_err(|x| x.to_string())?;
            eprintln!("saved advice: {path:?}");
        }
        #[cfg(feature = "recording_term_index")] {
            finish_file("term_index.cbor", recording::term_index::Tag)?;
        }
        #[cfg(feature = "recording_term_intern_index")] {
            finish_file("term_intern_index.cbor", recording::term_intern_index::Tag)?;
        }
        #[cfg(feature = "recording_search_index")] {
            finish_file("search_index.cbor", recording::search_index::Tag)?;
        }
        #[cfg(feature = "recording_avec_len")] {
            finish_file_chunked("avec_len.cbor", recording::avec_len::Tag)?;
        }
        #[cfg(feature = "recording_amap_keys")] {
            finish_file_chunked("amap_keys.cbor", recording::amap_keys::Tag)?;
        }
        #[cfg(feature = "recording_amap_access")] {
            finish_file("amap_access.cbor", recording::amap_access::Tag)?;
        }
        #[cfg(feature = "recording_linear")] {
            finish_file("linear.cbor", recording::linear::Tag)?;
        }

        Ok(())
    }
}

#[cfg(not(feature = "microram_api"))] pub use self::load_finish::{load, finish};


#[cfg(not(feature = "microram_api"))]
pub fn rollback_on_panic<F: FnOnce() -> R + UnwindSafe, R>(f: F) -> R {
    macro_rules! rollback_on_panic_body {
        ($f:expr; $($stream:ident),*) => {{
            $( let $stream = recording::$stream::Tag.with(|rs| rs.snapshot()); )*
            let r = panic::catch_unwind($f);
            match r {
                Ok(x) => x,
                Err(e) => {
                    $( recording::$stream::Tag.with(|rs| rs.rewind($stream)); )*
                    panic::resume_unwind(e);
                },
            }
        }};
    }

    rollback_on_panic_body!(
        f;
        rules, props, states, terms, term_index, term_intern_index, search_index, avec_len,
        amap_keys, amap_access, linear
    )
}
