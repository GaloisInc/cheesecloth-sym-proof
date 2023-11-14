use std::array;
use std::convert::{TryFrom, TryInto};
use std::collections::HashSet;
use std::io::{Read, Write};
use std::mem;
use serde_cbor;
use crate::{Word, BinOp};
use crate::logic::{Term, TermKind, VarId, VarCounter, Binder, Prop, ReachableProp, StatePred};
use crate::micro_ram::MemWidth;
use crate::symbolic::{self, MemState, MemConcrete, MemMap, MemSnapshot, MemLog, MemMulti};


pub type Value = u64;


pub struct RecordingStream {
    buf: Vec<Value>,
    /// Slots in `buf` that are reserved and currently contain a placeholder value.  These must be
    /// replaced with real values (via `resolve_deferred()`) before the recording stream is
    /// finished.
    deferred: HashSet<usize>,
}

#[derive(Debug)]
pub struct DeferredIndex(usize);

impl RecordingStream {
    pub fn new() -> RecordingStream {
        RecordingStream {
            buf: Vec::new(),
            deferred: HashSet::new(),
        }
    }

    pub fn put(&mut self, v: Value) {
        self.buf.push(v);
    }

    /// Reserve the next slot in the advice stream, but defer providing a value until later.  The
    /// returned `DeferredIndex` must be passed to `resolve_deferred` before the stream is
    /// finished.
    pub fn defer(&mut self) -> DeferredIndex {
        let i = self.buf.len();
        self.buf.push(0xbaddef);
        self.deferred.insert(i);
        DeferredIndex(i)
    }

    pub fn resolve_deferred(&mut self, idx: DeferredIndex, v: Value) {
        assert!(self.deferred.remove(&idx.0), "slot {:?} already contains a value", idx);
        self.buf[idx.0] = v;
    }

    pub fn finish(self, w: impl Write) -> serde_cbor::Result<()> {
        assert!(self.deferred.len() == 0,
            "must resolve all deferred values before calling finish(): {:?}", self.deferred);
        serde_cbor::to_writer(w, &self.buf)
    }
}

pub trait RecordingStreamTag: Sized + Copy {
    fn with<R>(self, f: impl FnOnce(&mut RecordingStream) -> R) -> R;

    fn put(self, v: Value) {
        self.with(|rs| rs.put(v))
    }

    fn put_cast<T: TryInto<Value>>(self, v: T) {
        self.put(v.try_into().ok().unwrap());
    }

    fn defer(self) -> DeferredIndex {
        self.with(|rs| rs.defer())
    }

    fn resolve_deferred(self, idx: DeferredIndex, v: Value) {
        self.with(|rs| rs.resolve_deferred(idx, v))
    }

    fn finish(self, w: impl Write) -> serde_cbor::Result<()> {
        self.with(|rs| mem::replace(rs, RecordingStream::new()).finish(w))
    }

    fn record<T: Record>(self, x: &T) {
        x.record_into(self);
    }
}

macro_rules! recording_stream {
    ($name:ident) => {
        pub mod $name {
            use std::cell::RefCell;
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


pub struct PlaybackStream {
    buf: Vec<Value>,
    pos: usize,
    inited: bool,
}

impl PlaybackStream {
    pub fn new() -> PlaybackStream {
        PlaybackStream {
            buf: Vec::new(),
            pos: 0,
            inited: false,
        }
    }

    pub fn load(&mut self, r: impl Read) -> serde_cbor::Result<()> {
        assert!(!self.inited, "stream has already been initialized");
        let buf = serde_cbor::from_reader(r)?;
        self.buf = buf;
        self.pos = 0;
        self.inited = true;
        Ok(())
    }

    pub fn take(&mut self) -> Value {
        assert!(self.inited, "tried to read from uninitialized stream");
        assert!(self.pos < self.buf.len(), "tried to read past end of stream");
        let v = self.buf[self.pos];
        self.pos += 1;
        v
    }

    pub fn take_bounded(&mut self, max: Value) -> Value {
        let v = self.take();
        assert!(v <= max);
        v
    }
}

pub trait PlaybackStreamTag: Sized + Copy {
    fn with<R>(self, f: impl FnOnce(&mut PlaybackStream) -> R) -> R;

    fn load(self, r: impl Read) -> serde_cbor::Result<()> {
        self.with(|ps| ps.load(r))
    }

    fn take(self) -> Value {
        self.with(|ps| ps.take())
    }

    fn take_bounded(self, max: Value) -> Value {
        self.with(|ps| ps.take_bounded(max))
    }

    fn take_cast<T: TryFrom<Value>>(self) -> T {
        self.take().try_into().ok().unwrap()
    }

    fn take_bounded_cast<T: TryFrom<Value>>(self, max: Value) -> T {
        self.take_bounded(max).try_into().ok().unwrap()
    }

    fn playback<T: Playback>(self) -> T {
        T::playback_from(self)
    }
}

macro_rules! playback_stream {
    ($name:ident) => {
        pub mod $name {
            use std::cell::RefCell;
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


pub trait Record {
    fn record_into(&self, rs: impl RecordingStreamTag);
}

pub trait Playback {
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
                ps.take_cast()
            }
        }
    };
}

impl_record_playback_for_primitive!(u8);
impl_record_playback_for_primitive!(u16);
impl_record_playback_for_primitive!(u32);
impl_record_playback_for_primitive!(u64);
impl_record_playback_for_primitive!(usize);


impl<T: Record> Record for &'_ T {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        T::record_into(self, rs);
    }
}

impl<T: Record> Record for Box<T> {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        T::record_into(self, rs);
    }
}

impl<T: Playback> Playback for Box<T> {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        Box::new(T::playback_from(ps))
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

impl<T: Record> Record for Box<[T]> {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        <[T]>::record_into(self, rs);
    }
}

impl<T: Playback> Playback for Box<[T]> {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        <Vec<T>>::playback_from(ps).into_boxed_slice()
    }
}

impl<T: Record> Record for Vec<T> {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        <[T]>::record_into(self, rs);
    }
}

impl<T: Playback> Playback for Vec<T> {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        let len = ps.playback::<usize>();
        let mut v = Vec::with_capacity(len);
        for _ in 0 .. len {
            v.push(T::playback_from(ps));
        }
        v
    }
}


impl<T: Record, const N: usize> Record for [T; N] {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        <[T]>::record_into(self, rs);
    }
}

impl<T: Playback, const N: usize> Playback for [T; N] {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        array::from_fn(|_| ps.playback())
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
                $( $A::record_into($A, rs); )*
            }
        }

        impl<$($A: Playback,)*> Playback for ($($A,)*) {
            // `rs` is unused in the zero-element case
            #[allow(unused)]
            fn playback_from(ps: impl PlaybackStreamTag) -> Self {
                #![allow(bad_style)]
                $( let $A = $A::playback_from(ps); )*
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
        T::record_into(&self.inner, rs);
    }
}

impl<T: Playback> Playback for Binder<T> {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        let vars = ps.playback::<VarCounter>();
        let inner = T::playback_from(ps);
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
        let rs = recording::terms::Tag;
        match *self.kind() {
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
    }
}

impl Playback for Term {
    fn playback_from(_ps: impl PlaybackStreamTag) -> Self {
        let ps = playback::terms::Tag;
        match ps.take_bounded(4) {
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
        let symbolic::State { pc, ref regs, ref mem } = *self;
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
        symbolic::State { pc, regs, mem }
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
        let _ = rs;
        todo!()
    }
}

impl Playback for MemMap {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        let _ = ps;
        todo!()
    }
}

impl Record for MemSnapshot {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        let _ = rs;
        todo!()
    }
}

impl Playback for MemSnapshot {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        let _ = ps;
        todo!()
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
    recording_stream!(terms);
    recording_stream!(states);
    recording_stream!(props);
}

pub mod playback {
    playback_stream!(terms);
    playback_stream!(states);
    playback_stream!(props);
}
