use std::fmt;
use std::slice;
use crate::advice::{Record, Playback, RecordingStreamTag, PlaybackStreamTag};

mod imp_vec {
    use std::iter::FromIterator;
    use std::ops::{Deref, DerefMut};
    use crate::advice::{self, ChunkedRecordingStreamTag, RecordingStreamTag};

    pub struct AVec<T> {
        v: Vec<T>,
        #[cfg(feature = "recording_avec_len")]
        rec: Recording,
    }

    struct Recording {
        max_len: usize,
        rs: advice::recording::avec_len::ChunkTag,
    }

    impl Recording {
        fn new(init_len: usize) -> Recording {
            let rs = advice::recording::avec_len::Tag.add_chunk();
            Recording {
                max_len: init_len,
                rs,
            }
        }
    }

    impl Drop for Recording {
        fn drop(&mut self) {
            self.rs.record(&self.max_len);
        }
    }


    impl<T> AVec<T> {
        pub fn new() -> AVec<T> {
            Self::from_vec(Vec::new())
        }

        pub fn with_capacity(n: usize) -> AVec<T> {
            Self::from_vec(Vec::with_capacity(n))
        }

        fn from_vec(v: Vec<T>) -> AVec<T> {
            AVec {
                #[cfg(feature = "recording_avec_len")]
                rec: Recording::new(v.len()),
                v,
            }
        }

        pub fn push(&mut self, x: T) {
            self.v.push(x);
            #[cfg(feature = "recording_avec_len")] {
                if self.v.len() > self.rec.max_len {
                    self.rec.max_len = self.v.len();
                }
            }
        }

        pub fn pop(&mut self) -> Option<T> {
            self.v.pop()
        }
    }

    impl<T> Default for AVec<T> {
        fn default() -> AVec<T> {
            Self::new()
        }
    }

    impl<T> Deref for AVec<T> {
        type Target = [T];
        fn deref(&self) -> &[T] {
            &*self.v
        }
    }

    impl<T> DerefMut for AVec<T> {
        fn deref_mut(&mut self) -> &mut [T] {
            &mut *self.v
        }
    }

    impl<T> FromIterator<T> for AVec<T> {
        fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
            Self::from_vec(Vec::from_iter(iter))
        }
    }

    impl<T> From<Box<[T]>> for AVec<T> {
        fn from(x: Box<[T]>) -> AVec<T> {
            Self::from_vec(x.into())
        }
    }

    impl<T> From<Vec<T>> for AVec<T> {
        fn from(x: Vec<T>) -> AVec<T> {
            Self::from_vec(x)
        }
    }

    impl<T> From<AVec<T>> for Box<[T]> {
        fn from(x: AVec<T>) -> Box<[T]> {
            x.v.into()
        }
    }
}

mod imp_box {
    use std::iter::{self, FromIterator};
    use std::mem::{self, MaybeUninit};
    use std::ptr;
    use std::slice;
    use std::ops::{Deref, DerefMut};
    use crate::advice::{self, PlaybackStreamTag};
    use crate::advice::ChunkedRecordingStreamTag;

    pub struct AVec<T> {
        v: Box<[MaybeUninit<T>]>,
        len: usize,
    }

    impl<T> AVec<T> {
        pub fn new() -> AVec<T> {
            let cap = advice::playback::avec_len::Tag.playback::<usize>();
            AVec {
                v: iter::repeat_with(MaybeUninit::uninit).take(cap).collect(),
                len: 0,
            }
        }

        pub fn with_capacity(n: usize) -> AVec<T> {
            Self::new()
        }

        pub fn push(&mut self, x: T) {
            unsafe {
                let i = self.len;
                self.v[i].as_mut_ptr().write(x);
                self.len += 1;
            }
        }

        pub fn pop(&mut self) -> Option<T> {
            unsafe {
                if self.len == 0 {
                    return None;
                }

                self.len -= 1;
                let i = self.len;
                // Note this indexing can't panic, since `self.len` on entry was greater than `i`.
                Some(self.v[i].as_ptr().read())
            }
        }
    }

    impl<T> Default for AVec<T> {
        fn default() -> AVec<T> {
            Self::new()
        }
    }

    impl<T> Deref for AVec<T> {
        type Target = [T];
        fn deref(&self) -> &[T] {
            unsafe {
                slice::from_raw_parts(
                    self.v.as_ptr() as *const T,
                    self.len,
                )
            }
        }
    }

    impl<T> DerefMut for AVec<T> {
        fn deref_mut(&mut self) -> &mut [T] {
            unsafe {
                slice::from_raw_parts_mut(
                    self.v.as_mut_ptr() as *mut T,
                    self.len,
                )
            }
        }
    }

    impl<T> FromIterator<T> for AVec<T> {
        fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
            let mut v = AVec::new();
            for item in iter.into_iter() {
                v.push(item);
            }
            v
        }
    }

    impl<T> From<Box<[T]>> for AVec<T> {
        fn from(x: Box<[T]>) -> AVec<T> {
            Vec::from(x).into()
        }
    }

    impl<T> From<Vec<T>> for AVec<T> {
        fn from(x: Vec<T>) -> AVec<T> {
            let mut v = AVec::new();
            for item in x.into_iter() {
                v.push(item);
            }
            v
        }
    }

    impl<T> From<AVec<T>> for Box<[T]> {
        fn from(mut x: AVec<T>) -> Box<[T]> {
            unsafe {
                if x.len == x.v.len() {
                    let v = mem::take(&mut x.v);
                    mem::transmute::<Box<[MaybeUninit<T>]>, Box<[T]>>(v)
                } else {
                    let n = x.len;
                    let mut b: Box<[MaybeUninit<T>]> =
                        iter::repeat_with(MaybeUninit::uninit).take(n).collect();
                    x.len = 0;
                    ptr::copy_nonoverlapping(x.v.as_ptr(), b.as_mut_ptr(), n);
                    mem::transmute::<Box<[MaybeUninit<T>]>, Box<[T]>>(b)
                }
            }
        }
    }
}

#[cfg(not(feature = "playback_avec_len"))]
pub use self::imp_vec::AVec;
#[cfg(feature = "playback_avec_len")]
pub use self::imp_box::AVec;

impl<T: Clone> Clone for AVec<T> {
    fn clone(&self) -> Self {
        let mut out = AVec::with_capacity(self.len());
        for x in self {
            out.push(x.clone());
        }
        out
    }
}

impl<T: fmt::Debug> fmt::Debug for AVec<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        <[T] as fmt::Debug>::fmt(self, f)
    }
}

impl<T: PartialEq<U>, U> PartialEq<AVec<U>> for AVec<T> {
    fn eq(&self, other: &AVec<U>) -> bool {
        self as &[_] == other as &[_]
    }
}

impl<T: Eq> Eq for AVec<T> {}

impl<'a, T> IntoIterator for &'a AVec<T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut AVec<T> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T: Record> Record for AVec<T> {
    fn record_into(&self, rs: impl RecordingStreamTag) {
        rs.record::<[T]>(self)
    }
}

impl<T: Playback> Playback for AVec<T> {
    fn playback_from(ps: impl PlaybackStreamTag) -> Self {
        let len = ps.playback::<usize>();
        let mut v = AVec::with_capacity(len);
        for _ in 0 .. len {
            v.push(ps.playback::<T>());
        }
        v
    }
}
