

mod imp_btree {
    use std::borrow::Borrow;
    use std::collections::{BTreeMap, BTreeSet};
    use std::fmt;
    use std::iter::FromIterator;
    use crate::advice::{
        self, Record, Playback, RecordingStreamTag, ChunkedRecordingStreamTag, PlaybackStreamTag,
    };

    pub struct AMap<K: Record, V> {
        m: BTreeMap<K, V>,
        #[cfg(feature = "recording_amap_keys")]
        rec: Recording<K>,
    }

    struct Recording<K: Record> {
        keys: BTreeSet<K>,
        rs: advice::recording::amap_keys::ChunkTag,
    }

    impl<K: Record> Recording<K> {
        fn new() -> Recording<K> {
            let rs = advice::recording::amap_keys::Tag.add_chunk();
            Recording {
                keys: BTreeSet::new(),
                rs,
            }
        }
    }

    impl<K: Record> Drop for Recording<K> {
        fn drop(&mut self) {
            self.rs.record(&self.keys.len());
            for k in self.keys.iter() {
                self.rs.record(k);
            }
        }
    }


    impl<K: Ord + Record, V> AMap<K, V> {
        pub fn new() -> AMap<K, V> {
            AMap {
                m: BTreeMap::new(),
                #[cfg(feature = "recording_amap_keys")]
                rec: Recording::new(),
            }
        }
    }

    impl<K: Ord + Record + Clone, V> AMap<K, V> {
        pub fn insert(&mut self, k: K, v: V) -> Option<V> {
            #[cfg(feature = "recording_amap_keys")] {
                self.rec.keys.insert(k.clone());
            }
            self.m.insert(k, v)
        }
    }

    impl<K: Ord + Record, V> AMap<K, V> {
        pub fn remove<Q>(&mut self, k: &Q) -> Option<V>
        where K: Borrow<Q>, Q: Ord + ?Sized {
            self.m.remove(k)
        }

        pub fn get<Q>(&self, k: &Q) -> Option<&V>
        where K: Borrow<Q>, Q: Ord + ?Sized {
            self.m.get(k)
        }

        pub fn get_mut<Q>(&mut self, k: &Q) -> Option<&mut V>
        where K: Borrow<Q>, Q: Ord + ?Sized {
            self.m.get_mut(k)
        }
    }

    impl<K: Record, V> AMap<K, V> {
        pub fn len(&self) -> usize {
            self.m.len()
        }

        pub fn iter<'a>(&'a self) -> impl Iterator<Item = (&'a K, &'a V)> + 'a {
            self.m.iter()
        }

        pub fn iter_mut<'a>(&'a mut self) -> impl Iterator<Item = (&'a K, &'a mut V)> + 'a {
            self.m.iter_mut()
        }

        pub fn values<'a>(&'a self) -> impl Iterator<Item = &'a V> + 'a {
            self.m.values()
        }
    }

    impl<K: PartialEq + Record, V: PartialEq> PartialEq for AMap<K, V> {
        fn eq(&self, other: &AMap<K, V>) -> bool {
            self.m == other.m
        }
    }

    impl<K: Eq + Record, V: Eq> Eq for AMap<K, V> {}

    impl<K: Ord + Record + Clone, V: Clone> Clone for AMap<K, V> {
        fn clone(&self) -> Self {
            self.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
        }
    }

    impl<K: Ord + Record + Clone, V: Clone> FromIterator<(K, V)> for AMap<K, V> {
        fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
            let mut m = AMap::new();
            for (k, v) in iter.into_iter() {
                m.insert(k, v);
            }
            m
        }
    }

    impl<K: fmt::Debug + Record, V: fmt::Debug> fmt::Debug for AMap<K, V> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            fmt::Debug::fmt(&self.m, f)
        }
    }
}

mod imp_box {
    use std::borrow::Borrow;
    use std::fmt;
    use std::iter::FromIterator;
    use crate::advice::{self, Record, Playback, RecordingStreamTag, PlaybackStreamTag};

    pub struct AMap<K, V> {
        /// Storage for key-value pairs.  This contains an entry for every key that will be
        /// inserted over the lifetime of this map (as predicted by the `amap_keys` advice stream).
        /// Only entries where the value part is `Some` represent key-value pairs currently present
        /// in the map.
        ///
        /// This list is sorted, so it's possible to prove with advice that a particular key is not
        /// present in the map by showing that it falls strictly between two adjacent entries.
        data: Box<[(K, Option<V>)]>,
        len: usize,
    }

    impl<K: Ord + Playback, V> AMap<K, V> {
        pub fn new() -> AMap<K, V> {
            let ps = advice::playback::amap_keys::Tag;
            let len = ps.playback::<usize>();
            let mut data = Vec::<(K, Option<V>)>::with_capacity(len);
            for i in 0 .. len {
                let k = ps.playback::<K>();
                if i > 0 {
                    // The key set given as advice must be sorted in strictly ascending order.
                    // This ensures that it contains no duplicates.
                    require!(k > data.last().unwrap().0)
                }
                data.push((k, None));
            }
            AMap {
                data: data.into_boxed_slice(),
                len: 0,
            }
        }
    }

    impl<K: Ord, V> AMap<K, V> {
        /// Get the index in `self.data` where the key is `k`.  Returns `None` if `k` is not
        /// present in this map's set of allowed keys.
        fn get_index<Q>(&self, k: &Q) -> Option<usize>
        where K: Borrow<Q>, Q: Ord + ?Sized {
            #[cfg(not(feature = "playback_amap_access"))] {
                match self.data.binary_search_by(|&(ref k2, _)| k2.borrow().cmp(k)) {
                    Ok(i) => {
                        #[cfg(feature = "recording_amap_access")] {
                            advice::recording::amap_access::Tag.record(&i);
                        }
                        return Some(i);
                    },
                    Err(i) => {
                        // `i` is "the index where a matching element could be inserted while
                        // maintaining sorted order".
                        #[cfg(feature = "recording_amap_access")] {
                            advice::recording::amap_access::Tag.record(&i);
                        }
                        return None;
                    },
                }
            }

            #[cfg(feature = "playback_amap_access")] {
                let i = advice::playback::amap_access::Tag.playback::<usize>();
                if self.data[i].0.borrow() == k {
                    return Some(i);
                }

                // Otherwise, the key is not present in the key set.  We prove that it's absent by
                // showing that it falls between two adjacent keys, or between a key and the
                // start/end of the list.

                // Check the lesser element.
                if i > 0 {
                    require!(self.data[i - 1].0.borrow() < k);
                }
                // If `i == 0`, then `k` is less than the first element in the list.

                // Check the greater element.
                if i < self.data.len() {
                    require!(k < self.data[i].0.borrow());
                }
                // If `i == self.data.len()`, then `k` is greater than the last element in the
                // list.

                return None;
            }

            unreachable!();
        }

        pub fn insert(&mut self, k: K, v: V) -> Option<V> {
            // This should always succeed, since the `amap_keys` advice provides the full set of
            // keys that will be inserted into the set.
            let i = self.get_index(&k)
                .unwrap_or_else(|| die!("bad advice: inserted key not present in AMap key set"));
            let old = self.data[i].1.replace(v);
            if old.is_none() {
                self.len += 1;
            }
            old
        }

        pub fn remove<Q>(&mut self, k: &Q) -> Option<V>
        where K: Borrow<Q>, Q: Ord + ?Sized {
            // If this returns `None`, no entry with this key was ever observed when recording
            // advice.
            let i = self.get_index(k)?;
            let old = self.data[i].1.take();
            if old.is_some() {
                self.len -= 1;
            }
            old
        }

        pub fn get<Q>(&self, k: &Q) -> Option<&V>
        where K: Borrow<Q>, Q: Ord + ?Sized {
            let i = self.get_index(k)?;
            self.data[i].1.as_ref()
        }

        pub fn get_mut<Q>(&mut self, k: &Q) -> Option<&mut V>
        where K: Borrow<Q>, Q: Ord + ?Sized {
            let i = self.get_index(k)?;
            self.data[i].1.as_mut()
        }
    }

    impl<K, V> AMap<K, V> {
        pub fn len(&self) -> usize {
            self.len
        }

        pub fn iter<'a>(&'a self) -> impl Iterator<Item = (&'a K, &'a V)> + 'a {
            self.data.iter().filter_map(|&(ref k, ref opt_v)| {
                Some((k, opt_v.as_ref()?))
            })
        }

        pub fn iter_mut<'a>(&'a mut self) -> impl Iterator<Item = (&'a K, &'a mut V)> + 'a {
            self.data.iter_mut().filter_map(|&mut (ref k, ref mut opt_v)| {
                Some((k, opt_v.as_mut()?))
            })
        }

        pub fn values<'a>(&'a self) -> impl Iterator<Item = &'a V> + 'a {
            self.iter().map(|(_k, v)| v)
        }
    }

    impl<K: PartialEq, V: PartialEq> PartialEq for AMap<K, V> {
        fn eq(&self, other: &AMap<K, V>) -> bool {
            let ps = advice::playback::amap_access::Tag;
            // We get the answer as advice, then check to make sure it's accurate.
            let eq = ps.playback::<bool>();
            if eq {
                require!(self.iter().eq(other.iter()),
                    "bad advice: AMaps are not equal");
            } else {
                let e1 = ps.take_elem(&self.data);
                let e2 = ps.take_elem(&other.data);
                require!(e1 != e2, "bad advice: provided AMap indices don't differ");
            }
            eq
        }
    }

    impl<K: Eq, V: Eq> Eq for AMap<K, V> {}

    impl<K: Ord + Playback + Clone, V: Clone> Clone for AMap<K, V> {
        fn clone(&self) -> Self {
            self.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
        }
    }

    impl<K: Ord + Playback + Clone, V: Clone> FromIterator<(K, V)> for AMap<K, V> {
        fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
            let mut m = AMap::new();
            for (k, v) in iter.into_iter() {
                m.insert(k, v);
            }
            m
        }
    }

    impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for AMap<K, V> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            f.debug_map().entries(self.iter()).finish()
        }
    }
}

#[cfg(not(feature = "playback_amap_keys"))]
pub use self::imp_btree::AMap;
#[cfg(feature = "playback_amap_keys")]
pub use self::imp_box::AMap;
