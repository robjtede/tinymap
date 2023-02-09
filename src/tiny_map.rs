//! Provides a map-like structure that can spill over into the heap if it overflows the stack. See
//! documentation for [`TinyMap`] for more information.

use core::{
    hash::Hash,
    iter::{Extend, FromIterator},
};

use hashbrown::hash_map::{
    HashMap, IntoIter as HashMapIntoIter, Iter as HashMapIter, IterMut as HashMapIterMut,
    Keys as HashMapKeys, Values as HashMapValues, ValuesMut as HashMapValuesMut,
};

use crate::array_map::{
    ArrayMap, IntoIter as ArrayMapIntoIter, Iter as ArrayMapIter, IterMut as ArrayMapIterMut,
    Keys as ArrayMapKeys, Values as ArrayMapValues, ValuesMut as ArrayMapValuesMut,
};

/// A map structure that will normally store its data on the stack unless it overflows to the heap.
///
/// This object is an enum containing either an [`ArrayMap`](crate::array_map::ArrayMap) or a
/// [`hashbrown::HashMap`](https://docs.rs/hashbrown). If the `ArrayMap` is completely full, it will
/// spill its elements into a `HashMap` contained on the heap.
///
/// # WARNING
///
/// `ArrayMap` currently uses a relatively slow implementation involving a binary tree setup. I plan
/// to port it over to a hash map-like implementation sometime in the next millennium. This
/// structure may not be worth it to use.
///
/// # Examples
///
/// ```
/// use tinymap::TinyMap;
///
/// // the crab hospital needs a database to keep track of the crabs
///
/// /// Represents a patient.
/// struct Patient {
///     shell_toughness: u32,
///     ailment: &'static str,
/// }
///
/// let map: TinyMap<&'static str, Patient, 3> = TinyMap::new();
/// ```
#[derive(Clone, Debug)]
pub enum TinyMap<K: PartialOrd + Eq + Hash, V, const N: usize> {
    Stack(ArrayMap<K, V, N>),
    Heap(HashMap<K, V>),
}

impl<K: PartialOrd + Eq + Hash, V, const N: usize> TinyMap<K, V, N> {
    /// Create a new, empty `TinyMap`.
    #[inline]
    pub fn new() -> Self {
        Self::Stack(ArrayMap::new())
    }

    /// Create an empty `TinyMap` with the specified capacity. If the capacity is greater than `N`, it will
    /// allocate on the heap immediately.
    #[inline]
    pub fn with_capacity(cap: usize) -> Self {
        if cap > N {
            Self::Heap(HashMap::with_capacity(cap))
        } else {
            Self::new()
        }
    }

    /// Get the length of the map.
    #[inline]
    pub fn len(&self) -> usize {
        match self {
            Self::Stack(s) => s.len(),
            Self::Heap(h) => h.len(),
        }
    }

    /// Tell whether the map is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        match self {
            Self::Stack(s) => s.is_empty(),
            Self::Heap(h) => h.is_empty(),
        }
    }

    /// Get an element from this map.
    #[inline]
    pub fn get(&self, key: &K) -> Option<&V> {
        match self {
            Self::Stack(s) => s.get(key),
            Self::Heap(h) => h.get(key),
        }
    }

    /// Get a mutable reference to an element from this map.
    #[inline]
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        match self {
            Self::Stack(s) => s.get_mut(key),
            Self::Heap(h) => h.get_mut(key),
        }
    }

    /// Insert an element into this map.
    #[inline]
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Ord,
    {
        match self {
            Self::Heap(h) => h.insert(key, value),
            Self::Stack(s) => match s.try_insert(key, value) {
                Ok(v) => v,
                Err((key, value)) => {
                    self.spill();
                    self.as_heap_mut().insert(key, value)
                }
            },
        }
    }

    /// Remove an entry from the map by its key.
    #[inline]
    pub fn remove_entry(&mut self, key: &K) -> Option<(K, V)>
    where
        K: Ord,
    {
        match self {
            Self::Heap(h) => h.remove_entry(key),
            Self::Stack(s) => s.remove_entry(key),
        }
    }

    /// Remove an item from the map by its key.
    #[inline]
    pub fn remove(&mut self, key: &K) -> Option<V>
    where
        K: Ord,
    {
        self.remove_entry(key).map(|(_k, v)| v)
    }

    /// Clear all entries from the map.
    #[inline]
    pub fn clear(&mut self) {
        match self {
            Self::Heap(h) => h.clear(),
            Self::Stack(s) => s.clear(),
        }
    }

    /// Create an iterator over this map.
    #[inline]
    pub fn iter(&self) -> Iter<'_, K, V> {
        match self {
            Self::Heap(h) => Iter::Heap(h.iter()),
            Self::Stack(s) => Iter::Stack(s.iter()),
        }
    }

    /// Create a mutable iterator over this map.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        match self {
            Self::Heap(h) => IterMut::Heap(h.iter_mut()),
            Self::Stack(s) => IterMut::Stack(s.iter_mut()),
        }
    }

    /// Create an iterator over this map's keys.
    #[inline]
    pub fn keys(&self) -> Keys<'_, K, V> {
        match self {
            Self::Heap(h) => Keys::Heap(h.keys()),
            Self::Stack(s) => Keys::Stack(s.keys()),
        }
    }

    /// Create an iterator over this map's values.
    #[inline]
    pub fn values(&self) -> Values<'_, K, V> {
        match self {
            Self::Heap(h) => Values::Heap(h.values()),
            Self::Stack(s) => Values::Stack(s.values()),
        }
    }

    /// Create a mutable iterator over this map's values.
    #[inline]
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        match self {
            Self::Heap(h) => ValuesMut::Heap(h.values_mut()),
            Self::Stack(s) => ValuesMut::Stack(s.values_mut()),
        }
    }

    #[inline]
    fn spill(&mut self) {
        let s = match self {
            Self::Stack(s) => s,
            Self::Heap(_) => return,
        };

        let heap: HashMap<K, V> = s.drain().collect();
        *self = Self::Heap(heap);
    }

    #[inline]
    fn as_heap_mut(&mut self) -> &mut HashMap<K, V> {
        match self {
            Self::Stack(_) => unreachable!(),
            Self::Heap(h) => h,
        }
    }
}

impl<K: PartialOrd + Eq + Hash, V, const N: usize> IntoIterator for TinyMap<K, V, N> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V, N>;

    #[inline]
    fn into_iter(self) -> IntoIter<K, V, N> {
        match self {
            Self::Heap(h) => IntoIter::Heap(h.into_iter()),
            Self::Stack(s) => IntoIter::Stack(s.into_iter()),
        }
    }
}

impl<K: Ord + Eq + Hash, V, const N: usize> Extend<(K, V)> for TinyMap<K, V, N> {
    #[inline]
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        iter.into_iter().for_each(|(key, value)| {
            self.insert(key, value);
        });
    }
}

impl<K: Ord + Eq + Hash, V, const N: usize> FromIterator<(K, V)> for TinyMap<K, V, N> {
    #[inline]
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let mut tm = TinyMap::with_capacity(iter.size_hint().0);
        tm.extend(iter);
        tm
    }
}

/// An iterator for instances of `TinyMap`.
pub enum Iter<'a, K, V> {
    Stack(ArrayMapIter<'a, K, V>),
    Heap(HashMapIter<'a, K, V>),
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Stack(s) => s.next(),
            Self::Heap(h) => h.next(),
        }
    }
}

/// A mutable iterator for instances of `TinyMap`.
pub enum IterMut<'a, K, V> {
    Stack(ArrayMapIterMut<'a, K, V>),
    Heap(HashMapIterMut<'a, K, V>),
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Stack(s) => s.next(),
            Self::Heap(h) => h.next(),
        }
    }
}

/// A consuming iterator for instances of `TinyMap`.
pub enum IntoIter<K, V, const N: usize> {
    Stack(ArrayMapIntoIter<K, V, N>),
    Heap(HashMapIntoIter<K, V>),
}

impl<K, V, const N: usize> Iterator for IntoIter<K, V, N> {
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<(K, V)> {
        match self {
            Self::Stack(s) => s.next(),
            Self::Heap(h) => h.next(),
        }
    }
}

/// An iterator over the keys of a `TinyMap`.
pub enum Keys<'a, K, V> {
    Stack(ArrayMapKeys<'a, K, V>),
    Heap(HashMapKeys<'a, K, V>),
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    #[inline]
    fn next(&mut self) -> Option<&'a K> {
        match self {
            Self::Stack(s) => s.next(),
            Self::Heap(h) => h.next(),
        }
    }
}

/// An iterator over the values of a `TinyMap`.
pub enum Values<'a, K, V> {
    Stack(ArrayMapValues<'a, K, V>),
    Heap(HashMapValues<'a, K, V>),
}

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    #[inline]
    fn next(&mut self) -> Option<&'a V> {
        match self {
            Self::Stack(s) => s.next(),
            Self::Heap(h) => h.next(),
        }
    }
}

/// A mutable iterator over the values of a `TinyMap`.
pub enum ValuesMut<'a, K, V> {
    Stack(ArrayMapValuesMut<'a, K, V>),
    Heap(HashMapValuesMut<'a, K, V>),
}

impl<'a, K, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    #[inline]
    fn next(&mut self) -> Option<&'a mut V> {
        match self {
            Self::Stack(s) => s.next(),
            Self::Heap(h) => h.next(),
        }
    }
}
