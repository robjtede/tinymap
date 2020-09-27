// MIT/Apache2 License

use super::Node;
use core::slice;
use tinyvec::ArrayVecIterator;

/// A non-consuming iterator for instances of `ArrayMap`.
#[repr(transparent)]
pub struct Iter<'a, K, V> {
    inner: slice::Iter<'a, Option<Node<K, V>>>,
}

impl<'a, K, V> Iter<'a, K, V> {
    #[inline]
    pub(crate) fn new(inner: slice::Iter<'a, Option<Node<K, V>>>) -> Self {
        Self { inner }
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        self.inner.find_map(|node| match node.as_ref() {
            None => None,
            Some(Node {
                kv: (ref k, ref v), ..
            }) => Some((k, v)),
        })
    }
}

/// A non-consuming iterator for instances of `ArrayMap` that returns mutable references.
#[repr(transparent)]
pub struct IterMut<'a, K, V> {
    inner: slice::IterMut<'a, Option<Node<K, V>>>,
}

impl<'a, K, V> IterMut<'a, K, V> {
    #[inline]
    pub(crate) fn new(inner: slice::IterMut<'a, Option<Node<K, V>>>) -> Self {
        Self { inner }
    }
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        self.inner.find_map(|node| match node.as_mut() {
            None => None,
            Some(Node {
                kv: (ref k, ref mut v),
                ..
            }) => Some((k, v)),
        })
    }
}

/// A consuming iterator for instances of `ArrayMap`.
#[repr(transparent)]
pub struct IntoIter<K, V, const N: usize> {
    inner: ArrayVecIterator<[Option<Node<K, V>>; N]>,
}

impl<K, V, const N: usize> IntoIter<K, V, N> {
    #[inline]
    pub(crate) fn new(inner: ArrayVecIterator<[Option<Node<K, V>>; N]>) -> Self {
        Self { inner }
    }
}

impl<K, V, const N: usize> Iterator for IntoIter<K, V, N> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.find_map(|node| match node {
            None => None,
            Some(node) => Some(node.kv),
        })
    }

    #[inline]
    #[must_use]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.inner.size_hint().1)
    }
}

#[test]
fn test_remove() {
    use super::ArrayMap;

    let mut map: ArrayMap<u32, u32, 25> = ArrayMap::new();
    for i in 0..25 {
        map.insert(i, i);
    }

    for j in 10..15 {
        map.remove(&j);
    }

    let _test = map.get(&16).unwrap();
}

/// A drain from an `ArrayMap`.
pub struct Drain<'a, K: PartialOrd, V> {
    inner: slice::IterMut<'a, Option<Node<K, V>>>,
}

impl<'a, K: PartialOrd, V> Drain<'a, K, V> {
    #[inline]
    pub(crate) fn new(inner: slice::IterMut<'a, Option<Node<K, V>>>) -> Self {
        Self { inner }
    }
}

impl<'a, K: PartialOrd, V> Iterator for Drain<'a, K, V> {
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<(K, V)> {
        self.inner.find_map(|m| m.take().map(|r| r.kv))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl<'a, K: PartialOrd, V> DoubleEndedIterator for Drain<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<(K, V)> {
        self.inner
            .rfind(|o| Option::is_some(o))
            .map(|r| r.take().unwrap().kv)
    }
}

/// An iterator over the keys of an `ArrayMap`.
#[repr(transparent)]
pub struct Keys<'a, K, V> {
    inner: Iter<'a, K, V>,
}

impl<'a, K, V> Keys<'a, K, V> {
    #[inline]
    pub(crate) fn new(inner: Iter<'a, K, V>) -> Self {
        Self { inner }
    }
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    #[inline]
    fn next(&mut self) -> Option<&'a K> {
        match self.inner.next() {
            Some((k, _v)) => Some(k),
            None => None,
        }
    }
}

/// An iterator over the values of an `ArrayMap`.
#[repr(transparent)]
pub struct Values<'a, K, V> {
    inner: Iter<'a, K, V>,
}

impl<'a, K, V> Values<'a, K, V> {
    #[inline]
    pub(crate) fn new(inner: Iter<'a, K, V>) -> Self {
        Self { inner }
    }
}

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    #[inline]
    fn next(&mut self) -> Option<&'a V> {
        match self.inner.next() {
            Some((_k, v)) => Some(v),
            None => None,
        }
    }
}

/// A mutable iterator over the values of an `ArrayMap`.
#[repr(transparent)]
pub struct ValuesMut<'a, K, V> {
    inner: IterMut<'a, K, V>,
}

impl<'a, K, V> ValuesMut<'a, K, V> {
    #[inline]
    pub(crate) fn new(inner: IterMut<'a, K, V>) -> Self {
        Self { inner }
    }
}

impl<'a, K, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    #[inline]
    fn next(&mut self) -> Option<&'a mut V> {
        match self.inner.next() {
            Some((_k, v)) => Some(v),
            None => None,
        }
    }
}
