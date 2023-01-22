// MIT/Apache2 License

//! A stack-based, fixed-size map that puts nodes on an array rather than the heap. See documentation
//! of [`ArrayMap]` for more information.

mod iterators;
pub use iterators::*;

use core::{cmp::Ordering, fmt, iter, mem};
use tinyvec::ArrayVec;

// A node in the binary tree making up the map.
pub(crate) struct Node<K, V> {
    kv: (K, V),
    children: [Option<usize>; 2],
}

impl<K: Clone, V: Clone> Clone for Node<K, V> {
    #[inline]
    fn clone(&self) -> Self {
        Node {
            kv: self.kv.clone(),
            children: self.children,
        }
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for Node<K, V> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.kv, f)
    }
}

/// A binary tree that uses a stack-based array as storage for nodes.
///
/// Rather than using the heap to store nodes, this structure uses an `ArrayVec`. Note that this
/// is nowhere near as efficient as the standard library `HashMap` implementation. The purpose of
/// this structure is to offer an interface similar to `HashMap` to use in its place in `no_std` environments.
///
/// # Example
///
/// ```rust
/// use tinymap::ArrayMap;
///
/// // Today, I'm making software for the lamp store. They want to match up a LampID to a
/// // Lamp. This software also needs to run on embedded hardware, where a Rust allocator
/// // hasn't been ported yet.
///
/// /// A representation of a lamp.
/// struct Lamp { wattage: u32, color: &'static str }
///
/// // The LampID is just a string that the manager uses to look up a lamp
/// // that the store has in stock.
/// let mut lamps: ArrayMap<&'static str, Lamp, 3> = ArrayMap::new();
///
/// // Let's take some of the lamps we have and put them in our map.
/// lamps.insert("32ZD", Lamp { wattage: 120, color: "red" });
/// lamps.insert("11HR", Lamp { wattage: 60, color: "gray" });
/// lamps.insert("2460", Lamp { wattage: 90, color: "blue" });
///
/// // The customer wants lamps #32ZD and #11HR?
/// assert_eq!(lamps.get(&"32ZD").unwrap().wattage, 120);
/// assert_eq!(lamps.get(&"11HR").unwrap().color, "gray");
///
/// // Let's add one more lamp! Nothing could go wrong!
/// let oops = lamps.try_insert("199K", Lamp { wattage: 80, color: "green" });
/// assert!(oops.is_err());
/// assert!(lamps.get(&"199k").is_none());
/// ```
pub struct ArrayMap<K: PartialOrd, V, const N: usize> {
    arena: ArrayVec<[Option<Node<K, V>>; N]>,
    root: Option<usize>,
}

macro_rules! unwrap_tpn {
    ($self: expr, $e: expr) => {{
        match $self.try_push_node($e) {
            Ok(u) => Some(u),
            Err(n) => {
                let Node { kv, .. } = n;
                return Err(kv);
            }
        }
    }};
}

enum ChildType {
    Left,
    Right,
}

impl<K: PartialOrd, V, const N: usize> ArrayMap<K, V, N> {
    /// Create a new [`ArrayMap`].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use tinymap::ArrayMap;
    /// #[derive(PartialOrd, Ord, PartialEq, Eq)]
    /// struct Foo;
    /// struct Bar;
    ///
    /// let my_map: ArrayMap<Foo, Bar, 1> = ArrayMap::new();
    /// ```
    #[must_use]
    #[inline]
    pub fn new() -> Self {
        Self {
            arena: ArrayVec::new(),
            root: None,
        }
    }

    /// Retrieves the current number of elements within the binary tree.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use tinymap::ArrayMap;
    /// #[derive(PartialOrd, Ord, PartialEq, Eq)]
    /// struct MyIndex(u32);
    /// struct MyData { foo: &'static str }
    ///
    /// let mut my_map: ArrayMap<MyIndex, MyData, 3> = ArrayMap::new();
    /// my_map.insert(MyIndex(12), MyData { foo: "Leroy" });
    /// my_map.insert(MyIndex(13), MyData { foo: "Barbara" });
    /// my_map.insert(MyIndex(12), MyData { foo: "Joanne" });
    /// assert_eq!(my_map.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.arena
            .iter()
            .filter(|n| match n {
                Some(_) => true,
                None => false,
            })
            .count()
    }

    /// Check to see if there are any elements in this map.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use tinymap::ArrayMap;
    /// let my_love_life: ArrayMap<&'static str, u32, 10> = ArrayMap::new();
    /// assert!(my_love_life.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        match self.root {
            Some(_) => false,
            None => true,
        }
    }

    #[must_use]
    #[inline]
    fn node_at(&self, index: usize) -> Option<&Node<K, V>> {
        self.arena[index].as_ref()
    }

    #[must_use]
    #[inline]
    fn node_at_mut(&mut self, index: usize) -> Option<&mut Node<K, V>> {
        self.arena[index].as_mut()
    }

    #[must_use]
    #[inline]
    fn root(&self) -> Option<usize> {
        self.root
    }

    #[must_use]
    #[inline]
    fn node_by_key(&self, key: &K) -> Option<&Node<K, V>> {
        let mut current = self.root();
        loop {
            match current {
                None => return None,
                Some(val) => {
                    let node = self.node_at(val).expect("Invalid node tree");
                    current = match node.kv.0.partial_cmp(key) {
                        None => return None,
                        Some(Ordering::Equal) => return Some(node),
                        Some(Ordering::Less) => node.children[0],
                        Some(Ordering::Greater) => node.children[1],
                    };
                }
            }
        }
    }

    #[must_use]
    #[inline]
    fn node_by_key_mut(&mut self, key: &K) -> Option<&mut Node<K, V>> {
        let mut current = self.root();
        loop {
            match current {
                None => return None,
                Some(val) => {
                    let node = self.node_at(val).expect("Invalid node tree");
                    current = match node.kv.0.partial_cmp(key) {
                        None => return None,
                        Some(Ordering::Equal) => {
                            return Some(self.node_at_mut(val).expect("Invalid node tree"));
                        }
                        Some(Ordering::Less) => node.children[0],
                        Some(Ordering::Greater) => node.children[1],
                    };
                }
            }
        }
    }

    /// Get a reference to an item stored inside of this map.
    #[must_use]
    #[inline]
    pub fn get(&self, key: &K) -> Option<&V> {
        match self.node_by_key(key) {
            Some(node) => Some(&node.kv.1),
            None => None,
        }
    }

    /// Get a mutable reference to an item stored inside of this map.
    #[must_use]
    #[inline]
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        match self.node_by_key_mut(key) {
            Some(node) => Some(&mut node.kv.1),
            None => None,
        }
    }

    /// Tell whether or not this map contains a certain key.
    #[must_use]
    #[inline]
    pub fn contains_key(&self, key: &K) -> bool {
        match self.node_by_key(key) {
            Some(_) => true,
            None => false,
        }
    }

    // push a node into the arena and get its index back
    #[inline]
    fn try_push_node(&mut self, node: Node<K, V>) -> Result<usize, Node<K, V>> {
        match self.arena.try_push(Some(node)) {
            Some(mut node) => {
                // look for a node to replace
                let pos = self.arena.iter().position(Option::is_none);
                match pos {
                    Some(pos) => {
                        mem::swap(&mut self.arena[pos], &mut node);
                        Ok(pos)
                    }
                    None => Err(node.unwrap()),
                }
            }
            None => Ok(self.arena.len() - 1),
        }
    }

    #[inline]
    fn insert_from_root(
        &mut self,
        mut node: Node<K, V>,
        mut current: usize,
    ) -> Result<Option<V>, (K, V)>
    where
        K: Ord,
    {
        let mut next;
        loop {
            let cmp_node = self.node_at(current).unwrap();
            let ct = match cmp_node.kv.0.cmp(&node.kv.0) {
                Ordering::Less => {
                    next = cmp_node.children[0];
                    ChildType::Left
                }
                Ordering::Greater => {
                    next = cmp_node.children[1];
                    ChildType::Right
                }
                Ordering::Equal => {
                    mem::swap(&mut self.node_at_mut(current).unwrap().kv.1, &mut node.kv.1);
                    return Ok(Some(node.kv.1));
                }
            };

            match next {
                None => {
                    let index = unwrap_tpn!(self, node);
                    let cmp_node_mut = self.node_at_mut(current).unwrap();
                    let slot = match ct {
                        ChildType::Left => &mut cmp_node_mut.children[0],
                        ChildType::Right => &mut cmp_node_mut.children[1],
                    };
                    *slot = index;

                    return Ok(None);
                }
                Some(next) => {
                    current = next;
                }
            }
        }
    }

    /// Insert a node into this binary tree. This function will return the value previously
    /// in the key's slot, if applicable.
    ///
    /// # Errors
    ///
    /// If the backing array is full, this function will return back the key-value pair passed
    /// in.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use tinymap::ArrayMap;
    /// /// The representation of a mattress.
    /// #[derive(PartialOrd, Ord, PartialEq, Eq)]
    /// struct Mattress { width: u32, height: u32, brand: &'static str }
    ///
    /// let mut mattress_ratings: ArrayMap<Mattress, u64, 12> = ArrayMap::new();
    /// let mut limit = 0;
    /// loop {
    ///     // The mattress testing robot tests more mattresses than we could ever imagine.
    ///     // But how long until it tests too many?
    ///     let mattress = Mattress {
    ///         width: limit + 1,
    ///         height: (limit + 1) * 2,
    ///         brand: "Smith Mattresses",
    ///     };
    ///     let res = mattress_ratings.try_insert(mattress, 27);
    ///     match res {
    ///         Ok(_) => { limit += 1; },
    ///         Err((reject, _)) => {
    ///             assert_eq!(reject.width, 13);
    ///             break;
    ///         }
    ///     }
    /// }
    ///
    /// assert_eq!(limit, 12);
    /// ```
    #[inline]
    pub fn try_insert(&mut self, key: K, value: V) -> Result<Option<V>, (K, V)>
    where
        K: Ord,
    {
        let node = Node {
            kv: (key, value),
            children: [None; 2],
        };

        match self.root {
            None => {
                // if the root doesn't exist, this is an empty map
                self.root = unwrap_tpn!(self, node);
                Ok(None)
            }
            Some(root) => self.insert_from_root(node, root),
        }
    }

    /// Insert a node into this binary tree.
    ///
    /// # Panics
    ///
    /// Unlike `try_insert`, this function will panic if the backing array is full.
    ///
    /// # Example
    ///
    /// ```rust, should_panic
    /// # use tinymap::ArrayMap;
    /// /// Representation of a viking.
    /// struct Viking { kill_count: u32, body_count: u32, name: &'static str }
    /// let mut famous_vikings: ArrayMap<u32, Viking, 25> = ArrayMap::new();
    ///
    /// for i in 0..100 {
    ///    // D'oh! I knew I shouldn't have run my school assignment on my microwave!
    ///    famous_vikings.insert(i, Viking { kill_count: i, body_count: i * 2, name: "John" });
    /// }
    /// ```
    #[inline]
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Ord,
    {
        match self.try_insert(key, value) {
            Err(_) => panic!("Unable to push node into binary tree"),
            Ok(res) => res,
        }
    }

    /// Remove a node entry from the binary tree. This function returns the key-value pair
    /// that was removed.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use tinymap::ArrayMap;
    /// fn help_humans() { println!("Let's solve world hunger!"); }
    /// fn kill_humans() { panic!("Kill! Kill! Kill!"); }
    ///
    /// // My robot needs to know what to do!
    /// let mut robot_behaviors: ArrayMap<&'static str, &dyn Fn(), 2> = ArrayMap::new();
    /// robot_behaviors.insert("help", &help_humans);
    /// robot_behaviors.insert("kill", &kill_humans);
    ///
    /// // ...wait. It probably shouldn't do that.
    /// let removed = robot_behaviors.remove_entry(&"kill").unwrap();
    ///
    /// assert_eq!(removed.0, "kill");
    /// ```
    #[inline]
    pub fn remove_entry(&mut self, key: &K) -> Option<(K, V)>
    where
        K: Ord,
    {
        const ERR_MSG: &str = "Invalid binary tree path";

        enum ParentChildRelation {
            ChildIsRoot,
            Left,
            Right,
        }

        let mut parent_index: Option<usize> = None;
        let mut last_relationship = ParentChildRelation::ChildIsRoot;
        let mut current: Option<usize> = self.root;
        loop {
            let c = match current {
                Some(c) => c,
                None => return None,
            };
            let cmp_node = self.node_at(c).expect(ERR_MSG);
            match cmp_node.kv.0.partial_cmp(key) {
                None => return None,
                Some(Ordering::Equal) => {
                    // create a node to replace the node in the tree
                    let mut replacement_node = match cmp_node.children {
                        [None, None] => None,
                        [Some(child), None] | [None, Some(child)] => Some(child),
                        [Some(child1), Some(child2)] => {
                            // take the node out of child2
                            let mut reloc_node = None;
                            mem::swap(&mut reloc_node, &mut self.arena[child2]);

                            // insert child2 under child1
                            if let Err(_) = self.insert_from_root(reloc_node.unwrap(), child1) {
                                panic!("This should not happen!");
                            }

                            // use child1 as the replacement node
                            Some(child1)
                        }
                    };

                    let slot = match (last_relationship, parent_index) {
                        (ParentChildRelation::ChildIsRoot, _) => &mut self.root,
                        (ParentChildRelation::Left, Some(p)) => {
                            &mut self.node_at_mut(p).expect(ERR_MSG).children[0]
                        }
                        (ParentChildRelation::Right, Some(p)) => {
                            &mut self.node_at_mut(p).expect(ERR_MSG).children[1]
                        }
                        _ => unreachable!(),
                    };

                    mem::swap(slot, &mut replacement_node);
                    let n = self.arena[replacement_node.unwrap()].take();
                    return Some(n.unwrap().kv);
                }
                Some(Ordering::Less) => {
                    parent_index = current;
                    current = cmp_node.children[0];
                    last_relationship = ParentChildRelation::Left;
                }
                Some(Ordering::Greater) => {
                    parent_index = current;
                    current = cmp_node.children[1];
                    last_relationship = ParentChildRelation::Right;
                }
            }
        }
    }

    /// Remove a value from the binary tree. This is similar to `remove_entry`, but it does not
    /// keep the value.
    #[inline]
    pub fn remove(&mut self, key: &K) -> Option<V>
    where
        K: Ord,
    {
        match self.remove_entry(key) {
            Some((_k, v)) => Some(v),
            None => None,
        }
    }

    /// Clear out the binary tree.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use tinymap::ArrayMap;
    /// struct Album { name: &'static str }
    ///
    /// let mut albums_by_artist: ArrayMap<&'static str, Album, 5> = ArrayMap::new();
    ///
    /// albums_by_artist.insert("Owl City", Album { name: "Ocean Lights" });
    /// albums_by_artist.insert("Billy Joel", Album { name: "Glass Houses" });
    /// albums_by_artist.insert("Frank Sinatra", Album { name: "My Way" });
    ///
    /// // You know what? I've decided I'm not really that into music anymore.
    /// albums_by_artist.clear();
    ///
    /// assert_eq!(albums_by_artist.len(), 0);
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.arena.clear();
        self.root = None;
    }

    /// Iterate over the elements of this binary tree in arbitrary order.
    #[inline]
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter::new(self.arena.iter())
    }

    /// Iterate over the elements of this binary tree in arbitrary order, mutably.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut::new(self.arena.iter_mut())
    }

    /// Iterate over the keys of this binary tree in arbitrary order.
    #[inline]
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys::new(self.iter())
    }

    /// Iterate over the values of this binary tree in arbitrary order.
    #[inline]
    pub fn values(&self) -> Values<'_, K, V> {
        Values::new(self.iter())
    }

    /// Iterate over the values of this binary tree in arbitrary order, mutably.
    #[inline]
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut::new(self.iter_mut())
    }

    /// Drain the values from this map.
    #[inline]
    pub fn drain(&mut self) -> Drain<'_, K, V> {
        Drain::new(self.arena.iter_mut())
    }
}

impl<K: PartialOrd, V, const N: usize> Default for ArrayMap<K, V, N> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<K: PartialOrd + Clone, V: Clone, const N: usize> Clone for ArrayMap<K, V, N> {
    #[inline]
    fn clone(&self) -> Self {
        ArrayMap {
            arena: self.arena.clone(),
            root: self.root,
        }
    }
}

impl<K: PartialOrd + fmt::Debug, V: fmt::Debug, const N: usize> fmt::Debug for ArrayMap<K, V, N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.arena, f)
    }
}

impl<K: PartialOrd, V, const N: usize> iter::IntoIterator for ArrayMap<K, V, N> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V, N>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self.arena.into_iter())
    }
}

impl<K: Ord, V, const N: usize> iter::Extend<(K, V)> for ArrayMap<K, V, N> {
    #[inline]
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        iter.into_iter().for_each(|(k, v)| {
            self.insert(k, v);
        });
    }
}

impl<K: Ord, V, const N: usize> iter::FromIterator<(K, V)> for ArrayMap<K, V, N> {
    #[inline]
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut map = ArrayMap::new();
        map.extend(iter);
        map
    }
}
