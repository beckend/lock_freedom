mod bucket;
mod guard;
mod insertion;
mod iter;
mod table;

pub use self::{
  guard::{ReadGuard, Removed},
  insertion::{Insertion, Preview},
  iter::{IntoIter, Iter, IterMut},
};
use alloc::vec::Vec;

use self::{
  bucket::{Bucket, Garbage},
  insertion::{InsertNew, Reinsert},
  table::Table,
};
use crate::ptr::check_null_align;
use crate::{common::noop, owned_alloc::OwnedAlloc};
use core::{
  borrow::Borrow,
  fmt,
  hash::{BuildHasher, Hash},
  iter::FromIterator,
  mem,
  sync::atomic::{self, AtomicUsize},
};
use std::collections::hash_map::RandomState;

/// A lock-free map. Implemented using multi-level hash-tables (in a tree
/// fashion) with ordered buckets.
///
/// # Design
/// In order to implement this map, we shall fix a constant named `BITS`, which
/// should be smaller than the number of bits in the hash (and not 0). We chose
/// `8` for it. Now, we define a table structure: an array of nodes with length
/// `1 << BITS` (`256` in this case).
///
/// For inserting, we take the first `BITS` bits of the hash. Now, we verify
/// the node. If it is empty, insert a new bucket with our entry (a leaf of the
/// tree), and assign our hash to the bucket. If there is a branch (i.e. a
/// sub-table), we shift the hash `BITS` bits to the left, but we also keep the
/// original hash for consultation. Then we try again in the sub-table. If
/// there is another leaf, and if the hash of the leaf's bucket is equal to
/// ours, we insert our entry into the bucket. If the hashes are not equal, we
/// create a sub-table, insert the old leaf into the new sub-table, and insert
/// our pair after.
///
/// Entries in a bucket are a single linked list ordered by key. The ordering
/// of the list is because of possible race conditions if e.g. new nodes were
/// always inserted at end. And if a bucket is detected to be empty, the
/// table will be requested to delete the bucket.
///
/// For searching, in a similar way, the hash is shifted and sub-tables are
/// entered until either a node is empty or a leaf is found. If the hash of the
/// leaf's bucket is equal to our hash, we search for the entry into the bucket.
/// Because the bucket is ordered, we may know the entry is not present with
/// ease.
///
/// Because of limitation of sharing in concurrent contexts, we do return plain
/// references to the entries, neither allow the user to move out removed
/// values, as they must be deinitialized correctly. Instead, we return guarded
/// references to the entries and wrappers over removed entries.
pub struct Map<K, V, H = RandomState> {
  builder: H,
  incin: SharedIncin<K, V>,
  length: AtomicUsize,
  top: OwnedAlloc<Table<K, V>>,
}

impl<K, V> Map<K, V> {
  /// Creates a new [`Map`] with the default hasher builder.
  pub fn new() -> Self {
    check_null_align::<Table<K, V>>();
    check_null_align::<Bucket<K, V>>();
    Self::default()
  }

  /// Creates the [`Map`] using the given shared incinerator.
  pub fn with_incin(incin: SharedIncin<K, V>) -> Self {
    Self::with_hasher_and_incin(RandomState::default(), incin)
  }
}

impl<K, V, H> Map<K, V, H> {
  /// Returns the number of entries in the map.
  pub fn len(&self) -> usize {
    self.length.load(atomic::Ordering::Acquire)
  }

  /// Returns `true` if the map is empty or `false` otherwise.
  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }
}

impl<K, V, H> Map<K, V, H> {
  /// Creates an iterator over guarded references to the key-value entries.
  pub fn iter(&self) -> Iter<K, V> {
    self.into_iter()
  }

  /// Creates an iterator over the key-value entries, with a mutable reference
  /// to the value.
  pub fn iter_mut(&mut self) -> IterMut<K, V> {
    self.into_iter()
  }

  /// Tries to optimize space by removing unnecessary tables *without removing
  /// any entry*. This method might also clear delayed resource destruction.
  /// This method cannot be performed in a shared context.
  pub fn optimize_space(&mut self) {
    self.incin.clear();
    self.top.optimize_space();
  }

  /// Removes all entries. This method might also clear delayed resource
  /// destruction. This method cannot be performed in a shared context.
  pub fn clear(&mut self) {
    self.incin.clear();
    let mut tables = Vec::new();
    self.top.clear(&mut tables);

    while let Some(mut table) = tables.pop() {
      // This is safe because we won't be using these tables anymore. We
      // won't load its nodes' contents.
      unsafe { table.free_nodes(&mut tables) }
    }
  }
}

impl<K, V, H> Map<K, V, H>
where
  H: BuildHasher,
{
  /// Creates the [`Map`] using the given hasher builder.
  pub fn with_hasher(builder: H) -> Self {
    Self::with_hasher_and_incin(builder, SharedIncin::new())
  }

  /// Creates the [`Map`] using the given hasher builder and shared
  /// incinerator.
  pub fn with_hasher_and_incin(builder: H, incin: SharedIncin<K, V>) -> Self {
    Self {
      builder,
      incin,
      length: Default::default(),
      top: Table::new_alloc(),
    }
  }

  /// The shared incinerator used by this [`Map`].
  pub fn incin(&self) -> SharedIncin<K, V> {
    self.incin.clone()
  }

  /// The hasher buider used by this [`Map`].
  pub fn hasher(&self) -> &H {
    &self.builder
  }

  /// Searches for the entry identified by the given key. The returned value
  /// is a guarded reference. Guarded to ensure no thread deallocates the
  /// allocation for the entry while it is being used. The method accepts
  /// a type resulted from borrowing the stored key. This method will only
  /// work correctly if [`Hash`] and [`Ord`] are implemented in the same way
  /// for the borrowed type and the stored type. If the entry was not
  /// found, [`None`] is returned.
  pub fn get<'map, Q>(&'map self, key: &Q, on_retry: impl FnMut()) -> Option<ReadGuard<'map, K, V>>
  where
    Q: ?Sized + Hash + Ord,
    K: Borrow<Q>,
  {
    let hash = self.hash_of(key);
    let pause = self.incin.get_unchecked().pause(on_retry);
    // Safe because we paused properly.
    unsafe { self.top.get(key, hash, pause) }
  }

  /// Inserts unconditionally the given key and value. If there was a
  /// previously stored value, it is returned.
  pub fn insert(&self, key: K, val: V, on_retry: impl FnMut()) -> Option<Removed<K, V>>
  where
    K: Hash + Ord,
  {
    let pause = self.incin.get_unchecked().pause(on_retry);
    let hash = self.hash_of(&key);
    // Safe because we paused properly.
    let insertion = unsafe {
      self.top.insert(
        InsertNew::with_pair(|_, _, _| Preview::Keep, (key, val)),
        hash,
        &pause,
        self.incin.get_unchecked(),
      )
    };

    match insertion {
      Insertion::Created => {
        self.length.fetch_add(1, atomic::Ordering::AcqRel);
        None
      }
      Insertion::Updated(old) => Some(old),
      Insertion::Failed(_) => unreachable!(),
    }
  }

  /// Inserts _interactively_ the given key. A closure is passed to generate
  /// the value part of the entry and validate it with the found value. Even
  /// though the closure may have already accepted some condition, it might
  /// get recalled many times due to concurrent modifications of the [`Map`].
  ///
  /// The first argument passed to the closure is the key passed in first
  /// place. The second argument is an optional mutable reference to a
  /// previously generated value. Obviously, if no value was ever generated,
  /// it is [`None`]. The third argument is a reference to the found stored
  /// entry. Obviously, if no stored entry was found, it is `None`. The return
  /// value of the closure is a specification of "what to do with the
  /// insertion now".
  pub fn insert_with<F>(
    &self,
    key: K,
    interactive: F,
    on_retry: impl FnMut(),
  ) -> Insertion<K, V, (K, Option<V>)>
  where
    K: Hash + Ord,
    F: FnMut(&K, Option<&mut V>, Option<&(K, V)>) -> Preview<V>,
  {
    let hash = self.hash_of(&key);
    let pause = self.incin.get_unchecked().pause(on_retry);
    // Safe because we paused properly.
    let insertion = unsafe {
      self.top.insert(
        InsertNew::with_key(interactive, key),
        hash,
        &pause,
        self.incin.get_unchecked(),
      )
    };

    match insertion {
      Insertion::Created => {
        self.length.fetch_add(1, atomic::Ordering::AcqRel);
        Insertion::Created
      }
      Insertion::Updated(old) => Insertion::Updated(old),
      Insertion::Failed(inserter) => Insertion::Failed(inserter.into_pair()),
    }
  }

  /// Reinserts a previously removed entry. The entry must have been either:
  ///
  /// 1. Removed from any [`Map`] using the same [`SharedIncin`] as this [`Map`].
  /// 2. Removed from an already dead [`Map`] with dead [`SharedIncin`].
  /// 3. Removed from a [`Map`] whose `SharedIncin` has no sensitive reads active.
  ///
  /// If the removed entry does not fit any category, the insertion will fail.
  /// Otherwise, insertion cannot fail.
  pub fn reinsert(
    &self,
    mut removed: Removed<K, V>,
    on_retry: impl FnMut(),
  ) -> Insertion<K, V, Removed<K, V>>
  where
    K: Hash + Ord,
  {
    if !Removed::is_usable_by(&mut removed, self.incin.get_unchecked()) {
      return Insertion::Failed(removed);
    }

    let hash = self.hash_of(removed.key());

    let pause = self.incin.get_unchecked().pause(on_retry);
    // Safe because we paused properly.
    let insertion = unsafe {
      self.top.insert(
        Reinsert::new(|_, _| true, removed),
        hash,
        &pause,
        self.incin.get_unchecked(),
      )
    };

    match insertion {
      Insertion::Created => {
        self.length.fetch_add(1, atomic::Ordering::AcqRel);
        Insertion::Created
      }
      Insertion::Updated(old) => Insertion::Updated(old),
      Insertion::Failed(_) => unreachable!(),
    }
  }

  /// Reinserts _interactively_ a previously removed entry. A closure will be
  /// passed to validate if the conditions are correct for the reinsertion.
  /// The first argument passed to the closure is a reference to the removed
  /// entry, the second argument is a reference to the stored found entry.
  /// Obviously, if no stored entry was found, the argument is [`None`]. The
  /// returned value is a boolean indicating if the reinsertion should go on.
  /// Even though the closure may have already accepted some condition, it
  /// might get recalled many times due to concurrent modifications of the
  /// [`Map`].
  ///
  /// The entry must have been either:
  ///
  /// 1. Removed from any [`Map`] using the same [`SharedIncin`] as this [`Map`].
  /// 2. Removed from an already dead [`Map`] with dead `SharedIncin`.
  /// 3. Removed from a [`Map`] whose `SharedIncin` has no sensitive reads active.
  ///
  /// If the removed entry does not fit any category, the insertion will fail.
  /// Otherwise, insertion cannot fail.
  pub fn reinsert_with<F>(
    &self,
    mut removed: Removed<K, V>,
    interactive: F,
    on_retry: impl FnMut(),
  ) -> Insertion<K, V, Removed<K, V>>
  where
    K: Hash + Ord,
    F: FnMut(&(K, V), Option<&(K, V)>) -> bool,
  {
    if !Removed::is_usable_by(&mut removed, self.incin.get_unchecked()) {
      return Insertion::Failed(removed);
    }

    let hash = self.hash_of(removed.key());

    let pause = self.incin.get_unchecked().pause(on_retry);
    // Safe because we paused properly.
    let insertion = unsafe {
      self.top.insert(
        Reinsert::new(interactive, removed),
        hash,
        &pause,
        self.incin.get_unchecked(),
      )
    };

    match insertion {
      Insertion::Created => {
        self.length.fetch_add(1, atomic::Ordering::AcqRel);
        Insertion::Created
      }
      Insertion::Updated(old) => Insertion::Updated(old),
      Insertion::Failed(inserter) => Insertion::Failed(inserter.into_removed()),
    }
  }

  /// Removes unconditionally the entry identified by the given key. If no
  /// entry was found, [`None`] is returned. This method will only work
  /// correctly if [`Hash`] and [`Ord`] are implemented in the same way for
  /// the borrowed type and the stored type. If the entry was not found,
  /// `None` is returned.
  pub fn remove<Q>(&self, key: &Q, on_retry: impl FnMut()) -> Option<Removed<K, V>>
  where
    Q: ?Sized + Hash + Ord,
    K: Borrow<Q>,
  {
    self.remove_with(key, |_| true, on_retry)
  }

  /// Removes _interactively_ the entry identified by the given key. A closure
  /// is passed to validate the removal. The only argument passed to the
  /// closure is a reference to the found entry. The closure returns if the
  /// removal should go on. If no entry was found, `None` is returned. This
  /// method will only work correctly if [`Hash`] and [`Ord`] are implemented
  /// in the same way for the borrowed type and the stored type. If the
  /// entry was not found, [`None`] is returned.
  pub fn remove_with<Q, F>(
    &self,
    key: &Q,
    interactive: F,
    on_retry: impl FnMut(),
  ) -> Option<Removed<K, V>>
  where
    Q: ?Sized + Hash + Ord,
    K: Borrow<Q>,
    F: FnMut(&(K, V)) -> bool,
  {
    let hash = self.hash_of(key);
    let pause = self.incin.get_unchecked().pause(on_retry);
    // Safe because we paused properly.
    let removed = unsafe {
      self
        .top
        .remove(key, interactive, hash, &pause, self.incin.get_unchecked())
    };

    if removed.is_some() {
      self.length.fetch_sub(1, atomic::Ordering::AcqRel);
    }

    removed
  }

  /// Acts just like [`Extend::extend`] but does not require mutability.
  pub fn extend<I>(&self, iterable: I, on_retry: impl FnMut() + Clone)
  where
    I: IntoIterator<Item = (K, V)>,
    K: Hash + Ord,
  {
    for (key, val) in iterable {
      self.insert(key, val, on_retry.clone());
    }
  }

  fn hash_of<Q>(&self, key: &Q) -> u64
  where
    Q: ?Sized + Hash,
  {
    self.builder.hash_one(key)
  }
}

impl<K, V, H> Default for Map<K, V, H>
where
  H: BuildHasher + Default,
{
  fn default() -> Self {
    Self::with_hasher(H::default())
  }
}

impl<K, V, H> fmt::Debug for Map<K, V, H>
where
  H: fmt::Debug,
{
  fn fmt(&self, fmtr: &mut fmt::Formatter) -> fmt::Result {
    write!(
      fmtr,
      "Map {{ top_table: {:?}, incin: {:?}, build_hasher: {:?} }}",
      self.top,
      self.incin.get_unchecked(),
      self.builder
    )
  }
}

impl<K, V, H> Drop for Map<K, V, H> {
  fn drop(&mut self) {
    let mut tables = Vec::new();

    // Safe because we won't use these nodes anymore. We are in the
    // destructor.
    unsafe { self.top.free_nodes(&mut tables) }

    while let Some(mut table) = tables.pop() {
      // Safe because we won't use these nodes anymore. We are in the
      // destructor.
      unsafe { table.free_nodes(&mut tables) }
    }
  }
}

impl<'map, K, V, H> IntoIterator for &'map Map<K, V, H> {
  type Item = ReadGuard<'map, K, V>;

  type IntoIter = Iter<'map, K, V>;

  fn into_iter(self) -> Self::IntoIter {
    Iter::new(self.incin.get_unchecked().pause(noop), &self.top)
  }
}

impl<'map, K, V, H> IntoIterator for &'map mut Map<K, V, H> {
  type Item = (&'map K, &'map mut V);

  type IntoIter = IterMut<'map, K, V>;

  fn into_iter(self) -> Self::IntoIter {
    IterMut::new(&mut self.top)
  }
}

impl<K, V, H> IntoIterator for Map<K, V, H> {
  type Item = (K, V);

  type IntoIter = IntoIter<K, V>;

  fn into_iter(mut self) -> Self::IntoIter {
    let raw = self.top.raw();
    // Unfortunately, this unsafe is needed since there is no other way of
    // dropping the field and forgetting the Map.
    unsafe {
      (&mut self.builder as *mut H).drop_in_place();
      (&mut self.incin as *mut SharedIncin<K, V>).drop_in_place();
      mem::forget(self);
      IntoIter::new(OwnedAlloc::from_raw(raw))
    }
  }
}

impl<K, V, H> Extend<(K, V)> for Map<K, V, H>
where
  H: BuildHasher,
  K: Hash + Ord,
{
  fn extend<I>(&mut self, iterable: I)
  where
    I: IntoIterator<Item = (K, V)>,
  {
    (*self).extend(iterable, noop)
  }
}

impl<K, V, H> FromIterator<(K, V)> for Map<K, V, H>
where
  H: BuildHasher + Default,
  K: Hash + Ord,
{
  fn from_iter<I>(iterable: I) -> Self
  where
    I: IntoIterator<Item = (K, V)>,
  {
    let this = Self::default();
    this.extend(iterable, noop);
    this
  }
}

unsafe impl<K, V, H> Send for Map<K, V, H>
where
  K: Send,
  V: Send,
  H: Send,
{
}

unsafe impl<K, V, H> Sync for Map<K, V, H>
where
  K: Sync,
  V: Sync,
  H: Sync,
{
}

make_shared_incin! {
    { "[`Map`]" }
    pub SharedIncin<K, V> of Garbage<K, V>
}

impl<K, V> fmt::Debug for SharedIncin<K, V> {
  fn fmt(&self, fmtr: &mut fmt::Formatter) -> fmt::Result {
    write!(fmtr, "SharedIncin {{ inner: {:?} }}", self.inner)
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use alloc::format;
  use alloc::sync::Arc;
  use std::{
    collections::HashMap,
    thread::{self, yield_now},
  };

  #[test]
  fn inserts_and_gets() {
    let map = Map::new();
    assert!(map.get("five", yield_now).is_none());
    assert!(map.insert("five".to_owned(), 5, yield_now).is_none());
    assert_eq!(*map.get("five", yield_now).unwrap().val(), 5);
    assert!(map.get("four", yield_now).is_none());
    assert!(map.insert("four".to_owned(), 4, yield_now).is_none());
    assert_eq!(*map.get("five", yield_now).unwrap().val(), 5);
    assert_eq!(*map.get("four", yield_now).unwrap().val(), 4);
    let guard = map.get("four", yield_now).unwrap();
    assert_eq!(guard.key(), "four");
    assert_eq!(*guard.val(), 4);
  }

  #[test]
  fn len_is_empty() {
    let map = Map::new();

    assert_eq!(map.len(), 0);
    assert!(map.is_empty());

    map.insert("five".to_owned(), 5, yield_now);

    assert_eq!(map.len(), 1);
    assert!(!map.is_empty());
  }

  #[test]
  fn create() {
    let map = Map::new();
    assert_eq!(map.len(), 0);

    assert!(map
      .insert_with(
        "five".to_owned(),
        |_, _, stored| if stored.is_none() {
          Preview::New(5)
        } else {
          Preview::Discard
        },
        yield_now
      )
      .created());

    assert_eq!(map.len(), 1);

    assert_eq!(*map.get("five", yield_now).unwrap().val(), 5);

    assert_eq!(map.len(), 1);

    assert!(map
      .insert_with(
        "five".to_owned(),
        |_, _, stored| if stored.is_none() {
          Preview::New(500)
        } else {
          Preview::Discard
        },
        yield_now
      )
      .failed()
      .is_some());

    assert_eq!(map.len(), 1);
  }

  #[test]
  fn update() {
    let map = Map::new();

    assert_eq!(map.len(), 0);

    assert!(map
      .insert_with(
        "five".to_owned(),
        |_, _, stored| {
          if let Some((_, n)) = stored {
            Preview::New(*n + 6)
          } else {
            Preview::Discard
          }
        },
        yield_now
      )
      .failed()
      .is_some());

    assert_eq!(map.len(), 0);

    assert!(map.insert("five".to_owned(), 5, yield_now).is_none());

    assert_eq!(map.len(), 1);

    let guard = map
      .insert_with(
        "five".to_owned(),
        |_, _, stored| {
          if let Some((_, n)) = stored {
            Preview::New(*n + 7)
          } else {
            Preview::Discard
          }
        },
        yield_now,
      )
      .take_updated()
      .unwrap();

    assert_eq!(map.len(), 1);

    assert_eq!(guard.key(), "five");
    assert_eq!(*guard.val(), 5);
    assert_eq!(*map.get("five", yield_now).unwrap().val(), 12);
  }

  #[test]
  fn never_inserts() {
    let map = Map::new();
    assert!(map
      .insert_with("five".to_owned(), |_, _, _| Preview::Discard, yield_now)
      .failed()
      .is_some());
    assert!(map.insert("five".to_owned(), 5, yield_now).is_none());
    assert!(map
      .insert_with("five".to_owned(), |_, _, _| Preview::Discard, yield_now)
      .failed()
      .is_some());
  }

  #[test]
  fn inserts_reinserts() {
    let map = Map::new();
    assert!(map.insert("four".to_owned(), 4, yield_now).is_none());
    let prev = map.insert("four".to_owned(), 40, yield_now).unwrap();
    assert_eq!(prev.key(), "four");
    assert_eq!(*prev.val(), 4);
    let prev = map.reinsert(prev, yield_now).take_updated().unwrap();
    assert_eq!(prev.key(), "four");
    assert_eq!(*prev.val(), 40);
    assert!(*map.get("four", yield_now).unwrap().val() == 4);
  }

  #[test]
  fn never_reinserts() {
    let map = Map::new();
    map.insert("five".to_owned(), 5, yield_now);
    let prev = map.remove("five", yield_now).unwrap();
    let prev = map
      .reinsert_with(prev, |_, _| false, yield_now)
      .take_failed()
      .unwrap();
    assert!(map.insert("five".to_owned(), 5, yield_now).is_none());
    map
      .reinsert_with(prev, |_, _| false, yield_now)
      .take_failed()
      .unwrap();
  }

  #[test]
  fn reinserts_create() {
    let map = Map::new();
    map.insert("five".to_owned(), 5, yield_now);
    let first = map.remove("five", yield_now).unwrap();
    map.insert("five".to_owned(), 5, yield_now);
    let second = map.remove("five", yield_now).unwrap();
    assert!(map
      .reinsert_with(first, |_, stored| stored.is_none(), yield_now)
      .created());
    assert_eq!(*map.get("five", yield_now).unwrap().val(), 5);
    assert!(map
      .reinsert_with(second, |_, stored| stored.is_none(), yield_now)
      .failed()
      .is_some());
  }

  #[test]
  fn reinserts_update() {
    let map = Map::new();
    map.insert("five".to_owned(), 5, yield_now);
    let prev = map.remove("five", yield_now).unwrap();
    let prev = map
      .reinsert_with(prev, |_, stored| stored.is_some(), yield_now)
      .take_failed()
      .unwrap();
    map.insert("five".to_owned(), 5, yield_now);
    assert!(map
      .reinsert_with(prev, |_, stored| stored.is_some(), yield_now)
      .updated()
      .is_some());
  }

  #[test]
  fn inserts_and_removes() {
    let map = Map::new();
    assert!(map.remove("five", yield_now).is_none());
    assert!(map.remove("four", yield_now).is_none());
    map.insert("five".to_owned(), 5, yield_now);
    let removed = map.remove("five", yield_now).unwrap();
    assert_eq!(removed.key(), "five");
    assert_eq!(*removed.val(), 5);
    assert!(map.insert("four".to_owned(), 4, yield_now).is_none());
    map.insert("three".to_owned(), 3, yield_now);
    assert!(map.remove("two", yield_now).is_none());
    map.insert("two".to_owned(), 2, yield_now);
    let removed = map.remove("three", yield_now).unwrap();
    assert_eq!(removed.key(), "three");
    assert_eq!(*removed.val(), 3);
    let removed = map.remove("two", yield_now).unwrap();
    assert_eq!(removed.key(), "two");
    assert_eq!(*removed.val(), 2);
    let removed = map.remove("four", yield_now).unwrap();
    assert_eq!(removed.key(), "four");
    assert_eq!(*removed.val(), 4);
  }

  #[test]
  fn repeated_inserts() {
    let map = Map::new();
    assert!(map.insert("five".to_owned(), 5, yield_now).is_none());
    assert!(*map.insert("five".to_owned(), 5, yield_now).unwrap().val() == 5);
  }

  #[test]
  fn reinsert_from_other_map_fails() {
    let other = Map::new();
    other.insert(5, 3, yield_now);
    other.insert(0, 0, yield_now);
    let removed = other.remove(&5, yield_now).unwrap();
    let _active_read = other.get(&0, yield_now).unwrap();
    let map = Map::new();
    map.reinsert(removed, yield_now).failed().unwrap();
  }

  #[test]
  fn iter_valid_items() {
    let map = Map::new();
    for i in 0..10u128 {
      for j in 0..32 {
        map.insert((i, j), i << j, yield_now);
      }
    }

    let mut result = HashMap::new();
    for guard in &map {
      let (k, v) = *guard;
      let in_place = result.get(&(k, v)).map_or(0, |&x| x);
      result.insert((k, v), in_place + 1);
    }

    for i in 0..10 {
      for j in 0..32 {
        let pair = ((i, j), i << j);
        assert_eq!(*result.get(&pair).unwrap(), 1);
      }
    }
  }

  #[test]
  fn optimize_space_preserves_entries() {
    let mut map = Map::new();
    for i in 0..200u128 {
      for j in 0..128 {
        map.insert((i, j), i << j, yield_now);
      }
    }

    for i in 0..200 {
      for j in 0..16 {
        map.remove(&(i, j), yield_now);
      }
    }

    map.optimize_space();

    let mut result = HashMap::new();
    for guard in &map {
      let (k, v) = *guard;
      let in_place = result.get(&(k, v)).map_or(0, |&x| x);
      result.insert((k, v), in_place + 1);
    }

    for i in 0..200 {
      for j in 16..128 {
        let pair = ((i, j), i << j);
        assert_eq!(*result.get(&pair).unwrap(), 1);
      }
    }
  }

  #[test]
  fn iter_mut_and_into_iter() {
    let mut map = Map::new();
    for i in 0..10u128 {
      for j in 0..32 {
        map.insert((i, j), i << j, yield_now);
      }
    }

    let mut result = HashMap::new();
    for (k, v) in &mut map {
      let in_place = result.get(&(*k, *v)).map_or(0, |&x| x);
      result.insert((*k, *v), in_place + 1);
      *v += 1;
    }

    for i in 0..10 {
      for j in 0..32 {
        let pair = ((i, j), i << j);
        assert_eq!(*result.get(&pair).unwrap(), 1);
      }
    }

    result.clear();

    for (k, v) in map {
      let in_place = result.get(&(k, v)).map_or(0, |&x| x);
      result.insert((k, v), in_place + 1);
    }

    for i in 0..10 {
      for j in 0..32 {
        let pair = ((i, j), (i << j) + 1);
        assert_eq!(*result.get(&pair).unwrap(), 1);
      }
    }
  }

  #[test]
  fn multithreaded() {
    let map = Arc::new(Map::new());
    let mut threads = Vec::new();
    for i in 1i64..=20 {
      let map = map.clone();
      threads.push(thread::spawn(move || {
        let prev = map
          .get(&format!("prefix{}suffix", i - 1), yield_now)
          .map_or(0, |guard| *guard.val());
        map.insert(format!("prefix{}suffix", i), prev + i, yield_now);
        map.insert_with(
          format!("prefix{}suffix", i + 1),
          |_, _, stored| Preview::New(stored.map_or(0, |&(_, x)| x + i)),
          yield_now,
        );
      }));
    }
    for thread in threads {
      thread.join().expect("thread failed");
    }
    for i in 1i64..=20 {
      let val = *map
        .get(&format!("prefix{}suffix", i), yield_now)
        .unwrap()
        .val();
      assert!(val > 0);
    }
  }
}
