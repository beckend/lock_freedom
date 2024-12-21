use crate::{
  incin::Pause,
  owned_alloc::OwnedAlloc,
  queue::{Node, Queue},
};
use core::ptr::NonNull;
use std::ops::Deref;

/// A guard for reading items.
#[allow(missing_debug_implementations)]
pub struct GuardRead<'a, T> {
  #[allow(dead_code)]
  /// The guard.
  pub(crate) guard: Pause<'a, OwnedAlloc<Node<T>>>,
  /// The node read guarded.
  pub(crate) inner: NonNull<Node<T>>,
  /// The queue.
  pub(crate) queue: &'a Queue<T>,
}

impl<'a, T> GuardRead<'a, T> {
  /// Creates a new instance.
  pub(crate) fn new(
    queue: &'a Queue<T>,
    guard: Pause<'a, OwnedAlloc<Node<T>>>,
    inner: NonNull<Node<T>>,
  ) -> Self {
    Self {
      guard,
      inner,
      queue,
    }
  }

  /// Pops/takes the item from the queue while the guard is holding unto inner.
  pub fn pop(self, on_retry: impl FnMut() + Clone) -> T {
    self
      .queue
      .pop_with_guard(self.guard, on_retry)
      .expect("Must have item since we are holding it's guard.")
  }
}

impl<T> Deref for GuardRead<'_, T> {
  type Target = T;

  #[allow(clippy::needless_borrow)]
  fn deref(&self) -> &Self::Target {
    unsafe {
      &self
        .inner
        .as_ref()
        .item
        .get_ref()
        .expect("This should be guarded.")
    }
  }
}

#[allow(unsafe_code)]
unsafe impl<T> Send for GuardRead<'_, T> where T: Send {}
#[allow(unsafe_code)]
unsafe impl<T> Sync for GuardRead<'_, T> where T: Send {}
