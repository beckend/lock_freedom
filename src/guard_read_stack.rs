use crate::{
  incin::Pause,
  owned_alloc::OwnedAlloc,
  stack::{Node, Stack},
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
  /// The stack.
  pub(crate) stack: &'a Stack<T>,
}

impl<'a, T> GuardRead<'a, T> {
  /// Creates a new instance.
  pub(crate) fn new(
    stack: &'a Stack<T>,
    guard: Pause<'a, OwnedAlloc<Node<T>>>,
    node: NonNull<Node<T>>,
  ) -> Self {
    Self {
      guard,
      inner: node,
      stack,
    }
  }

  /// Pops/takes the item from the stack while the guard is holding unto inner.
  pub fn pop(self, on_retry: impl FnMut() + Clone) -> T {
    self
      .stack
      .pop_with_guard(self.guard, on_retry)
      .expect("Must have item since we are holding it's guard.")
  }
}

impl<T> Deref for GuardRead<'_, T> {
  type Target = T;

  fn deref(&self) -> &Self::Target {
    unsafe { &self.inner.as_ref().val }
  }
}

#[allow(unsafe_code)]
unsafe impl<T> Send for GuardRead<'_, T> where T: Send {}
#[allow(unsafe_code)]
unsafe impl<T> Sync for GuardRead<'_, T> where T: Send {}
