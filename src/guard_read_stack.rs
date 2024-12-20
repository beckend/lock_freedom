use crate::{incin::Pause, owned_alloc::OwnedAlloc, stack::Node};
use core::ptr::NonNull;
use std::ops::Deref;

/// A guard for reading items.
#[allow(missing_debug_implementations)]
pub struct GuardRead<'a, T> {
  #[allow(dead_code)]
  /// The guard.
  pub(crate) guard: Pause<'a, OwnedAlloc<Node<T>>>,
  /// The node read guarded.
  pub(crate) node: NonNull<Node<T>>,
}

impl<'a, T> GuardRead<'a, T> {
  /// Creates a new instance.
  pub(crate) fn new(guard: Pause<'a, OwnedAlloc<Node<T>>>, node: NonNull<Node<T>>) -> Self {
    Self { guard, node }
  }
}

impl<T> Deref for GuardRead<'_, T> {
  type Target = T;

  fn deref(&self) -> &Self::Target {
    unsafe { &self.node.as_ref().val }
  }
}

#[allow(unsafe_code)]
unsafe impl<T> Send for GuardRead<'_, T> where T: Send {}
#[allow(unsafe_code)]
unsafe impl<T> Sync for GuardRead<'_, T> where T: Send {}
