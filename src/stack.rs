use crate::{common::noop, guard_read_stack::GuardRead, owned_alloc::OwnedAlloc};
use core::{
  fmt,
  iter::FromIterator,
  mem::ManuallyDrop,
  ptr::{null_mut, NonNull},
  sync::atomic::{AtomicPtr, AtomicUsize, Ordering::*},
};

/// A lock-free stack. LIFO/FILO semanthics are fully respected.
pub struct Stack<T> {
  incin: SharedIncin<T>,
  length: AtomicUsize,
  top: AtomicPtr<Node<T>>,
}

impl<T> Stack<T> {
  /// Creates a new empty stack.
  pub fn new() -> Self {
    Self::with_incin(SharedIncin::new())
  }

  /// Creates an empty queue using the passed shared incinerator.
  pub fn with_incin(incin: SharedIncin<T>) -> Self {
    Self {
      incin,
      length: AtomicUsize::default(),
      top: AtomicPtr::new(null_mut()),
    }
  }

  /// Returns the shared incinerator used by this [`Stack`].
  pub fn incin(&self) -> SharedIncin<T> {
    self.incin.clone()
  }

  /// Creates an iterator over `T`s, based on [`pop`](Stack::pop) operation of
  /// the [`Stack`].
  pub fn pop_iter(&self) -> PopIter<'_, T> {
    PopIter { stack: self }
  }

  /// Pushes a new value onto the top of the stack.
  pub fn push(&self, val: T) {
    // Let's first create a node.
    let mut target = OwnedAlloc::new(Node::new(val, self.top.load(Acquire)));

    loop {
      // Let's try to publish our changes.
      let new_top = target.raw().as_ptr();
      match self
        .top
        .compare_exchange(target.next, new_top, Release, Relaxed)
      {
        Ok(_) => {
          self.length.fetch_add(1, AcqRel);
          // Let's be sure we do not deallocate the pointer.
          target.into_raw();
          break;
        }

        Err(ptr) => target.next = ptr,
      }
    }
  }

  /// Pops a single element from the top of the stack.
  pub fn pop(&self, mut on_retry: impl FnMut() + Clone) -> Option<T> {
    // We need this because of ABA problem and use-after-free.
    let pause = self.incin.get_unchecked().pause(on_retry.clone());
    // First, let's load our top.
    let mut top = self.top.load(Acquire);

    loop {
      // If top is null, we have nothing. Try operator (?) handles it.
      let mut nnptr = NonNull::new(top)?;
      // The replacement for top is its "next". This is only possible
      // because of incinerator. Otherwise, we would face the "ABA
      // problem".
      //
      // Note this dereferral is safe because we only delete nodes via
      // incinerator and we have a pause now.
      match self
        .top
        .compare_exchange(top, unsafe { nnptr.as_ref().next }, AcqRel, Acquire)
      {
        Ok(_) => {
          // Done with an element. Let's first get the "val" to be
          // returned.
          //
          // This derreferal and read are safe since we drop the
          // node via incinerator and we never drop the inner value
          // when dropping the node in the incinerator.
          let val = unsafe { (&mut *nnptr.as_mut().val as *mut T).read() };
          // Safe because we already removed the node and we are
          // adding to the incinerator rather than
          // dropping it directly.
          self.length.fetch_sub(1, AcqRel);
          pause.add_to_incin(unsafe { OwnedAlloc::from_raw(nnptr) });
          break Some(val);
        }

        Err(new_top) => top = new_top,
      };

      on_retry();
    }
  }

  /// Peek at a single element from the top of the stack. Returns a guard, nothing is removed.
  pub fn top_peek(&self, mut on_retry: impl FnMut() + Clone) -> Option<GuardRead<T>> {
    // We need this because of ABA problem and use-after-free.
    let pause = self.incin.get_unchecked().pause(on_retry.clone());
    // First, let's load our top.
    let mut top = self.top.load(Acquire);

    loop {
      // If top is null, we have nothing. Try operator (?) handles it.
      let nnptr = NonNull::new(top)?;

      if let Err(new_top) =
        self
          .top
          .fetch_update(AcqRel, Acquire, |x| if x == top { Some(top) } else { None })
      {
        top = new_top;
      } else {
        return Some(GuardRead::new(pause, nnptr));
      }

      on_retry();
    }
  }

  /// Pushes elements from the given iterable. Acts just like
  /// [`Extend::extend`] but does not require mutability.
  pub fn extend<I>(&self, iterable: I)
  where
    I: IntoIterator<Item = T>,
  {
    for elem in iterable {
      self.push(elem);
    }
  }
}

impl<T> Stack<T> {
  /// Returns the number of elements in the stack.
  pub fn len(&self) -> usize {
    self.length.load(Acquire)
  }

  /// Returns `true` if the stack is empty otherwise `false`.
  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }
}

impl<T> Default for Stack<T> {
  fn default() -> Self {
    Self::new()
  }
}

impl<T> Drop for Stack<T> {
  fn drop(&mut self) {
    for _ in self.by_ref() {}
  }
}

impl<T> Iterator for Stack<T> {
  type Item = T;

  fn next(&mut self) -> Option<T> {
    let top = self.top.get_mut();

    NonNull::new(*top).map(|nnptr| {
      // This is safe because we only store pointers allocated via
      // `OwnedAlloc`. Also, we have exclusive access to this pointer.
      let mut node = unsafe { OwnedAlloc::from_raw(nnptr) };
      *top = node.next;
      // This read is we never drop the inner value when dropping the
      // node.
      unsafe { (&mut *node.val as *mut T).read() }
    })
  }
}

impl<T> Extend<T> for Stack<T> {
  fn extend<I>(&mut self, iterable: I)
  where
    I: IntoIterator<Item = T>,
  {
    (*self).extend(iterable)
  }
}

impl<T> FromIterator<T> for Stack<T> {
  fn from_iter<I>(iterable: I) -> Self
  where
    I: IntoIterator<Item = T>,
  {
    let this = Self::new();
    this.extend(iterable);
    this
  }
}

impl<T> fmt::Debug for Stack<T> {
  fn fmt(&self, fmtr: &mut fmt::Formatter) -> fmt::Result {
    write!(
      fmtr,
      "Stack {{ top: {:?}, incin: {:?} }}",
      self.top, self.incin
    )
  }
}

unsafe impl<T> Send for Stack<T> where T: Send {}

unsafe impl<T> Sync for Stack<T> where T: Send {}

/// An iterator based on [`pop`](Stack::pop) operation of the [`Stack`].
pub struct PopIter<'stack, T>
where
  T: 'stack,
{
  stack: &'stack Stack<T>,
}

impl<T> Iterator for PopIter<'_, T> {
  type Item = T;

  fn next(&mut self) -> Option<Self::Item> {
    self.stack.pop(noop)
  }
}

impl<T> fmt::Debug for PopIter<'_, T> {
  fn fmt(&self, fmtr: &mut fmt::Formatter) -> fmt::Result {
    write!(fmtr, "PopIter {{ stack: {:?} }}", self.stack)
  }
}

make_shared_incin! {
    { "[`Stack`]" }
    pub SharedIncin<T> of OwnedAlloc<Node<T>>
}

impl<T> fmt::Debug for SharedIncin<T> {
  fn fmt(&self, fmtr: &mut fmt::Formatter) -> fmt::Result {
    write!(fmtr, "SharedIncin {{ inner: {:?} }}", self.inner)
  }
}

#[derive(Debug)]
pub(crate) struct Node<T> {
  pub(crate) val: ManuallyDrop<T>,
  next: *mut Node<T>,
}

impl<T> Node<T> {
  fn new(val: T, next: *mut Node<T>) -> Self {
    Self {
      val: ManuallyDrop::new(val),
      next,
    }
  }
}

// Testing the safety of `unsafe` in this module is done with random operations
// via fuzzing
#[cfg(test)]
mod test {
  use std::thread::yield_now;

  use super::*;

  #[test]
  fn on_empty_first_pop_is_none() {
    let stack = Stack::<usize>::new();
    assert!(stack.pop(yield_now).is_none());
  }

  #[test]
  fn on_empty_last_pop_is_none() {
    let stack = Stack::new();
    stack.push(3);
    stack.push(1234);
    stack.pop(yield_now);
    stack.pop(yield_now);
    assert!(stack.pop(yield_now).is_none());
  }

  #[test]
  fn length_is_empty() {
    let stack = Stack::new();
    assert_eq!(stack.len(), 0);
    assert!(stack.is_empty());
    stack.push(3);
    stack.push(1234);

    assert_eq!(stack.len(), 2);
    assert!(!stack.is_empty());

    stack.pop(yield_now);
    assert_eq!(stack.len(), 1);
    stack.pop(yield_now);
    assert_eq!(stack.len(), 0);
  }

  #[test]
  fn top_peek() {
    let stack = Stack::new();

    stack.push(3);
    stack.push(1234);
    assert_eq!(stack.len(), 2);

    let guard = stack.top_peek(yield_now).expect("This must work.");
    assert_eq!(stack.len(), 2);
    assert_eq!(*guard, 1234);
    assert_eq!(stack.pop(yield_now), Some(1234));
    assert_eq!(stack.len(), 1);
  }

  #[test]
  fn order() {
    let stack = Stack::new();
    stack.push(4);
    stack.push(3);
    stack.push(5);
    stack.push(6);
    assert_eq!(stack.pop(yield_now), Some(6));
    assert_eq!(stack.pop(yield_now), Some(5));
    assert_eq!(stack.pop(yield_now), Some(3));
  }

  #[cfg(feature = "std")]
  #[test]
  fn no_data_corruption() {
    use std::sync::Arc;
    use std::thread;

    const NTHREAD: usize = 20;
    const NITER: usize = 800;
    const NMOD: usize = 55;

    let stack = Arc::new(Stack::new());

    thread::scope(|s| {
      for i in 0..NTHREAD {
        s.spawn({
          let stack = stack.clone();

          move || {
            for j in 0..NITER {
              let val = (i * NITER) + j;
              stack.push(val);
              if (val + 1) % NMOD == 0 {
                if let Some(val) = stack.pop(yield_now) {
                  assert!(val < NITER * NTHREAD);
                }
              }
            }
          }
        });
      }
    });

    let expected = NITER * NTHREAD - NITER * NTHREAD / NMOD;
    let mut res = 0;
    while let Some(val) = stack.pop(yield_now) {
      assert!(val < NITER * NTHREAD);
      res += 1;
    }

    assert_eq!(res, expected);
  }

  #[cfg(feature = "std")]
  #[test]
  fn stability() {
    use std::sync::Arc;
    use std::thread;

    use crate::set::Set;

    const NTHREAD: usize = 500 * 20;
    const NITER: usize = 800;

    let stack = Arc::new(Stack::new());
    let set = Arc::new(Set::new());

    thread::scope(|s| {
      for i in 0..NTHREAD {
        s.spawn({
          let stack = stack.clone();

          move || {
            for j in 0..NITER {
              stack.push(format!("{i}_{j}"));
            }
          }
        });

        s.spawn({
          let stack = stack.clone();
          let set = set.clone();

          move || {
            for _ in 0..NITER {
              loop {
                if let Some(val) = stack.pop(yield_now) {
                  set.insert(val, yield_now).unwrap();
                  break;
                }

                yield_now();
              }
            }
          }
        });

        s.spawn({
          let stack = stack.clone();

          move || {
            for _ in 0..NITER {
              stack.top_peek(yield_now);
            }
          }
        });
      }
    });

    assert_eq!(set.len(), NTHREAD * NITER);
  }
}
