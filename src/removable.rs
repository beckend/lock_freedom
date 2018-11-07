pub use std::sync::atomic::Ordering;
use std::{
    fmt,
    mem::{uninitialized, ManuallyDrop},
    sync::atomic::{AtomicBool, Ordering::*},
};

/// A shared removable value. You can only take values from this type (no
/// insertion allowed). No extra allocation is necessary. It may be useful for
/// things like shared `thread::JoinHandle`s.
pub struct Removable<T> {
    item: ManuallyDrop<T>,
    present: AtomicBool,
}

impl<T> Removable<T> {
    /// Creates a removable value with the passed argument as a present value.
    pub fn new(val: T) -> Self {
        Self {
            item: ManuallyDrop::new(val),
            present: AtomicBool::new(true),
        }
    }

    /// Creates a removable value with no present value.
    pub fn empty() -> Self {
        Self {
            item: ManuallyDrop::new(unsafe { uninitialized() }),
            present: AtomicBool::new(false),
        }
    }

    /// Tests if the stored value is present using the given memory ordering.
    /// Note that there are no guarantees that `take` will be successful if
    /// this method returns `true` because some other thread could take the
    /// value meanwhile.
    pub fn is_present(&self, ordering: Ordering) -> bool {
        self.present.load(ordering)
    }

    /// Tries to take the value using the given memory ordering. If no value was
    /// present in first place, `None` is returned.
    pub fn take(&self, ordering: Ordering) -> Option<T> {
        let success = self.present.swap(false, ordering);
        if success {
            Some(unsafe { (&*self.item as *const T).read() })
        } else {
            None
        }
    }
}

impl<T> fmt::Debug for Removable<T> {
    fn fmt(&self, fmtr: &mut fmt::Formatter) -> fmt::Result {
        write!(
            fmtr,
            "Removable {} present: {:?} {}",
            '{',
            self.is_present(SeqCst),
            '}'
        )
    }
}

impl<T> Default for Removable<T> {
    fn default() -> Self {
        Self::empty()
    }
}

impl<T> Drop for Removable<T> {
    fn drop(&mut self) {
        if self.is_present(Relaxed) {
            unsafe { ManuallyDrop::drop(&mut self.item) }
        }
    }
}
