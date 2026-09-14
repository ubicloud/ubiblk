use std::cell::UnsafeCell;
use std::ops::{Deref, DerefMut};
use std::sync::atomic::{AtomicBool, Ordering};

/// A lock for critical sections a few instructions long, where parking a
/// thread would cost more than waiting for the holder to finish.
pub struct SpinLock<T> {
    locked: AtomicBool,
    value: UnsafeCell<T>,
}

// SAFETY: the value is only reachable through a guard, and only one guard
// exists at a time.
unsafe impl<T: Send> Send for SpinLock<T> {}
unsafe impl<T: Send> Sync for SpinLock<T> {}

impl<T> SpinLock<T> {
    pub fn new(value: T) -> Self {
        SpinLock {
            locked: AtomicBool::new(false),
            value: UnsafeCell::new(value),
        }
    }

    pub fn lock(&self) -> SpinLockGuard<'_, T> {
        while self
            .locked
            .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            std::hint::spin_loop();
        }
        SpinLockGuard {
            lock: self,
            _not_sync: std::marker::PhantomData,
        }
    }
}

pub struct SpinLockGuard<'a, T> {
    lock: &'a SpinLock<T>,
    /// Not `Sync` by default: see the impl below.
    _not_sync: std::marker::PhantomData<*const ()>,
}

// SAFETY: sharing a guard shares `&T`, which is only sound when `T` is `Sync`.
// Without this the guard would inherit `Sync` from the lock, which asks less.
unsafe impl<T: Sync> Sync for SpinLockGuard<'_, T> {}

impl<T> Deref for SpinLockGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // SAFETY: holding the guard means holding the lock.
        unsafe { &*self.lock.value.get() }
    }
}

impl<T> DerefMut for SpinLockGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: holding the guard means holding the lock.
        unsafe { &mut *self.lock.value.get() }
    }
}

impl<T> Drop for SpinLockGuard<'_, T> {
    fn drop(&mut self) {
        self.lock.locked.store(false, Ordering::Release);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn increments_from_many_threads_are_not_lost() {
        let lock = Arc::new(SpinLock::new(0u64));
        let threads: Vec<_> = (0..4)
            .map(|_| {
                let lock = lock.clone();
                std::thread::spawn(move || {
                    for _ in 0..100_000 {
                        *lock.lock() += 1;
                    }
                })
            })
            .collect();
        for thread in threads {
            thread.join().unwrap();
        }
        assert_eq!(*lock.lock(), 400_000);
    }
}
