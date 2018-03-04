#![cfg_attr(feature = "nightly", feature(const_atomic_usize_new))]
#![no_std]

#[macro_use]
#[no_link]
extern crate static_assertions;

use core::cmp::{Ord, Ordering as CmpOrdering, PartialOrd};
use core::fmt;
use core::sync::atomic::{AtomicUsize, Ordering};
use core::marker::{PhantomData, Sized};
use core::mem;
use core::ops::{Deref, DerefMut};

/// An atomic wrapper over an enum type.
///
/// Note that the enum is backed by an `AtomicUsize`, so `assert_eq!(mem::size_of::<Atomic<EnumType>>(), mem::size_of::<usize>());`
/// will always be true, regardless of the size of `EnumType`.
pub struct Atomic<E> {
    inner: AtomicUsize,
    _marker: PhantomData<E>,
}

#[cfg(feature = "nightly")]
pub const ATOMIC_ENUM_INIT: Atomic<E> = Atomic {
    inner: AtomicUsize::new(E::INIT),
    _marker: PhantomData,
};

impl<E: AtomicEnum> Atomic<E> {
    pub fn new(val: E) -> Self {
        // `sizeof(E)` must always be smaller than `sizeof(usize)` for safety.
        const_assert!(mem::size_of::<E>() <= mem::size_of::<usize>());
        Atomic {
            inner: AtomicUsize::new(val.to_usize()),
            _marker: PhantomData,
        }
    }

    pub fn get_mut(&mut self) -> MutInner<E> {
        MutInner {
            inner: self.inner.get_mut(),
            _marker: PhantomData,
        }
    }

    pub fn into_inner(self) -> E {
        E::from_usize(self.inner.into_inner())
    }

    pub fn load(&self, order: Ordering) -> E {
        E::from_usize(self.inner.load(order))
    }

    pub fn store(&self, val: E, order: Ordering) {
        self.inner.store(val.to_usize(), order)
    }

    pub fn compare_and_swap(&self, current: E, new: E, order: Ordering) -> E {
        let v = self.inner.compare_and_swap(current.to_usize(), new.to_usize(), order);
        E::from_usize(v)
    }

    pub fn compare_exchange(&self, current: E, new: E, success: Ordering, failure: Ordering) -> Result<E, E> {
        self.inner.compare_exchange(current.to_usize(), new.to_usize(), success, failure)
            .map(|v| E::from_usize(v))
            .map_err(|e| E::from_usize(e))
    }

    pub fn compare_exchange_weak(&self, current: E, new: E, success: Ordering, failure: Ordering) -> Result<E, E> {
        self.inner.compare_exchange_weak(current.to_usize(), new.to_usize(), success, failure)
            .map(|v| E::from_usize(v))
            .map_err(|e| E::from_usize(e))
    }
}

impl<E: Default + AtomicEnum> Default for Atomic<E> {
    fn default() -> Self {
        Atomic::new(Default::default())
    }
}

impl<E: fmt::Debug + AtomicEnum> fmt::Debug for Atomic<E> {
    fn fmt(&self, fmtr: &mut fmt::Formatter) -> fmt::Result {
        fmtr.debug_tuple("AtomicEnum")
            .field(&self.load(Ordering::SeqCst))
            .finish()
    }
}

impl<E: AtomicEnum> From<E> for Atomic<E> {
    fn from(v: E) -> Self {
        Self::new(v)
    }
}

/// A mutable reference to the inner enum type `E` of an `Atomic<E>`.
#[derive(Eq, Hash, PartialEq)]
pub struct MutInner<'a, E> {
    inner: &'a mut usize,
    _marker: PhantomData<E>,
}

impl<'a, E: PartialOrd> PartialOrd for MutInner<'a, E> {
    fn partial_cmp(&self, rhs: &Self) ->  Option<CmpOrdering> {
        let inner: &usize = self.inner;
        inner.partial_cmp(&*rhs.inner)
    }
}

impl<'a, E: Ord> Ord for MutInner<'a, E> {
    fn cmp(&self, rhs: &Self) -> CmpOrdering {
        let inner: &usize = self.inner;
        inner.cmp(&*rhs.inner)
    }
}

impl<'a, E: fmt::Debug> fmt::Debug for MutInner<'a, E> {
    fn fmt(&self, fmtr: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self.deref(), fmtr)
    }
}

impl<'a, E> Deref for MutInner<'a, E> {
    type Target = E;
    fn deref(&self) -> &Self::Target {
        let inner: &usize = self.inner;
        unsafe {
            mem::transmute::<&usize, &E>(inner)
        }
    }
}

impl<'a, E> DerefMut for MutInner<'a, E> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe {
            mem::transmute::<&mut usize, &mut E>(self.inner)
        }
    }
}

/// Any enum that needs to be atomic implements this trait. 
// TODO: replace with `collections::enum_set::CLike` when that stabilizes.
pub unsafe trait AtomicEnum {
    /// The const value to use 
    const INIT: usize;

    /// Convert from `usize` to self.
    fn from_usize(val: usize) -> Self;
    /// Convert from `Self` to usize.
    fn to_usize(self) -> usize;
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
