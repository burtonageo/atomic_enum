#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "nightly", feature(const_atomic_usize_new, const_fn, integer_atomics))]

// declared up here so that the `nightly_helpers` mod can access it.
macro_rules! impl_atomic_enum_repr {
    ($atomic_ty:ident, $base_ty:ty) => {
        impl ::AtomicEnumRepr for $atomic_ty {
            type BaseInteger = $base_ty;

            fn new(val: Self::BaseInteger) -> Self {
                $atomic_ty::new(val)
            }

            fn get_mut(&mut self) -> &mut Self::BaseInteger {
                $atomic_ty::get_mut(self)
            }

            fn into_inner(self) -> Self::BaseInteger {
                $atomic_ty::into_inner(self)
            }

            fn load(&self, ordering: Ordering) -> Self::BaseInteger {
                $atomic_ty::load(self, ordering)
            }

            fn store(&self, val: Self::BaseInteger, ordering: Ordering) {
                $atomic_ty::store(self, val, ordering)
            }

            fn swap(&self, val: Self::BaseInteger, ordering: Ordering) -> Self::BaseInteger {
                $atomic_ty::swap(self, val, ordering)
            }

            fn compare_and_swap(&self, current: Self::BaseInteger, new: Self::BaseInteger, ordering: Ordering) -> Self::BaseInteger {
                $atomic_ty::compare_and_swap(self, current, new, ordering)
            }

            fn compare_exchange(&self, current: Self::BaseInteger, new: Self::BaseInteger, success: Ordering, failure: Ordering) -> Result<Self::BaseInteger, Self::BaseInteger> {
                $atomic_ty::compare_exchange(self, current, new, success, failure)
            }

            fn compare_exchange_weak(&self, current: Self::BaseInteger, new: Self::BaseInteger, success: Ordering, failure: Ordering) -> Result<Self::BaseInteger, Self::BaseInteger> {
                $atomic_ty::compare_exchange_weak(self, current, new, success, failure)
            }
        }
    }
}

#[cfg(feature = "nightly")]
mod nightly_helpers;

#[cfg(feature = "std")]
extern crate core;

use core::cmp::{Eq, Ord, Ordering as CmpOrdering, PartialEq, PartialOrd};
use core::fmt;
use core::hash::{Hash, Hasher};
use core::mem;
use core::ops::{Deref, DerefMut};
use core::sync::atomic::{AtomicUsize, Ordering};

impl_atomic_enum_repr!(AtomicUsize, usize);

/// An enum type which can be safely shared between threads.
///
/// To allow your enum types to be placed into an `Atomic`, it is recommended that you use the `#[derive(AtomicEnum)]` attribute on them,
/// as shown below:
///
/// ```
/// #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd, Ord, AtomicEnum)]
/// #[repr(i32)]
/// pub enum MyEnum {
///     A,
///     B,
///     C,
/// }
/// ```
///
/// # Notes
///
/// On stable, the enum is backed by an `AtomicUsize`, so `assert_eq!(mem::size_of::<Atomic<EnumType>>(), mem::size_of::<usize>());`
/// will always be true, regardless of the size of `EnumType`.
///
/// On nightly, the enum will be backed by an atomic type that is closest to the underlying integer type of the enum. For example,
/// enums annotated with `#[repr(i8)]` will be backed by an `AtomicI8`.
pub struct Atomic<E: AtomicEnum> {
    inner: <E as AtomicEnum>::AtomicRepr,
}

/// Creates a constant `Atomic<E>`, initialized to the value specified in `E::INIT`.
///
/// Only available on nightly.
///
/// By default, this value will be the first variant of the enum annotated with `derive(AtomicEnum)`. To change this behavior, you can annotate
/// another variant with the `#[atomic_enum_init]` attribute, as shown below.
///
/// # Example
///
/// ```
/// # fn main() {
/// #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd, Ord, AtomicEnum)]
/// #[repr(isize)]
/// pub enum KeypadStatusCode {
///     OnFire = -1,
///     #[atomic_enum_init]
///     Operational = 0,
///     PasswordFileNotFound = 1,
///     KeyboardNotConnected = 2,
/// }
///
/// static MAIN_DOOR_KEYPAD_COMPUTER_STATUS: Atomic<KeypadStatusCode> = atomic_enum_new::<KeypadStatusCode>();
/// assert_eq!(MAIN_DOOR_KEYPAD_COMPUTER_STATUS.load(Ordering::SeqCst), KeypadStatusCode::Operational);
/// # }
/// ```
#[cfg(feature = "nightly")]
pub const fn atomic_enum_new<E: AtomicEnum>() -> Atomic<E> {
    Atomic {
        inner: <E as AtomicEnum>::INIT,
    }
}

impl<E: AtomicEnum> Atomic<E> {
    /// Create a new `Atomic<E>` from the enum value passed in.
    ///
    /// # Example
    ///
    /// ```
    /// # fn main() {
    /// #[repr(i32)]
    /// #[derive(Copy, Clone, Eq, Hash, PartialEq, PartialOrd, AtomicEnum)]
    /// pub enum SomeEnum {
    ///     A,
    ///     B,
    ///     C,
    /// }
    ///
    /// let atomic_enum = Atomic::new(SomeEnum::A);
    ///
    /// # }
    /// ```
    pub fn new(val: E) -> Self {
        Atomic {
            inner: <E as AtomicEnum>::AtomicRepr::new(val.to_underlying()),
        }
    }

    /// Returns a mutable reference to the underlying enum.
    ///
    /// This is safe because the mutable reference guarantees that no other threads are concurrently accessing the atomic data.
    ///
    /// # Example
    ///
    /// ```
    /// # fn main() {
    /// #[repr(i32)]
    /// #[derive(Copy, Clone, Eq, Hash, PartialEq, PartialOrd, AtomicEnum)]
    /// pub enum SomeEnum {
    ///     A,
    ///     B,
    ///     C,
    /// }
    ///
    /// let atomic_enum = Atomic::new(SomeEnum::A);
    /// assert_eq!(*atomic_enum.get_mut(), SomeEnum::A);
    /// *atomic_enum.get_mut() = SomeEnum::C;
    /// assert_eq!(atomic_enum.into_inner(), SomeEnum::C);
    ///
    /// # }
    /// ```
    pub fn get_mut(&mut self) -> Mut<E> {
        Mut {
            inner: self.inner.get_mut(),
        }
    }

    /// Consumes the atomic and returns the contained value.
    ///
    /// This is safe because passing self by value guarantees that no other threads are concurrently accessing the atomic data.
    ///
    /// # Example
    ///
    /// ```
    /// # fn main() {
    /// #[repr(i32)]
    /// #[derive(Copy, Clone, Eq, Hash, PartialEq, PartialOrd, AtomicEnum)]
    /// pub enum SomeEnum {
    ///     A,
    ///     B,
    ///     C,
    /// }
    ///
    /// let atomic_enum = Atomic::new(SomeEnum::A);
    /// assert_eq!(atomic_enum.into_inner(), SomeEnum::A);
    ///
    /// # }
    /// ```
    pub fn into_inner(self) -> E {
        E::from_underlying(self.inner.into_inner())
    }


    /// Loads a value from the atomic enum.
    ///
    /// `load` takes an `Ordering` argument which describes the memory ordering of this operation.
    ///
    /// # Panics
    ///
    /// Panics if `order` is `Release` or `AcqRel`.
    pub fn load(&self, order: Ordering) -> E {
        E::from_underlying(self.inner.load(order))
    }

    /// Stores a value into the atomic enum.
    ///
    /// `store` takes an `Ordering` argument which describes the memory ordering of this operation.
    ///
    /// # Panics
    ///
    /// Panics if `order` is `Acquire` or `AcqRel`.
    pub fn store(&self, val: E, order: Ordering) {
        self.inner.store(val.to_underlying(), order)
    }

    /// Stores a value into the atomic enum, returning the previous value.
    ///
    /// `swap` takes an `Ordering` argument which describes the memory ordering of this operation.
    pub fn swap(&self, val: E, order: Ordering) -> E {
        E::from_underlying(self.inner.swap(val.to_underlying(), order))
    }

    /// Stores a value into the atomic enum if the `current` value is the same as the current value.
    ///
    /// The return value is always the previous value. If it is equal to `current`, then the value was updated.
    ///
    /// `compare_and_swap` also takes an `Ordering` argument which describes the memory ordering of this operation.
    pub fn compare_and_swap(&self, current: E, new: E, order: Ordering) -> E
    where
        E: Eq + PartialEq,
    {
        let v = self.inner.compare_and_swap(current.to_underlying(), new.to_underlying(), order);
        E::from_underlying(v)
    }

    /// Stores a value into the atomic integer if the current value is the same as the current value.
    ///
    /// The return value is a result indicating whether the new value was written and containing the previous value.
    /// On success this value is guaranteed to be equal to `current`.
    ///
    /// `compare_exchange` takes two `Ordering` arguments to describe the memory ordering of this operation. The first
    /// describes the required ordering if the operation succeeds while the second describes the required ordering when
    /// the operation fails. The failure ordering can't be `Release` or `AcqRel` and must be equivalent or weaker than
    /// the success ordering.
    pub fn compare_exchange(&self, current: E, new: E, success: Ordering, failure: Ordering) -> Result<E, E>
    where
        E: Eq + PartialEq,
    {
        self.inner.compare_exchange(current.to_underlying(), new.to_underlying(), success, failure)
            .map(|v| E::from_underlying(v))
            .map_err(|e| E::from_underlying(e))
    }

    /// Stores a value into the atomic enum if the current value is the same as the current value.
    ///
    /// Unlike `compare_exchange`, this function is allowed to spuriously fail even when the comparison
    /// succeeds, which can result in more efficient code on some platforms. The return value is a result
    /// indicating whether the new value was written and containing the previous value.
    ///
    /// `compare_exchange_weak` takes two `Ordering` arguments to describe the memory ordering of this operation.
    /// The first describes the required ordering if the operation succeeds while the second describes the required
    /// ordering when the operation fails. The failure ordering can't be `Release` or `AcqRel` and must be equivalent
    /// or weaker than the success ordering.
    pub fn compare_exchange_weak(&self, current: E, new: E, success: Ordering, failure: Ordering) -> Result<E, E>
    where
        E: Eq + PartialEq,
    {
        self.inner.compare_exchange_weak(current.to_underlying(), new.to_underlying(), success, failure)
            .map(|v| E::from_underlying(v))
            .map_err(|e| E::from_underlying(e))
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

#[cfg(feature = "std")]
impl<E: AtomicEnum> std::panic::RefUnwindSafe for Atomic<E>
where
    <E as AtomicEnum>::AtomicRepr: std::panic::RefUnwindSafe
{
}

/// A mutable reference to the inner enum type `E` of an `Atomic<E>`.
///
/// Created by calling `get_mut()` on an `Atomic<E>`.
pub struct Mut<'a, E: AtomicEnum>
where
    <E as AtomicEnum>::UnderlyingRepr: 'a,
{
    inner: &'a mut <E as AtomicEnum>::UnderlyingRepr,
}

impl<'a, E: AtomicEnum> Deref for Mut<'a, E> {
    type Target = E;
    fn deref(&self) -> &Self::Target {
        let inner: &<E as AtomicEnum>::UnderlyingRepr = self.inner;
        unsafe {
            mem::transmute::<&<E as AtomicEnum>::UnderlyingRepr, &E>(inner)
        }
    }
}

impl<'a, E: AtomicEnum> DerefMut for Mut<'a, E> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe {
            mem::transmute::<&mut <E as AtomicEnum>::UnderlyingRepr, &mut E>(self.inner)
        }
    }
}

impl<'a, E: AtomicEnum + fmt::Debug> fmt::Debug for Mut<'a, E> {
    fn fmt(&self, fmtr: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self.deref(), fmtr)
    }
}

impl<'a, E> Hash for Mut<'a, E>
where
    E: AtomicEnum + Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.deref().hash(state);
    }
}

impl<'a, E> PartialEq for Mut<'a, E>
where
    E: AtomicEnum + PartialEq,
{
    fn eq(&self, rhs: &Self) -> bool {
        self.deref().eq(rhs.deref())
    }
}

impl<'a, E> Eq for Mut<'a, E>
where
    E: AtomicEnum + PartialEq + Eq,
{
}

impl<'a, E> PartialOrd for Mut<'a, E>
where
    E: AtomicEnum + PartialEq + PartialOrd,
{
    fn partial_cmp(&self, rhs: &Self) ->  Option<CmpOrdering> {
        self.deref().partial_cmp(rhs.deref())
    }
}

impl<'a, E> Ord for Mut<'a, E>
where
    E: AtomicEnum + Eq + PartialEq + PartialOrd + Ord,
{
    fn cmp(&self, rhs: &Self) -> CmpOrdering {
        self.deref().cmp(rhs.deref())
    }
}

/// Any enum that can be placed into an `Atomic<E>` needs to implement this trait.
///
/// # Note
///
/// Note this trait is unsafe because `INIT` must be set to a value that is a valid variant
/// of the enum type this is implemented for.
pub unsafe trait AtomicEnum {
    /// The underlying repr, e.g. for the following enum, this should be `i32`.
    ///
    /// ```
    /// #[repr(i32)]
    /// #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    /// pub enum SomeEnum {
    ///     A,
    ///     B,
    ///     C,
    /// }
    /// ```
    type UnderlyingRepr: Copy + Clone;
    /// The atomic type used to represent this enum.
    ///
    /// # Notes
    ///
    /// On stable and beta, this will always be `AtomicUsize`.
    ///
    /// If the `nightly` feature is enabled, this will be the type which most closely matches `UnderlyingRepr`,
    /// e.g. for `i32`, this would be `AtomicI32`.
    type AtomicRepr: AtomicEnumRepr<BaseInteger = Self::UnderlyingRepr>;

    /// The value that should be used when creating `ATOMIC_ENUM_INIT`.
    #[cfg(feature = "nightly")]
    const INIT: Self::AtomicRepr;

    /// Convert from `UnderlyingRepr` to `Self`.
    fn from_underlying(_: Self::UnderlyingRepr) -> Self;
    /// Convert from `self` to `UnderlyingRepr`.
    fn to_underlying(self) -> Self::UnderlyingRepr;
}

/// The underlying `Atomic` type that backs an `Atomic<_>`.
pub trait AtomicEnumRepr {
    /// The base integer type (e.g. for `AtomicU8`, this will be `u8`).
    type BaseInteger: Clone + Copy;

    /// Create a new `AtomicEnumRepr` from `val`.
    fn new(val: Self::BaseInteger) -> Self;
    /// Corresponds to `Atomic::get_mut`.
    fn get_mut(&mut self) -> &mut Self::BaseInteger;
    /// Corresponds to `Atomic::into_inner`.
    fn into_inner(self) -> Self::BaseInteger;
    /// Corresponds to `Atomic::load`.
    fn load(&self, order: Ordering) -> Self::BaseInteger;
    /// Corresponds to `Atomic::store`.
    fn store(&self, val: Self::BaseInteger, order: Ordering);
    fn swap(&self, val: Self::BaseInteger, order: Ordering) -> Self::BaseInteger;
    fn compare_and_swap(&self, current: Self::BaseInteger, new: Self::BaseInteger, order: Ordering) -> Self::BaseInteger;
    fn compare_exchange(&self, current: Self::BaseInteger, new: Self::BaseInteger, success: Ordering, failure: Ordering) -> Result<Self::BaseInteger, Self::BaseInteger>;
    fn compare_exchange_weak(&self, current: Self::BaseInteger, new: Self::BaseInteger, success: Ordering, failure: Ordering) -> Result<Self::BaseInteger, Self::BaseInteger>;
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
