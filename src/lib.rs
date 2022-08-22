//! Defines a set of primitives which make it easier to write robust unsafe code
//! that deals with type-erased values. This crate is only useful in situations
//! where the type can be determined from context -- type information is not stored.
//!
//! If you want safe, fallible type erasure, just use `Box<dyn Any>` from `std`.

use std::{mem::ManuallyDrop, ptr::NonNull};

/// A type-erased version of [`Box`], which only uses dynamic dispatch for the [`Drop`] impl.
/// This type is essentially a wide pointer (16 bytes) -- 1 pointer for the data,
/// and 1 pointer for the drop handling code.
///
/// If you never intending on dropping this type, [`LeakyBox`] is a more efficient alternative,
/// as it is only 1 pointer wide (8 bytes).
pub struct ErasedBox {
    /// INVARIANT: This field contains values of type `T`, where `T` corresponds to the type argument
    /// used with `Self::from_box` or `Self::new`. `T` is unknown at runtime.
    inner: ManuallyDrop<LeakyBox>,
    /// SAFETY: The `LeakyBox` passed to this fn pointer must be the one contained in `self.inner`.
    drop: unsafe fn(LeakyBox),
}

impl ErasedBox {
    pub const fn from_box<T: 'static>(boxed: Box<T>) -> Self {
        Self {
            inner: ManuallyDrop::new(LeakyBox::from_box(boxed)),
            drop: |inner| unsafe {
                // SAFETY: We can confidently downcast `inner` to type `T`,
                // since we just created it from a value of type `T`.
                std::mem::drop(inner.downcast::<T>());
            },
        }
    }
    pub fn new<T: 'static>(val: T) -> Self {
        Self::from_box(Box::new(val))
    }

    /// # Safety
    /// This instance must have been created from a value of type `T`.
    pub unsafe fn downcast<T: 'static>(self) -> Box<T> {
        // SAFETY: The caller has promised that the invariants of `LeakyBox::downcast` are upheld.
        LeakyBox::from(self).downcast()
    }

    /// # Safety
    /// This instance must have been created from a value of type `T`.
    pub unsafe fn downcast_ref<T: 'static>(&self) -> &T {
        // SAFETY: The caller has promised that the invariants of `LeakyBox::downcast_ref` are upheld.
        self.inner.downcast_ref()
    }

    /// # Safety
    /// This instance must have been created from a value of type `T`.
    pub unsafe fn downcast_mut<T: 'static>(&mut self) -> &mut T {
        // SAFETY: The caller has promised that the invariants of `LeakyBox::downcast_mut` are upheld.
        self.inner.downcast_mut()
    }
}

impl Drop for ErasedBox {
    #[inline]
    fn drop(&mut self) {
        // Move the `LeakyBox` out of this instance.
        // SAFETY: The compiler will prevent `self` from ever being used again,
        // so it's okay to leave the ManuallyDrop field in an invalid state.
        let inner = unsafe { ManuallyDrop::take(&mut self.inner) };
        // SAFETY: `inner` was obtained from the same instance of `ErasedBox` as the drop fn pointer.
        unsafe { (self.drop)(inner) };
    }
}

impl From<ErasedBox> for LeakyBox {
    #[inline]
    fn from(boxed: ErasedBox) -> Self {
        // Make sure the `ErasedBox` doesn't have its destructor called.
        let mut boxed = ManuallyDrop::new(boxed);
        // SAFETY: `boxed` will go out of scope after this call, and can never be used again.
        unsafe { ManuallyDrop::take(&mut boxed.inner) }
    }
}

/// A type-erased version of [`Box`], which uses no dynamic dispatch and is 1 pointer wide.
///
/// If this type is allowed to go out of scope, the value will be forgotten and the allocation will be leaked.
/// To avoid leaking, this type should be [downcasted](#method.downcast) to a concrete type
/// before it is allowed to go out of scope.
///
/// If you need a droppable type-erased box, consider using [`ErasedBox`].
pub struct LeakyBox {
    ptr: NonNull<u8>,
}

impl LeakyBox {
    pub const fn from_box<T: 'static>(boxed: Box<T>) -> Self {
        let ptr = &*boxed as *const T as *mut u8;
        std::mem::forget(boxed);
        // SAFETY: `ptr` was obtained from a `Box`, so it is guaranteed to be non-null.
        let ptr = unsafe { NonNull::new_unchecked(ptr) };
        Self { ptr }
    }
    pub fn new<T: 'static>(val: T) -> Self {
        Self::from_box(Box::new(val))
    }

    /// # Safety
    /// This instance must have been created from a value of type `T`.
    pub unsafe fn downcast<T: 'static>(self) -> Box<T> {
        // SAFETY: `self.ptr` was originally obtained from `Box`,
        // and the caller has promised that the type matches.
        Box::from_raw(self.ptr.as_ptr() as *mut T)
    }

    /// # Safety
    /// This instance must have been created from a value of type `T`.
    pub unsafe fn downcast_ref<T: 'static>(&self) -> &T {
        &*(self.ptr.as_ptr() as *mut T)
    }

    /// # Safety
    /// This instance must have been created from a value of type `T`.
    pub unsafe fn downcast_mut<T: 'static>(&mut self) -> &mut T {
        &mut *(self.ptr.as_ptr() as *mut T)
    }
}

impl Drop for LeakyBox {
    fn drop(&mut self) {
        // No-op drop impl for future-proofing.
        // We'll never be able to run the destructor on the wrapped type,
        // but we may be able to clean up the allocation someday.
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn assert_sizes() {
        assert_eq!(std::mem::size_of::<ErasedBox>(), 16);
        assert_eq!(std::mem::size_of::<LeakyBox>(), 8);
    }
}
