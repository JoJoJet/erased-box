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
/// If you do not need to reuse allocations, consider using [`SlimBox`],
/// which is only 1 pointer wide (8 bytes).
///
/// If you never intend on dropping this type, [`LeakyBox`] does not use dynamic dispatch,
/// is only 1 pointer wide, and allows reusing allocations (converting to/from `Box<>`).
pub struct ErasedBox {
    /// INVARIANT: This field contains values of type `T`, where `T` corresponds to the type argument
    /// used with `Self::from_box` or `Self::new`. `T` is unknown at runtime.
    inner: ManuallyDrop<LeakyBox>,
    /// SAFETY: The `LeakyBox` passed to this fn pointer must be the one contained in `self.inner`.
    drop: unsafe fn(LeakyBox),
}

impl ErasedBox {
    pub fn from_box<T: 'static>(boxed: Box<T>) -> Self {
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

/// A type-erased version of [`Box`], which only uses dynamic dispatch for the [`Drop`] impl
/// and is only 1 pointer wide (8 bytes).
///
/// If you need to reuse allocations, consider using [`ErasedBox`]. This type allows converting
/// to/from `Box<>`, but it is 2 pointers wide (8 bytes).
///
/// If you never intend on dropping this type, [`LeakyBox`] does not have any `Drop`-associated overhead
/// and is only 1 pointer wide.
pub struct SlimBox {
    /// This points to values of type `SlimBoxImpl<T>`, for an unknown T.
    inner: ManuallyDrop<LeakyBox>,
}

#[repr(C)]
struct SlimBoxImpl<T> {
    /// SAFETY: The passed `LeakyBox` must point to the `SlimBoxImpl` instance that contains this fn pointer.
    drop: unsafe fn(LeakyBox),
    val: T,
}

impl SlimBox {
    pub fn new<T: 'static>(val: T) -> Self {
        let inner = SlimBoxImpl {
            val,
            drop: |inner| unsafe {
                // Downcast the type-erased value back to its concrete type, then drop it.
                std::mem::drop(inner.downcast::<SlimBoxImpl<T>>());
            },
        };
        Self {
            inner: ManuallyDrop::new(LeakyBox::new(inner)),
        }
    }

    /// # Safety
    /// This instance must have been created from a value of type `T`.
    pub unsafe fn downcast<T: 'static>(mut self) -> T {
        // SAFETY: `self` will not get dropped, so it's okay to leave `self.inner` uninitialized.
        let inner = ManuallyDrop::take(&mut self.inner);
        std::mem::forget(self);
        let SlimBoxImpl::<T> { val, .. } = *inner.downcast();
        val
    }

    /// # Safety
    /// This instance must have been created from a value of type `T`.
    pub unsafe fn downcast_ref<T: 'static>(&self) -> &T {
        let SlimBoxImpl::<T> { val, .. } = self.inner.downcast_ref();
        val
    }

    /// # Safety
    /// This instance must have been created from a value of type `T`.
    pub unsafe fn downcast_mut<T: 'static>(&mut self) -> &mut T {
        let SlimBoxImpl::<T> { val, .. } = self.inner.downcast_mut();
        val
    }
}

impl Drop for SlimBox {
    #[inline]
    fn drop(&mut self) {
        // SAFETY: The compiler will guarantee that nothing can observe `self` after this fn returns,
        // so it is okay to leave `self.inner` in an uninitialized state.
        let inner = unsafe { ManuallyDrop::take(&mut self.inner) };
        // SAFETY: `inner` points to an instance of `SlimBoxImpl<T>`, for an unknown T.
        // Since all `SlimBoxImpl` monomorphizations are `repr(C)`, that means a reference to
        // a `SlimBoxImpl` can be cast to a reference to its first field.
        // Its first field is a fn pointer to the drop code, so let's downcast to that type.
        let drop: unsafe fn(LeakyBox) = unsafe { *inner.downcast_ref() };
        // SAFETY: The `drop` fn pointer expects to be passed the `SlimBoxImpl` that contains it, which we do.
        unsafe { drop(inner) };
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
    pub fn from_box<T: 'static>(boxed: Box<T>) -> Self {
        let mut boxed = ManuallyDrop::new(boxed);
        let ptr = &mut **boxed as *mut T as *mut u8;
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
        assert_eq!(std::mem::size_of::<SlimBox>(), 8);
        assert_eq!(std::mem::size_of::<LeakyBox>(), 8);
    }
}
