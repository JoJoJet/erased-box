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
    ptr: NonNull<u8>,
    drop: fn(*mut u8),
}

impl<T: 'static> From<Box<T>> for ErasedBox {
    fn from(boxed: Box<T>) -> Self {
        let ptr = Box::into_raw(boxed) as *mut u8;
        Self {
            // SAFETY: `ptr` was obtained from a `Box`, so it is guaranteed to be non-null.
            ptr: unsafe { NonNull::new_unchecked(ptr) },
            drop: |ptr| {
                // SAFETY: We can call `Box::from_raw`, since `ptr` was originally obtained from `Box<T>::into_raw`.
                // This closure will only get called in the `Drop` impl, which gets called at most once.
                let boxed = unsafe { Box::from_raw(ptr as *mut T) };
                std::mem::drop(boxed);
            },
        }
    }
}

impl Drop for ErasedBox {
    #[inline]
    fn drop(&mut self) {
        (self.drop)(self.ptr.as_ptr());
    }
}

impl ErasedBox {
    pub fn new<T: 'static>(val: T) -> Self {
        Self::from(Box::new(val))
    }

    /// # Safety
    /// This instance must have been created from a value of type `T`.
    pub unsafe fn downcast<T: 'static>(self) -> Box<T> {
        // Make sure the drop handler doesn't get called at the end of this fn.
        let ptr = ManuallyDrop::new(self).ptr.as_ptr();
        // SAFETY: `ptr` was originally obtained from `Box::into_raw`,
        // and the caller has promised that the type matches.
        Box::from_raw(ptr as *mut T)
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

impl<T: 'static> From<Box<T>> for LeakyBox {
    fn from(boxed: Box<T>) -> Self {
        let ptr = Box::into_raw(boxed) as *mut u8;
        Self {
            // SAFETY: `ptr` was obtained from a `Box`, so it is guaranteed to be non-null.
            ptr: unsafe { NonNull::new_unchecked(ptr) },
        }
    }
}

impl LeakyBox {
    pub fn new<T: 'static>(val: T) -> Self {
        Self::from(Box::new(val))
    }

    /// # Safety
    /// This instance must have been created from a value of type `T`.
    pub unsafe fn downcast<T: 'static>(self) -> Box<T> {
        // SAFETY: `self.ptr` was originally obtained from `Box::into_raw`,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn assert_sizes() {
        assert_eq!(std::mem::size_of::<ErasedBox>(), 16);
        assert_eq!(std::mem::size_of::<LeakyBox>(), 8);
    }
}
