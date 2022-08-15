use std::ptr::NonNull;

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
    pub unsafe fn downcast_unchecked<T: 'static>(self) -> Box<T> {
        // SAFETY: `self.ptr` was originally obtained from `Box::into_raw`,
        // and the caller has promised that the type matches.
        Box::from_raw(self.ptr.as_ptr() as *mut T)
    }

    /// # Safety
    /// This instance must have been created from a value of type `T`.
    pub unsafe fn downcast_ref_unchecked<T: 'static>(&self) -> &T {
        &*(self.ptr.as_ptr() as *mut T)
    }

    /// # Safety
    /// This instance must have been created from a value of type `T`.
    pub unsafe fn downcast_mut_unchecked<T: 'static>(&mut self) -> &mut T {
        &mut *(self.ptr.as_ptr() as *mut T)
    }
}

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
    pub unsafe fn downcast_unchecked<T: 'static>(self) -> Box<T> {
        // SAFETY: `self.ptr` was originally obtained from `Box::into_raw`,
        // and the caller has promised that the type matches.
        Box::from_raw(self.ptr.as_ptr() as *mut T)
    }

    /// # Safety
    /// This instance must have been created from a value of type `T`.
    pub unsafe fn downcast_ref_unchecked<T: 'static>(&self) -> &T {
        &*(self.ptr.as_ptr() as *mut T)
    }

    /// # Safety
    /// This instance must have been created from a value of type `T`.
    pub unsafe fn downcast_mut_unchecked<T: 'static>(&mut self) -> &mut T {
        &mut *(self.ptr.as_ptr() as *mut T)
    }
}

#[cfg(test)]
mod tests {}
