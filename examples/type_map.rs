use std::{any::TypeId, collections::HashMap};

use erased_box::ErasedBox;

fn main() {
    let mut type_map = TypeMap::default();

    // Insert a complex type into the map.
    type_map.insert(vec!["Hello"]);
    // Retrieve that type.
    assert_eq!(type_map.get::<Vec<&str>>(), Some(&vec!["Hello"]));
    // Modify it.
    let vec = type_map.get_mut::<Vec<&str>>().unwrap();
    vec.push("World!");
    // Retrieve it again.
    assert_eq!(type_map.get::<Vec<&str>>(), Some(&vec!["Hello", "World!"]));
}

/// A container that stores heterogenous values, keyed by their types.
#[derive(Default)]
pub struct TypeMap(
    // INVARIANT: The type erased by `ErasedBox` is the same type identified by the `TypeId`.
    HashMap<TypeId, ErasedBox>,
);

impl TypeMap {
    pub fn insert<T: 'static>(&mut self, val: T) -> Option<T> {
        let old = self.0.insert(TypeId::of::<T>(), ErasedBox::new(val))?;
        // SAFETY: The old value was keyed with the TypeId of `T`,
        // so we can safely downcast it back to its original type.
        Some(unsafe { *old.downcast::<T>() })
    }

    pub fn get<T: 'static>(&self) -> Option<&T> {
        let val = self.0.get(&TypeId::of::<T>())?;
        // SAFETY: The value was keyed with the TypeId of `T`,
        // so we can safely downcast it back to its original type.
        Some(unsafe { val.downcast_ref::<T>() })
    }

    pub fn get_mut<T: 'static>(&mut self) -> Option<&mut T> {
        let val = self.0.get_mut(&TypeId::of::<T>())?;
        // SAFETY: The value was keyed with the TypeId of `T`,
        // so we can safely downcast it back to its original type.
        Some(unsafe { val.downcast_mut::<T>() })
    }
}
