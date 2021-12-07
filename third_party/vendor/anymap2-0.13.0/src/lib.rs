//! This crate provides the `AnyMap` type, a safe and convenient store for one
//! value of each type.

#![warn(missing_docs, unused_results)]
#![allow(unused_doc_comments)]

//#![deny(warnings)]
use std::{any::TypeId, marker::PhantomData};

use crate::{
    any::{Any, IntoBox, UncheckedAnyExt},
    raw::RawMap,
};

macro_rules! impl_common_methods {
    (
        field: $t:ident.$field:ident;
        new() => $new:expr;
        with_capacity($with_capacity_arg:ident) => $with_capacity:expr;
    ) => {
        impl<A: ?Sized + UncheckedAnyExt> $t<A> {
            /// Create an empty collection.
            #[inline]
            pub fn new() -> $t<A> {
                $t { $field: $new }
            }

            /// Creates an empty collection with the given initial capacity.
            #[inline]
            pub fn with_capacity($with_capacity_arg: usize) -> $t<A> {
                $t {
                    $field: $with_capacity,
                }
            }

            /// Returns the number of elements the collection can hold without
            /// reallocating.
            #[inline]
            pub fn capacity(&self) -> usize {
                self.$field.capacity()
            }

            /// Reserves capacity for at least `additional` more elements to be inserted
            /// in the collection. The collection may reserve more space to avoid
            /// frequent reallocations.
            ///
            /// # Panics
            ///
            /// Panics if the new allocation size overflows `usize`.
            #[inline]
            pub fn reserve(&mut self, additional: usize) {
                self.$field.reserve(additional)
            }

            /// Shrinks the capacity of the collection as much as possible. It will drop
            /// down as much as possible while maintaining the internal rules
            /// and possibly leaving some space in accordance with the resize policy.
            #[inline]
            pub fn shrink_to_fit(&mut self) {
                self.$field.shrink_to_fit()
            }

            /// Returns the number of items in the collection.
            #[inline]
            pub fn len(&self) -> usize {
                self.$field.len()
            }

            /// Returns true if there are no items in the collection.
            #[inline]
            pub fn is_empty(&self) -> bool {
                self.$field.is_empty()
            }

            /// Removes all items from the collection. Keeps the allocated memory for
            /// reuse.
            #[inline]
            pub fn clear(&mut self) {
                self.$field.clear()
            }
        }

        impl<A: ?Sized + UncheckedAnyExt> Default for $t<A> {
            #[inline]
            fn default() -> $t<A> {
                $t::new()
            }
        }
    };
}

pub mod any;
pub mod raw;

/// A collection containing zero or one values for any given type and allowing
/// convenient, type-safe access to those values.
///
/// The type parameter `A` allows you to use a different value type; normally
/// you will want it to be `anymap::any::Any`, but there are other choices:
///
/// - If you want the entire map to be cloneable, use `CloneAny` instead of
///   `Any`.
/// - You can add on `+ Send` and/or `+ Sync` (e.g. `Map<Any + Send>`) to add
///   those bounds.
///
/// ```rust
/// # use anymap2::AnyMap;
/// let mut data = AnyMap::new();
/// assert_eq!(data.get(), None::<&i32>);
/// data.insert(42i32);
/// assert_eq!(data.get(), Some(&42i32));
/// data.remove::<i32>();
/// assert_eq!(data.get::<i32>(), None);
///
/// #[derive(Clone, PartialEq, Debug)]
/// struct Foo {
///     str: String,
/// }
///
/// assert_eq!(data.get::<Foo>(), None);
/// data.insert(Foo {
///     str: format!("foo"),
/// });
/// assert_eq!(
///     data.get(),
///     Some(&Foo {
///         str: format!("foo")
///     })
/// );
/// data.get_mut::<Foo>().map(|foo| foo.str.push('t'));
/// assert_eq!(&*data.get::<Foo>().unwrap().str, "foot");
/// ```
///
/// Values containing non-static references are not permitted.
#[derive(Debug)]
pub struct Map<A: ?Sized + UncheckedAnyExt = dyn Any> {
    raw: RawMap<A>,
}

// #[derive(Clone)] would want A to implement Clone, but in reality it’s only
// Box<A> that can.
impl<A: ?Sized + UncheckedAnyExt> Clone for Map<A>
where
    Box<A>: Clone,
{
    #[inline]
    fn clone(&self) -> Map<A> {
        Map {
            raw: self.raw.clone(),
        }
    }
}

/// The most common type of `Map`: just using `Any`.
///
/// Why is this a separate type alias rather than a default value for `Map<A>`?
/// `Map::new()` doesn’t seem to be happy to infer that it should go with the
/// default value. It’s a bit sad, really. Ah well, I guess this approach will
/// do.
pub type AnyMap = Map<dyn Any>;

/// Sync version
pub type SendSyncAnyMap = Map<dyn Any + Send + Sync>;

impl_common_methods! {
    field: Map.raw;
    new() => RawMap::new();
    with_capacity(capacity) => RawMap::with_capacity(capacity);
}

impl<A: ?Sized + UncheckedAnyExt> Map<A> {
    /// Returns a reference to the value stored in the collection for the type
    /// `T`, if it exists.
    #[inline]
    pub fn get<T: IntoBox<A>>(&self) -> Option<&T> {
        self.raw
            .get(&TypeId::of::<T>())
            .map(|any| unsafe { any.downcast_ref_unchecked::<T>() })
    }

    /// Returns a mutable reference to the value stored in the collection for
    /// the type `T`, if it exists.
    #[inline]
    pub fn get_mut<T: IntoBox<A>>(&mut self) -> Option<&mut T> {
        self.raw
            .get_mut(&TypeId::of::<T>())
            .map(|any| unsafe { any.downcast_mut_unchecked::<T>() })
    }

    /// Sets the value stored in the collection for the type `T`.
    /// If the collection already had a value of type `T`, that value is
    /// returned. Otherwise, `None` is returned.
    #[inline]
    pub fn insert<T: IntoBox<A>>(&mut self, value: T) -> Option<T> {
        unsafe {
            self.raw
                .insert(TypeId::of::<T>(), value.into_box())
                .map(|any| *any.downcast_unchecked::<T>())
        }
    }

    /// Removes the `T` value from the collection,
    /// returning it if there was one or `None` if there was not.
    #[inline]
    pub fn remove<T: IntoBox<A>>(&mut self) -> Option<T> {
        self.raw
            .remove(&TypeId::of::<T>())
            .map(|any| *unsafe { any.downcast_unchecked::<T>() })
    }

    /// Returns true if the collection contains a value of type `T`.
    #[inline]
    pub fn contains<T: IntoBox<A>>(&self) -> bool {
        self.raw.contains_key(&TypeId::of::<T>())
    }

    /// Gets the entry for the given type in the collection for in-place
    /// manipulation
    #[inline]
    pub fn entry<T: IntoBox<A>>(&mut self) -> Entry<A, T> {
        match self.raw.entry(TypeId::of::<T>()) {
            raw::Entry::Occupied(e) => Entry::Occupied(OccupiedEntry {
                inner: e,
                type_: PhantomData,
            }),
            raw::Entry::Vacant(e) => Entry::Vacant(VacantEntry {
                inner: e,
                type_: PhantomData,
            }),
        }
    }
}

impl<A: ?Sized + UncheckedAnyExt> AsRef<RawMap<A>> for Map<A> {
    #[inline]
    fn as_ref(&self) -> &RawMap<A> {
        &self.raw
    }
}

impl<A: ?Sized + UncheckedAnyExt> AsMut<RawMap<A>> for Map<A> {
    #[inline]
    fn as_mut(&mut self) -> &mut RawMap<A> {
        &mut self.raw
    }
}

impl<A: ?Sized + UncheckedAnyExt> From<Map<A>> for RawMap<A> {
    #[inline]
    fn from(map: Map<A>) -> Self {
        map.raw
    }
}

/// A view into a single occupied location in an `Map`.
pub struct OccupiedEntry<'a, A: ?Sized + UncheckedAnyExt, V: 'a> {
    inner: raw::OccupiedEntry<'a, A>,
    type_: PhantomData<V>,
}

/// A view into a single empty location in an `Map`.
pub struct VacantEntry<'a, A: ?Sized + UncheckedAnyExt, V: 'a> {
    inner: raw::VacantEntry<'a, A>,
    type_: PhantomData<V>,
}

/// A view into a single location in an `Map`, which may be vacant or occupied.
pub enum Entry<'a, A: ?Sized + UncheckedAnyExt, V: 'a> {
    /// An occupied Entry
    Occupied(OccupiedEntry<'a, A, V>),
    /// A vacant Entry
    Vacant(VacantEntry<'a, A, V>),
}

impl<'a, A: ?Sized + UncheckedAnyExt, V: IntoBox<A>> Entry<'a, A, V> {
    /// Ensures a value is in the entry by inserting the default if empty, and
    /// returns a mutable reference to the value in the entry.
    #[inline]
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(inner) => inner.into_mut(),
            Entry::Vacant(inner) => inner.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default
    /// function if empty, and returns a mutable reference to the value in
    /// the entry.
    #[inline]
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(inner) => inner.into_mut(),
            Entry::Vacant(inner) => inner.insert(default()),
        }
    }
}

impl<'a, A: ?Sized + UncheckedAnyExt, V: Default + IntoBox<A>> Entry<'a, A, V> {
    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # use anymap2::AnyMap;
    /// let mut data = AnyMap::new();
    /// {
    ///     let r = data.entry::<i32>().or_default();
    ///     assert_eq!(r, &mut 0);
    ///     *r = 1;
    /// }
    /// assert_eq!(data.get(), Some(&1));
    /// assert_eq!(data.entry::<i32>().or_default(), &mut 1);
    /// ```
    pub fn or_default(self) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(Default::default()),
        }
    }
}

impl<'a, A: ?Sized + UncheckedAnyExt, V: IntoBox<A>> OccupiedEntry<'a, A, V> {
    /// Gets a reference to the value in the entry
    #[inline]
    pub fn get(&self) -> &V {
        unsafe { self.inner.get().downcast_ref_unchecked() }
    }

    /// Gets a mutable reference to the value in the entry
    #[inline]
    pub fn get_mut(&mut self) -> &mut V {
        unsafe { self.inner.get_mut().downcast_mut_unchecked() }
    }

    /// Converts the OccupiedEntry into a mutable reference to the value in the
    /// entry with a lifetime bound to the collection itself
    #[inline]
    pub fn into_mut(self) -> &'a mut V {
        unsafe { self.inner.into_mut().downcast_mut_unchecked() }
    }

    /// Sets the value of the entry, and returns the entry's old value
    #[inline]
    pub fn insert(&mut self, value: V) -> V {
        unsafe { *self.inner.insert(value.into_box()).downcast_unchecked() }
    }

    /// Takes the value out of the entry, and returns it
    #[inline]
    pub fn remove(self) -> V {
        unsafe { *self.inner.remove().downcast_unchecked() }
    }
}

impl<'a, A: ?Sized + UncheckedAnyExt, V: IntoBox<A>> VacantEntry<'a, A, V> {
    /// Sets the value of the entry with the VacantEntry's key,
    /// and returns a mutable reference to it
    #[inline]
    pub fn insert(self, value: V) -> &'a mut V {
        unsafe { self.inner.insert(value.into_box()).downcast_mut_unchecked() }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        any::{Any, CloneAny, CloneAnySend, CloneAnySendSync, CloneAnySync},
        AnyMap, Entry, Map,
    };

    #[derive(Clone, Debug, PartialEq)]
    struct A(i32);
    #[derive(Clone, Debug, PartialEq)]
    struct B(i32);
    #[derive(Clone, Debug, PartialEq)]
    struct C(i32);
    #[derive(Clone, Debug, PartialEq)]
    struct D(i32);
    #[derive(Clone, Debug, PartialEq)]
    struct E(i32);
    #[derive(Clone, Debug, PartialEq)]
    struct F(i32);
    #[derive(Clone, Debug, PartialEq)]
    struct J(i32);

    macro_rules! test_entry {
        ($name:ident, $init:ty) => {
            #[test]
            fn $name() {
                let mut map = <$init>::new();
                assert_eq!(map.insert(A(10)), None);
                assert_eq!(map.insert(B(20)), None);
                assert_eq!(map.insert(C(30)), None);
                assert_eq!(map.insert(D(40)), None);
                assert_eq!(map.insert(E(50)), None);
                assert_eq!(map.insert(F(60)), None);

                // Existing key (insert)
                match map.entry::<A>() {
                    Entry::Vacant(_) => unreachable!(),
                    Entry::Occupied(mut view) => {
                        assert_eq!(view.get(), &A(10));
                        assert_eq!(view.insert(A(100)), A(10));
                    }
                }
                assert_eq!(map.get::<A>().unwrap(), &A(100));
                assert_eq!(map.len(), 6);

                // Existing key (update)
                match map.entry::<B>() {
                    Entry::Vacant(_) => unreachable!(),
                    Entry::Occupied(mut view) => {
                        let v = view.get_mut();
                        let new_v = B(v.0 * 10);
                        *v = new_v;
                    }
                }
                assert_eq!(map.get::<B>().unwrap(), &B(200));
                assert_eq!(map.len(), 6);

                // Existing key (remove)
                match map.entry::<C>() {
                    Entry::Vacant(_) => unreachable!(),
                    Entry::Occupied(view) => {
                        assert_eq!(view.remove(), C(30));
                    }
                }
                assert_eq!(map.get::<C>(), None);
                assert_eq!(map.len(), 5);

                // Inexistent key (insert)
                match map.entry::<J>() {
                    Entry::Occupied(_) => unreachable!(),
                    Entry::Vacant(view) => {
                        assert_eq!(*view.insert(J(1000)), J(1000));
                    }
                }
                assert_eq!(map.get::<J>().unwrap(), &J(1000));
                assert_eq!(map.len(), 6);

                // Entry.or_insert on existing key
                map.entry::<B>().or_insert(B(71)).0 += 1;
                assert_eq!(map.get::<B>().unwrap(), &B(201));
                assert_eq!(map.len(), 6);

                // Entry.or_insert on nonexisting key
                map.entry::<C>().or_insert(C(300)).0 += 1;
                assert_eq!(map.get::<C>().unwrap(), &C(301));
                assert_eq!(map.len(), 7);
            }
        };
    }

    test_entry!(test_entry_any, AnyMap);
    test_entry!(test_entry_cloneany, Map<dyn CloneAny>);

    #[test]
    fn test_default() {
        let map: AnyMap = Default::default();
        assert_eq!(map.len(), 0);
    }

    #[test]
    fn test_clone() {
        let mut map: Map<dyn CloneAny> = Map::new();
        let _ = map.insert(A(1));
        let _ = map.insert(B(2));
        let _ = map.insert(D(3));
        let _ = map.insert(E(4));
        let _ = map.insert(F(5));
        let _ = map.insert(J(6));
        let map2 = map.clone();
        assert_eq!(map2.len(), 6);
        assert_eq!(map2.get::<A>(), Some(&A(1)));
        assert_eq!(map2.get::<B>(), Some(&B(2)));
        assert_eq!(map2.get::<C>(), None);
        assert_eq!(map2.get::<D>(), Some(&D(3)));
        assert_eq!(map2.get::<E>(), Some(&E(4)));
        assert_eq!(map2.get::<F>(), Some(&F(5)));
        assert_eq!(map2.get::<J>(), Some(&J(6)));
    }

    #[test]
    fn test_varieties() {
        fn assert_send<T: Send>() {}
        fn assert_sync<T: Sync>() {}
        fn assert_clone<T: Clone>() {}
        fn assert_debug<T: ::std::fmt::Debug>() {}
        assert_send::<Map<dyn Any + Send>>();
        assert_send::<Map<dyn Any + Send + Sync>>();
        assert_sync::<Map<dyn Any + Sync>>();
        assert_sync::<Map<dyn Any + Send + Sync>>();
        assert_debug::<Map<dyn Any>>();
        assert_debug::<Map<dyn Any + Send>>();
        assert_debug::<Map<dyn Any + Sync>>();
        assert_debug::<Map<dyn Any + Send + Sync>>();
        assert_send::<Map<dyn CloneAnySend + Send>>();
        assert_send::<Map<dyn CloneAnySendSync + Send + Sync>>();
        assert_sync::<Map<dyn CloneAnySync + Sync>>();
        assert_sync::<Map<dyn CloneAnySendSync + Send + Sync>>();
        assert_clone::<Map<dyn CloneAnySend + Send>>();
        assert_clone::<Map<dyn CloneAnySendSync + Send + Sync>>();
        assert_clone::<Map<dyn CloneAnySync + Sync>>();
        assert_clone::<Map<dyn CloneAnySendSync + Send + Sync>>();
        assert_debug::<Map<dyn CloneAny>>();
        assert_debug::<Map<dyn CloneAnySend + Send>>();
        assert_debug::<Map<dyn CloneAnySync + Sync>>();
        assert_debug::<Map<dyn CloneAnySendSync + Send + Sync>>();
    }
}
