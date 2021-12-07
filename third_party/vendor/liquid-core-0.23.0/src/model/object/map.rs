//! Type representing a Liquid object, payload of the `Value::Object` variant

use std::borrow::Borrow;
use std::collections::hash_map;
use std::fmt::{self, Debug};
use std::hash::Hash;
use std::iter::FromIterator;
use std::ops;

use serde::{de, ser};

use super::Value;

/// Type representing a Liquid object, payload of the `Value::Object` variant
pub struct Object {
    map: MapImpl<Key, Value>,
}

type Key = kstring::KString;

type MapImpl<K, V> = hash_map::HashMap<K, V>;
type VacantEntryImpl<'a> = hash_map::VacantEntry<'a, Key, Value>;
type OccupiedEntryImpl<'a> = hash_map::OccupiedEntry<'a, Key, Value>;
type IterImpl<'a> = hash_map::Iter<'a, Key, Value>;
type IterMutImpl<'a> = hash_map::IterMut<'a, Key, Value>;
type IntoIterImpl = hash_map::IntoIter<Key, Value>;
type KeysImpl<'a> = hash_map::Keys<'a, Key, Value>;
type ValuesImpl<'a> = hash_map::Values<'a, Key, Value>;
type ValuesMutImpl<'a> = hash_map::ValuesMut<'a, Key, Value>;

impl Object {
    /// Makes a new empty Object.
    #[inline]
    pub fn new() -> Self {
        Object {
            map: MapImpl::new(),
        }
    }

    /// Clears the map, removing all values.
    #[inline]
    pub fn clear(&mut self) {
        self.map.clear()
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    #[inline]
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&Value>
    where
        Key: Borrow<Q>,
        Q: Ord + Eq + Hash,
    {
        self.map.get(key)
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    #[inline]
    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
    where
        Key: Borrow<Q>,
        Q: Ord + Eq + Hash,
    {
        self.map.contains_key(key)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    #[inline]
    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut Value>
    where
        Key: Borrow<Q>,
        Q: Ord + Eq + Hash,
    {
        self.map.get_mut(key)
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned.
    #[inline]
    pub fn insert(&mut self, k: Key, v: Value) -> Option<Value> {
        self.map.insert(k, v)
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    #[inline]
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<Value>
    where
        Key: Borrow<Q>,
        Q: Ord + Eq + Hash,
    {
        self.map.remove(key)
    }

    /// Gets the given key's corresponding entry in the map for in-place
    /// manipulation.
    pub fn entry<S>(&mut self, key: S) -> Entry<'_>
    where
        S: Into<Key>,
    {
        use std::collections::hash_map::Entry as EntryImpl;
        match self.map.entry(key.into()) {
            EntryImpl::Vacant(vacant) => Entry::Vacant(VacantEntry { vacant }),
            EntryImpl::Occupied(occupied) => Entry::Occupied(OccupiedEntry { occupied }),
        }
    }

    /// Returns the number of elements in the map.
    #[inline]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns true if the map contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Gets an iterator over the entries of the map.
    #[inline]
    pub fn iter(&self) -> Iter<'_> {
        Iter {
            iter: self.map.iter(),
        }
    }

    /// Gets a mutable iterator over the entries of the map.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_> {
        IterMut {
            iter: self.map.iter_mut(),
        }
    }

    /// Gets an iterator over the keys of the map.
    #[inline]
    pub fn keys(&self) -> Keys<'_> {
        Keys {
            iter: self.map.keys(),
        }
    }

    /// Gets an iterator over the values of the map.
    #[inline]
    pub fn values(&self) -> Values<'_> {
        Values {
            iter: self.map.values(),
        }
    }

    /// Gets an iterator over mutable values of the map.
    #[inline]
    pub fn values_mut(&mut self) -> ValuesMut<'_> {
        ValuesMut {
            iter: self.map.values_mut(),
        }
    }
}

impl Default for Object {
    #[inline]
    fn default() -> Self {
        Self {
            map: MapImpl::new(),
        }
    }
}

impl Clone for Object {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            map: self.map.clone(),
        }
    }
}

impl PartialEq for Object {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.map.eq(&other.map)
    }
}

impl Eq for Object {}

/// Access an element of this map. Panics if the given key is not present in the
/// map.
///
/// ```rust
/// # use liquid_core::model::Value;
/// # use liquid_core::model::ValueView;
/// #
/// # let val = &Value::scalar("");
/// # let _ =
/// match *val {
///     Value::Scalar(ref s) => Some(s.to_kstr()),
///     Value::Array(ref arr) => Some(arr[0].to_kstr()),
///     Value::Object(ref map) => Some(map["type"].to_kstr()),
///     _ => None,
/// }
/// # ;
/// ```
impl<'a, Q: ?Sized> ops::Index<&'a Q> for Object
where
    Key: Borrow<Q>,
    Q: Ord + Eq + Hash,
{
    type Output = Value;

    fn index(&self, index: &Q) -> &Value {
        self.map.index(index)
    }
}

/// Mutably access an element of this map. Panics if the given key is not
/// present in the map.
///
/// ```rust
/// #     let mut map = liquid_core::model::Object::new();
/// #     map.insert("key".into(), liquid_core::model::Value::Nil);
/// #
/// map["key"] = liquid_core::value!("value");
/// ```
impl<'a, Q: ?Sized> ops::IndexMut<&'a Q> for Object
where
    Key: Borrow<Q>,
    Q: Ord + Eq + Hash,
{
    fn index_mut(&mut self, index: &Q) -> &mut Value {
        self.map.get_mut(index).expect("no entry found for key")
    }
}

impl Debug for Object {
    #[inline]
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        self.map.fmt(formatter)
    }
}

impl ser::Serialize for Object {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ser::Serializer,
    {
        use serde::ser::SerializeMap;
        let mut map = serializer.serialize_map(Some(self.len()))?;
        for (k, v) in self {
            map.serialize_key(k)?;
            map.serialize_value(v)?;
        }
        map.end()
    }
}

impl<'de> de::Deserialize<'de> for Object {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        struct Visitor;

        impl<'de> de::Visitor<'de> for Visitor {
            type Value = Object;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a map")
            }

            #[inline]
            fn visit_unit<E>(self) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(Object::new())
            }

            #[inline]
            fn visit_map<V>(self, mut visitor: V) -> Result<Self::Value, V::Error>
            where
                V: de::MapAccess<'de>,
            {
                let mut values = Object::new();

                while let Some((key, value)) = visitor.next_entry()? {
                    values.insert(key, value);
                }

                Ok(values)
            }
        }

        deserializer.deserialize_map(Visitor)
    }
}

impl FromIterator<(Key, Value)> for Object {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (Key, Value)>,
    {
        Self {
            map: FromIterator::from_iter(iter),
        }
    }
}

impl Extend<(Key, Value)> for Object {
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = (Key, Value)>,
    {
        self.map.extend(iter);
    }
}

macro_rules! delegate_iterator {
    (($name:ident $($generics:tt)*) => $item:ty) => {
        impl $($generics)* Iterator for $name $($generics)* {
            type Item = $item;
            #[inline]
            fn next(&mut self) -> Option<Self::Item> {
                self.iter.next()
            }
            #[inline]
            fn size_hint(&self) -> (usize, Option<usize>) {
                self.iter.size_hint()
            }
        }

        impl $($generics)* ExactSizeIterator for $name $($generics)* {
            #[inline]
            fn len(&self) -> usize {
                self.iter.len()
            }
        }
    }
}

//////////////////////////////////////////////////////////////////////////////

/// A view into a single entry in a map, which may either be vacant or occupied.
/// This enum is constructed from the [`entry`] method on [`Object`].
///
/// [`entry`]: Object::entry()
#[derive(Debug)]
pub enum Entry<'a> {
    /// A vacant Entry.
    Vacant(VacantEntry<'a>),
    /// An occupied Entry.
    Occupied(OccupiedEntry<'a>),
}

/// A vacant Entry. It is part of the [`Entry`] enum.
///
#[derive(Debug)]
pub struct VacantEntry<'a> {
    vacant: VacantEntryImpl<'a>,
}

/// An occupied Entry. It is part of the [`Entry`] enum.
///
#[derive(Debug)]
pub struct OccupiedEntry<'a> {
    occupied: OccupiedEntryImpl<'a>,
}

impl<'a> Entry<'a> {
    /// Returns a reference to this entry's key.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut map = liquid_core::model::Object::new();
    /// assert_eq!(map.entry("liquid").key(), &"liquid");
    /// ```
    pub fn key(&self) -> &Key {
        match *self {
            Entry::Vacant(ref e) => e.key(),
            Entry::Occupied(ref e) => e.key(),
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty, and
    /// returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut map = liquid_core::model::Object::new();
    /// map.entry("liquid").or_insert(liquid_core::value!(12));
    ///
    /// assert_eq!(map["liquid"], liquid_core::value!(12));
    /// ```
    pub fn or_insert(self, default: Value) -> &'a mut Value {
        match self {
            Entry::Vacant(entry) => entry.insert(default),
            Entry::Occupied(entry) => entry.into_mut(),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default
    /// function if empty, and returns a mutable reference to the value in the
    /// entry.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut map = liquid_core::model::Object::new();
    /// map.entry("liquid").or_insert_with(|| liquid_core::value!("hoho"));
    ///
    /// assert_eq!(map["liquid"], liquid_core::value!("hoho"));
    /// ```
    pub fn or_insert_with<F>(self, default: F) -> &'a mut Value
    where
        F: FnOnce() -> Value,
    {
        match self {
            Entry::Vacant(entry) => entry.insert(default()),
            Entry::Occupied(entry) => entry.into_mut(),
        }
    }
}

impl<'a> VacantEntry<'a> {
    /// Gets a reference to the key that would be used when inserting a value
    /// through the VacantEntry.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use liquid_core::model::map::Entry;
    ///
    /// let mut map = liquid_core::model::Object::new();
    ///
    /// match map.entry("liquid") {
    ///     Entry::Vacant(vacant) => {
    ///         assert_eq!(vacant.key(), &"liquid");
    ///     }
    ///     Entry::Occupied(_) => unimplemented!(),
    /// }
    /// ```
    #[inline]
    pub fn key(&self) -> &Key {
        self.vacant.key()
    }

    /// Sets the value of the entry with the VacantEntry's key, and returns a
    /// mutable reference to it.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use liquid_core::model::map::Entry;
    ///
    /// let mut map = liquid_core::model::Object::new();
    ///
    /// match map.entry("liquid") {
    ///     Entry::Vacant(vacant) => {
    ///         vacant.insert(liquid_core::value!("hoho"));
    ///     }
    ///     Entry::Occupied(_) => unimplemented!(),
    /// }
    /// ```
    #[inline]
    pub fn insert(self, value: Value) -> &'a mut Value {
        self.vacant.insert(value)
    }
}

impl<'a> OccupiedEntry<'a> {
    /// Gets a reference to the key in the entry.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use liquid_core::model::map::Entry;
    ///
    /// let mut map = liquid_core::model::Object::new();
    /// map.insert("liquid".into(), liquid_core::value!(12));
    ///
    /// match map.entry("liquid") {
    ///     Entry::Occupied(occupied) => {
    ///         assert_eq!(occupied.key(), &"liquid");
    ///     }
    ///     Entry::Vacant(_) => unimplemented!(),
    /// }
    /// ```
    #[inline]
    pub fn key(&self) -> &Key {
        self.occupied.key()
    }

    /// Gets a reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use liquid_core::model::map::Entry;
    ///
    /// let mut map = liquid_core::model::Object::new();
    /// map.insert("liquid".into(), liquid_core::value!(12));
    ///
    /// match map.entry("liquid") {
    ///     Entry::Occupied(occupied) => {
    ///         assert_eq!(occupied.get(), &liquid_core::value!(12));
    ///     }
    ///     Entry::Vacant(_) => unimplemented!(),
    /// }
    /// ```
    #[inline]
    pub fn get(&self) -> &Value {
        self.occupied.get()
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use liquid_core::model::ValueView;
    /// #
    /// use liquid_core::model::map::Entry;
    ///
    /// let mut map = liquid_core::model::Object::new();
    /// map.insert("liquid".into(), liquid_core::value!([1, 2, 3]));
    ///
    /// match map.entry("liquid") {
    ///     Entry::Occupied(mut occupied) => {
    ///         occupied.get_mut().as_array().unwrap();
    ///     }
    ///     Entry::Vacant(_) => unimplemented!(),
    /// }
    /// ```
    #[inline]
    pub fn get_mut(&mut self) -> &mut Value {
        self.occupied.get_mut()
    }

    /// Converts the entry into a mutable reference to its value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use liquid_core::model::ValueView;
    /// #
    /// use liquid_core::model::map::Entry;
    ///
    /// let mut map = liquid_core::model::Object::new();
    /// map.insert("liquid".into(), liquid_core::value!([1, 2, 3]));
    ///
    /// match map.entry("liquid") {
    ///     Entry::Occupied(mut occupied) => {
    ///         occupied.into_mut().as_array().unwrap();
    ///     }
    ///     Entry::Vacant(_) => unimplemented!(),
    /// }
    /// ```
    #[inline]
    pub fn into_mut(self) -> &'a mut Value {
        self.occupied.into_mut()
    }

    /// Sets the value of the entry with the `OccupiedEntry`'s key, and returns
    /// the entry's old value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use liquid_core::model::map::Entry;
    ///
    /// let mut map = liquid_core::model::Object::new();
    /// map.insert("liquid".into(), liquid_core::value!(12));
    ///
    /// match map.entry("liquid") {
    ///     Entry::Occupied(mut occupied) => {
    ///         assert_eq!(occupied.insert(liquid_core::value!(13)), liquid_core::value!(12));
    ///         assert_eq!(occupied.get(), &liquid_core::value!(13));
    ///     }
    ///     Entry::Vacant(_) => unimplemented!(),
    /// }
    /// ```
    #[inline]
    pub fn insert(&mut self, value: Value) -> Value {
        self.occupied.insert(value)
    }

    /// Takes the value of the entry out of the map, and returns it.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use liquid_core::model::map::Entry;
    ///
    /// let mut map = liquid_core::model::Object::new();
    /// map.insert("liquid".into(), liquid_core::value!(12));
    ///
    /// match map.entry("liquid") {
    ///     Entry::Occupied(occupied) => {
    ///         assert_eq!(occupied.remove(), liquid_core::value!(12));
    ///     }
    ///     Entry::Vacant(_) => unimplemented!(),
    /// }
    /// ```
    #[inline]
    pub fn remove(self) -> Value {
        self.occupied.remove()
    }
}

//////////////////////////////////////////////////////////////////////////////

impl<'a> IntoIterator for &'a Object {
    type Item = (&'a Key, &'a Value);
    type IntoIter = Iter<'a>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        Iter {
            iter: self.map.iter(),
        }
    }
}

/// An iterator over a liquid_core::model::Object's entries.
#[derive(Debug)]
pub struct Iter<'a> {
    iter: IterImpl<'a>,
}

delegate_iterator!((Iter<'a>) => (&'a Key, &'a Value));

//////////////////////////////////////////////////////////////////////////////

impl<'a> IntoIterator for &'a mut Object {
    type Item = (&'a Key, &'a mut Value);
    type IntoIter = IterMut<'a>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IterMut {
            iter: self.map.iter_mut(),
        }
    }
}

/// A mutable iterator over a liquid_core::model::Object's entries.
#[derive(Debug)]
pub struct IterMut<'a> {
    iter: IterMutImpl<'a>,
}

delegate_iterator!((IterMut<'a>) => (&'a Key, &'a mut Value));

//////////////////////////////////////////////////////////////////////////////

impl IntoIterator for Object {
    type Item = (Key, Value);
    type IntoIter = IntoIter;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            iter: self.map.into_iter(),
        }
    }
}

/// An owning iterator over a liquid_core::model::Object's entries.
#[derive(Debug)]
pub struct IntoIter {
    iter: IntoIterImpl,
}

delegate_iterator!((IntoIter) => (Key, Value));

//////////////////////////////////////////////////////////////////////////////

/// An iterator over a liquid_core::model::Object's keys.
#[derive(Debug)]
pub struct Keys<'a> {
    iter: KeysImpl<'a>,
}

delegate_iterator!((Keys<'a>) => &'a Key);

//////////////////////////////////////////////////////////////////////////////

/// An iterator over a liquid_core::model::Object's values.
#[derive(Debug)]
pub struct Values<'a> {
    iter: ValuesImpl<'a>,
}

delegate_iterator!((Values<'a>) => &'a Value);

//////////////////////////////////////////////////////////////////////////////

/// A mutable iterator over a liquid_core::model::Object's values.
#[derive(Debug)]
pub struct ValuesMut<'a> {
    iter: ValuesMutImpl<'a>,
}

delegate_iterator!((ValuesMut<'a>) => &'a mut Value);
