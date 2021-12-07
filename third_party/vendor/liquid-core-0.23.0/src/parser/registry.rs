use std::collections::hash_map;

type MapImpl<K, V> = hash_map::HashMap<K, V>;
type KeysImpl<'a, K, V> = hash_map::Keys<'a, K, V>;

/// Liquid language plugin registry.
pub struct PluginRegistry<P> {
    plugins: MapImpl<String, P>,
}

impl<P> PluginRegistry<P> {
    /// Create a new registry.
    pub fn new() -> Self {
        Self {
            plugins: Default::default(),
        }
    }

    /// Register a plugin
    ///
    /// Generally this is used when setting up the program.
    ///
    /// Returns whether this overrode an existing plugin.
    pub fn register(&mut self, name: String, plugin: P) -> bool {
        let old = self.plugins.insert(name, plugin);
        old.is_some()
    }

    /// Look up an existing plugin.
    ///
    /// Generally this is used for running plugins.
    pub fn get(&self, name: &str) -> Option<&P> {
        self.plugins.get(name)
    }

    /// All available plugins
    pub fn plugin_names(&self) -> PluginNames<P> {
        PluginNames {
            iter: self.plugins.keys(),
        }
    }

    /// All plugins
    pub fn plugins(&self) -> impl Iterator<Item = &P> {
        self.plugins.values()
    }
}

impl<P> Default for PluginRegistry<P> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<P> Clone for PluginRegistry<P>
where
    P: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            plugins: self.plugins.clone(),
        }
    }
}

//////////////////////////////////////////////////////////////////////////////

macro_rules! delegate_iterator {
    (($name:ident $($generics:tt)*) => $item:ty) => {
        impl $($generics)* Iterator for $name $($generics)* {
            type Item = $item;
            #[inline]
            fn next(&mut self) -> Option<Self::Item> {
                self.iter.next().map(|s| s.as_str())
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

/// Available plugins.
#[derive(Debug)]
pub struct PluginNames<'a, P>
where
    P: 'a,
{
    iter: KeysImpl<'a, String, P>,
}

delegate_iterator!((PluginNames<'a, P>) => &'a str);
