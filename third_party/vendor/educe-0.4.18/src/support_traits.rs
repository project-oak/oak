#[cfg(not(any(
    feature = "Debug",
    feature = "PartialEq",
    feature = "Eq",
    feature = "PartialOrd",
    feature = "Ord",
    feature = "Hash",
    feature = "Default",
    feature = "Clone",
    feature = "Copy",
    feature = "Deref",
    feature = "DerefMut"
)))]
compile_error!("at least one of the trait features must be enabled");

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Ordinalize)]
#[cfg_attr(not(feature = "default"), allow(dead_code))]
pub enum Trait {
    #[cfg(feature = "Debug")]
    Debug,
    #[cfg(feature = "PartialEq")]
    PartialEq,
    #[cfg(feature = "Eq")]
    Eq,
    #[cfg(feature = "PartialOrd")]
    PartialOrd,
    #[cfg(feature = "Ord")]
    Ord,
    #[cfg(feature = "Hash")]
    Hash,
    #[cfg(feature = "Default")]
    Default,
    #[cfg(feature = "Clone")]
    Clone,
    #[cfg(feature = "Copy")]
    Copy,
    #[cfg(feature = "Deref")]
    Deref,
    #[cfg(feature = "DerefMut")]
    DerefMut,
}

impl Trait {
    #[inline]
    pub fn from_str<S: AsRef<str>>(s: S) -> Trait {
        let s = s.as_ref();

        match s {
            #[cfg(feature = "Debug")]
            "Debug" => Trait::Debug,
            #[cfg(feature = "PartialEq")]
            "PartialEq" => Trait::PartialEq,
            #[cfg(feature = "Eq")]
            "Eq" => Trait::Eq,
            #[cfg(feature = "PartialOrd")]
            "PartialOrd" => Trait::PartialOrd,
            #[cfg(feature = "Ord")]
            "Ord" => Trait::Ord,
            #[cfg(feature = "Hash")]
            "Hash" => Trait::Hash,
            #[cfg(feature = "Default")]
            "Default" => Trait::Default,
            #[cfg(feature = "Clone")]
            "Clone" => Trait::Clone,
            #[cfg(feature = "Copy")]
            "Copy" => Trait::Copy,
            #[cfg(feature = "Deref")]
            "Deref" => Trait::Deref,
            #[cfg(feature = "DerefMut")]
            "DerefMut" => Trait::DerefMut,
            _ => panic!("Unsupported trait `{}`. Available traits are {:?}", s, Trait::variants()),
        }
    }
}
