use std::fmt;

#[allow(unused)]
const TAG_SIZE: usize = std::mem::size_of::<u8>();

#[allow(unused)]
const MAX_CAPACITY: usize = std::mem::size_of::<crate::string::StdString>() - TAG_SIZE - TAG_SIZE;

// Performance seems to slow down when trying to occupy all of the padding left by `String`'s
// discriminant.  The question is whether faster len=1-16 "allocations" outweighs going to the heap
// for len=17-22.
#[allow(unused)]
const ALIGNED_CAPACITY: usize = std::mem::size_of::<crate::string::OwnedStr>() - TAG_SIZE;

#[cfg(feature = "max_inline")]
pub(crate) const CAPACITY: usize = MAX_CAPACITY;
#[cfg(not(feature = "max_inline"))]
pub(crate) const CAPACITY: usize = ALIGNED_CAPACITY;

#[derive(Copy, Clone)]
pub(crate) struct InlineString {
    len: u8,
    array: [u8; CAPACITY],
}

impl InlineString {
    #[inline]
    pub(crate) fn new(s: &str) -> Self {
        let len = s.as_bytes().len();
        debug_assert!(len <= CAPACITY);
        let mut array = [0; CAPACITY];
        array[..len].copy_from_slice(&s.as_bytes());
        Self {
            len: len as u8,
            array,
        }
    }

    #[inline]
    pub(crate) fn to_boxed_str(&self) -> Box<str> {
        Box::from(self.as_str())
    }

    #[inline]
    pub(crate) fn as_str(&self) -> &str {
        let len = self.len as usize;
        // SAFETY: Constructors guarantee that `buffer[..len]` is a `str`,
        // and we don't mutate the data afterwards.
        unsafe {
            let slice = self.array.get_unchecked(..len);
            std::str::from_utf8_unchecked(slice)
        }
    }
}

impl fmt::Debug for InlineString {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_str(), f)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_size() {
        println!("InlineString: {}", std::mem::size_of::<InlineString>());
    }
}
