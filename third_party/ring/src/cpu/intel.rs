// Copyright 2016-2021 Brian Smith.
//
// Permission to use, copy, modify, and/or distribute this software for any
// purpose with or without fee is hereby granted, provided that the above
// copyright notice and this permission notice appear in all copies.
//
// THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHORS DISCLAIM ALL WARRANTIES
// WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY
// SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
// WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
// OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
// CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

#![cfg_attr(
    not(any(target_arch = "x86", target_arch = "x86_64")),
    allow(dead_code)
)]

pub(crate) struct Feature {
    word: usize,
    mask: u32,
}

impl Feature {
    #[allow(clippy::needless_return)]
    #[inline(always)]
    pub fn available(&self, _: super::Features) -> bool {
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            prefixed_extern! {
                static mut OPENSSL_ia32cap_P: [u32; 4];
            }
            return self.mask == self.mask & unsafe { OPENSSL_ia32cap_P[self.word] };
        }

        #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
        {
            return false;
        }
    }
}

pub(crate) const FXSR: Feature = Feature {
    word: 0,
    mask: 1 << 24,
};

pub(crate) const PCLMULQDQ: Feature = Feature {
    word: 1,
    mask: 1 << 1,
};

pub(crate) const SSSE3: Feature = Feature {
    word: 1,
    mask: 1 << 9,
};

#[cfg(target_arch = "x86_64")]
pub(crate) const SSE41: Feature = Feature {
    word: 1,
    mask: 1 << 19,
};

#[cfg(target_arch = "x86_64")]
pub(crate) const MOVBE: Feature = Feature {
    word: 1,
    mask: 1 << 22,
};

pub(crate) const AES: Feature = Feature {
    word: 1,
    mask: 1 << 25,
};

#[cfg(target_arch = "x86_64")]
pub(crate) const AVX: Feature = Feature {
    word: 1,
    mask: 1 << 28,
};

#[cfg(all(target_arch = "x86_64", test))]
mod x86_64_tests {
    use super::*;

    #[test]
    fn test_avx_movbe_mask() {
        // This is the OpenSSL style of testing these bits.
        assert_eq!((AVX.mask | MOVBE.mask) >> 22, 0x41);
    }
}
