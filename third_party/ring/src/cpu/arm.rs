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

#[cfg(all(
    any(target_os = "android", target_os = "linux"),
    any(target_arch = "aarch64", target_arch = "arm")
))]
pub fn setup() {
    use libc::c_ulong;

    // XXX: The `libc` crate doesn't provide `libc::getauxval` consistently
    // across all Android/Linux targets, e.g. musl.
    extern "C" {
        fn getauxval(type_: c_ulong) -> c_ulong;
    }

    const AT_HWCAP: c_ulong = 16;

    #[cfg(target_arch = "aarch64")]
    const HWCAP_NEON: c_ulong = 1 << 1;

    #[cfg(target_arch = "arm")]
    const HWCAP_NEON: c_ulong = 1 << 12;

    let caps = unsafe { getauxval(AT_HWCAP) };

    // We assume NEON is available on AARCH64 because it is a required
    // feature.
    #[cfg(target_arch = "aarch64")]
    debug_assert!(caps & HWCAP_NEON == HWCAP_NEON);

    // OpenSSL and BoringSSL don't enable any other features if NEON isn't
    // available.
    if caps & HWCAP_NEON == HWCAP_NEON {
        let mut features = NEON.mask;

        #[cfg(target_arch = "aarch64")]
        const OFFSET: c_ulong = 3;

        #[cfg(target_arch = "arm")]
        const OFFSET: c_ulong = 0;

        #[cfg(target_arch = "arm")]
        let caps = {
            const AT_HWCAP2: c_ulong = 26;
            unsafe { getauxval(AT_HWCAP2) }
        };

        const HWCAP_AES: c_ulong = 1 << 0 + OFFSET;
        const HWCAP_PMULL: c_ulong = 1 << 1 + OFFSET;
        const HWCAP_SHA2: c_ulong = 1 << 3 + OFFSET;

        if caps & HWCAP_AES == HWCAP_AES {
            features |= AES.mask;
        }
        if caps & HWCAP_PMULL == HWCAP_PMULL {
            features |= PMULL.mask;
        }
        if caps & HWCAP_SHA2 == HWCAP_SHA2 {
            features |= SHA256.mask;
        }

        unsafe { OPENSSL_armcap_P = features };
    }
}

#[cfg(all(target_os = "fuchsia", target_arch = "aarch64"))]
pub fn setup() {
    type zx_status_t = i32;

    #[link(name = "zircon")]
    extern "C" {
        fn zx_system_get_features(kind: u32, features: *mut u32) -> zx_status_t;
    }

    const ZX_OK: i32 = 0;
    const ZX_FEATURE_KIND_CPU: u32 = 0;
    const ZX_ARM64_FEATURE_ISA_ASIMD: u32 = 1 << 2;
    const ZX_ARM64_FEATURE_ISA_AES: u32 = 1 << 3;
    const ZX_ARM64_FEATURE_ISA_PMULL: u32 = 1 << 4;
    const ZX_ARM64_FEATURE_ISA_SHA2: u32 = 1 << 6;

    let mut caps = 0;
    let rc = unsafe { zx_system_get_features(ZX_FEATURE_KIND_CPU, &mut caps) };

    // OpenSSL and BoringSSL don't enable any other features if NEON isn't
    // available.
    if rc == ZX_OK && (caps & ZX_ARM64_FEATURE_ISA_ASIMD == ZX_ARM64_FEATURE_ISA_ASIMD) {
        let mut features = NEON.mask;

        if caps & ZX_ARM64_FEATURE_ISA_AES == ZX_ARM64_FEATURE_ISA_AES {
            features |= AES.mask;
        }
        if caps & ZX_ARM64_FEATURE_ISA_PMULL == ZX_ARM64_FEATURE_ISA_PMULL {
            features |= PMULL.mask;
        }
        if caps & ZX_ARM64_FEATURE_ISA_SHA2 == ZX_ARM64_FEATURE_ISA_SHA2 {
            features |= 1 << 4;
        }

        unsafe { OPENSSL_armcap_P = features };
    }
}

#[cfg(all(target_os = "windows", target_arch = "aarch64"))]
pub fn setup() {
    // We do not need to check for the presence of NEON, as Armv8-A always has it
    let mut features = NEON.mask;

    let result = unsafe {
        winapi::um::processthreadsapi::IsProcessorFeaturePresent(
            winapi::um::winnt::PF_ARM_V8_CRYPTO_INSTRUCTIONS_AVAILABLE,
        )
    };

    if result != 0 {
        // These are all covered by one call in Windows
        features |= AES.mask;
        features |= PMULL.mask;
        features |= SHA256.mask;
    }

    unsafe { OPENSSL_armcap_P = features };
}

macro_rules! features {
    {
        $(
            $name:ident {
                mask: $mask:expr,

                /// Should we assume that the feature is always available
                /// for aarch64-apple-* targets? The first AArch64 iOS
                /// device used the Apple A7 chip.
                // TODO: When we can use `if` in const expressions:
                // ```
                // aarch64_apple: $aarch64_apple,
                // ```
                aarch64_apple: true,
            }
        ),+
        , // trailing comma is required.
    } => {
        $(
            #[allow(dead_code)]
            pub(crate) const $name: Feature = Feature {
                mask: $mask,
            };
        )+

        // TODO: When we can use `if` in const expressions, do this:
        // ```
        // const ARMCAP_STATIC: u32 = 0
        //    $(
        //        | ( if $aarch64_apple &&
        //               cfg!(all(target_arch = "aarch64",
        //                        target_vendor = "apple")) {
        //                $name.mask
        //            } else {
        //                0
        //            }
        //          )
        //    )+;
        // ```
        //
        // TODO: Add static feature detection to other targets.
        // TODO: Combine static feature detection with runtime feature
        //       detection.
        #[cfg(all(target_arch = "aarch64", target_vendor = "apple"))]
        const ARMCAP_STATIC: u32 = 0
            $(  | $name.mask
            )+;
        #[cfg(not(all(target_arch = "aarch64", target_vendor = "apple")))]
        const ARMCAP_STATIC: u32 = 0;

        #[cfg(all(target_arch = "aarch64", target_vendor = "apple"))]
        #[test]
        fn test_armcap_static_available() {
            let features = crate::cpu::features();
            $(
                assert!($name.available(features));
            )+
        }
    }
}

pub(crate) struct Feature {
    mask: u32,
}

impl Feature {
    #[inline(always)]
    pub fn available(&self, _: super::Features) -> bool {
        if self.mask == self.mask & ARMCAP_STATIC {
            return true;
        }

        #[cfg(all(
            any(
                target_os = "android",
                target_os = "fuchsia",
                target_os = "linux",
                target_os = "windows"
            ),
            any(target_arch = "arm", target_arch = "aarch64")
        ))]
        {
            if self.mask == self.mask & unsafe { OPENSSL_armcap_P } {
                return true;
            }
        }

        false
    }
}

features! {
    // Keep in sync with `ARMV7_NEON`.
    NEON {
        mask: 1 << 0,
        aarch64_apple: true,
    },

    // Keep in sync with `ARMV8_AES`.
    AES {
        mask: 1 << 2,
        aarch64_apple: true,
    },

    // Keep in sync with `ARMV8_SHA256`.
    SHA256 {
        mask: 1 << 4,
        aarch64_apple: true,
    },

    // Keep in sync with `ARMV8_PMULL`.
    PMULL {
        mask: 1 << 5,
        aarch64_apple: true,
    },
}

// Some non-Rust code still checks this even when it is statically known
// the given feature is available, so we have to ensure that this is
// initialized properly. Keep this in sync with the initialization in
// BoringSSL's crypto.c.
//
// TODO: This should have "hidden" visibility but we don't have a way of
// controlling that yet: https://github.com/rust-lang/rust/issues/73958.
#[cfg(any(target_arch = "arm", target_arch = "aarch64"))]
prefixed_export! {
    #[allow(non_upper_case_globals)]
    static mut OPENSSL_armcap_P: u32 = ARMCAP_STATIC;
}

#[cfg(all(
    any(target_arch = "arm", target_arch = "aarch64"),
    target_vendor = "apple"
))]
#[test]
fn test_armcap_static_matches_armcap_dynamic() {
    assert_eq!(ARMCAP_STATIC, 1 | 4 | 16 | 32);
    assert_eq!(ARMCAP_STATIC, unsafe { OPENSSL_armcap_P });
}
