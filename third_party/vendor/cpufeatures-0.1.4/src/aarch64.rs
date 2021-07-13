//! ARM64 CPU feature detection support.
//!
//! Unfortunately ARM instructions to detect CPU features cannot be called from
//! unprivileged userspace code, so this implementation relies on OS-specific
//! APIs for feature detection.

// Evaluate the given `$body` expression any of the supplied target features
// are not enabled. Otherwise returns true.
#[macro_export]
#[doc(hidden)]
macro_rules! __unless_target_features {
    ($($tf:tt),+ => $body:expr ) => {
        {
            #[cfg(not(all($(target_feature=$tf,)*)))]
            $body

            #[cfg(all($(target_feature=$tf,)*))]
            true
        }
    };
}

// Linux runtime detection of target CPU features using `getauxval`.
#[cfg(target_os = "linux")]
#[macro_export]
#[doc(hidden)]
macro_rules! __detect_target_features {
    ($($tf:tt),+) => {{
        let hwcaps = $crate::aarch64::getauxval_hwcap();
        $($crate::check!(hwcaps, $tf) & )+ true
    }};
}

/// Linux helper function for calling `getauxval` to get `AT_HWCAP`.
#[cfg(target_os = "linux")]
pub fn getauxval_hwcap() -> u64 {
    unsafe { libc::getauxval(libc::AT_HWCAP) }
}

// MacOS runtime detection of target CPU features using `sysctlbyname`.
#[cfg(target_os = "macos")]
#[macro_export]
#[doc(hidden)]
macro_rules! __detect_target_features {
    ($($tf:tt),+) => {{
        $($crate::check!($tf) & )+ true
    }};
}

// Linux `expand_check_macro`
#[cfg(target_os = "linux")]
macro_rules! __expand_check_macro {
    ($(($name:tt, $hwcap:ident)),* $(,)?) => {
        #[macro_export]
        #[doc(hidden)]
        macro_rules! check {
            $(
                ($hwcaps:expr, $name) => {
                    (($hwcaps & $crate::aarch64::hwcaps::$hwcap) != 0)
                };
            )*
        }
    };
}

// Linux `expand_check_macro`
#[cfg(target_os = "linux")]
__expand_check_macro! {
    ("aes",  HWCAP_AES),  // Enable AES support.
    ("sha2", HWCAP_SHA2), // Enable SHA1 and SHA256 support.
    ("sha3", HWCAP_SHA3), // Enable SHA512 and SHA3 support.
}

/// Linux hardware capabilities
///
/// Workaround for these being missing from certain environments (i.e. Musl)
/// See: <https://github.com/rust-lang/libc/issues/2171>
#[cfg(target_os = "linux")]
pub mod hwcaps {
    pub const HWCAP_AES: libc::c_ulong = 1 << 3;
    pub const HWCAP_NEON: libc::c_ulong = 1 << 12;
    pub const HWCAP_SHA2: libc::c_ulong = 1 << 6;
    pub const HWCAP_SHA3: libc::c_ulong = 1 << 17;
}

// macOS `check!` macro.
//
// NOTE: several of these instructions (e.g. `aes`, `sha2`) can be assumed to
// be present on all Apple ARM64 hardware.
//
// Newer CPU instructions now have nodes within sysctl's `hw.optional`
// namespace, however the ones that do not can safely be assumed to be
// present on all Apple ARM64 devices, now and for the foreseeable future.
//
// See discussion on this issue for more information:
// <https://github.com/RustCrypto/utils/issues/378>
#[cfg(target_os = "macos")]
#[macro_export]
#[doc(hidden)]
macro_rules! check {
    ("aes") => {
        true
    };
    ("sha2") => {
        true
    };
    ("sha3") => {
        unsafe { $crate::aarch64::sysctlbyname(b"hw.optional.armv8_2_sha3\0") }
    };
}

/// macOS helper function for calling `sysctlbyname`.
#[cfg(target_os = "macos")]
pub unsafe fn sysctlbyname(name: &[u8]) -> bool {
    assert_eq!(
        name.last().cloned(),
        Some(0),
        "name is not NUL terminated: {:?}",
        name
    );

    let mut value: u32 = 0;
    let mut size = core::mem::size_of::<u32>();

    let rc = libc::sysctlbyname(
        name.as_ptr() as *const i8,
        &mut value as *mut _ as *mut libc::c_void,
        &mut size,
        core::ptr::null_mut(),
        0,
    );

    assert_eq!(size, 4, "unexpected sysctlbyname(3) result size");
    assert_eq!(rc, 0, "sysctlbyname returned error code: {}", rc);
    value != 0
}

// On other targets, runtime CPU feature detection is unavailable
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
#[macro_export]
#[doc(hidden)]
macro_rules! __detect_target_features {
    ($($tf:tt),+) => {
        false
    };
}
