use crate::base::SecCertificateRef;
use crate::base::SecKeyRef;
use core_foundation_sys::array::CFArrayRef;
use core_foundation_sys::base::{Boolean, CFIndex, CFTypeID, CFTypeRef, OSStatus};
#[cfg(any(feature = "OSX_10_13", target_os = "ios"))]
use core_foundation_sys::error::CFErrorRef;

pub type SecTrustResultType = u32;

pub const kSecTrustResultInvalid: SecTrustResultType = 0;
pub const kSecTrustResultProceed: SecTrustResultType = 1;
pub const kSecTrustResultDeny: SecTrustResultType = 3;
pub const kSecTrustResultUnspecified: SecTrustResultType = 4;
pub const kSecTrustResultRecoverableTrustFailure: SecTrustResultType = 5;
pub const kSecTrustResultFatalTrustFailure: SecTrustResultType = 6;
pub const kSecTrustResultOtherError: SecTrustResultType = 7;

pub enum __SecTrust {}

pub type SecTrustRef = *mut __SecTrust;

extern "C" {
    pub fn SecTrustGetTypeID() -> CFTypeID;
    pub fn SecTrustGetCertificateCount(trust: SecTrustRef) -> CFIndex;
    #[deprecated(note = "deprecated by Apple")]
    pub fn SecTrustGetCertificateAtIndex(trust: SecTrustRef, ix: CFIndex) -> SecCertificateRef;
    pub fn SecTrustSetAnchorCertificates(
        trust: SecTrustRef,
        anchorCertificates: CFArrayRef,
    ) -> OSStatus;
    pub fn SecTrustSetAnchorCertificatesOnly(
        trust: SecTrustRef,
        anchorCertificatesOnly: Boolean,
    ) -> OSStatus;
    #[cfg(target_os = "macos")]
    pub fn SecTrustCopyAnchorCertificates(anchors: *mut CFArrayRef) -> OSStatus;
    #[deprecated(note = "deprecated by Apple")]
    pub fn SecTrustEvaluate(trust: SecTrustRef, result: *mut SecTrustResultType) -> OSStatus;
    // it should have been OSX_10_14, but due to back-compat it can't rely on the newer feature flag
    #[cfg(any(feature = "OSX_10_13", target_os = "ios"))]
    pub fn SecTrustEvaluateWithError(trust: SecTrustRef, error: *mut CFErrorRef) -> bool;
    pub fn SecTrustCreateWithCertificates(
        certificates: CFTypeRef,
        policies: CFTypeRef,
        trust: *mut SecTrustRef,
    ) -> OSStatus;
    pub fn SecTrustSetPolicies(trust: SecTrustRef, policies: CFTypeRef) -> OSStatus;
    pub fn SecTrustCopyPublicKey(trust: SecTrustRef) -> SecKeyRef;
}
