// -*- mode: rust; -*-
//
// This file is part of x25519-dalek.
// Copyright (c) 2017-2021 isis lovecruft
// Copyright (c) 2019-2021 DebugSteven
// See LICENSE for licensing information.
//
// Authors:
// - isis agora lovecruft <isis@patternsinthevoid.net>
// - DebugSteven <debugsteven@gmail.com>

//! x25519 Diffie-Hellman key exchange
//!
//! This implements x25519 key exchange as specified by Mike Hamburg
//! and Adam Langley in [RFC7748](https://tools.ietf.org/html/rfc7748).

use curve25519_dalek::constants::ED25519_BASEPOINT_TABLE;
use curve25519_dalek::montgomery::MontgomeryPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::IsIdentity;

use rand_core::CryptoRng;
use rand_core::RngCore;

use zeroize::Zeroize;

/// A Diffie-Hellman public key, corresponding to an [`EphemeralSecret`] or
/// [`StaticSecret`] key.
///
/// We implement `Zeroize` so that downstream consumers may derive it for `Drop`
/// should they wish to erase public keys from memory.  Note that this erasure
/// (in this crate) does *not* automatically happen, but either must be derived
/// for Drop or explicitly called.
#[cfg_attr(feature = "serde", serde(crate = "our_serde"))]
#[cfg_attr(
    feature = "serde",
    derive(our_serde::Serialize, our_serde::Deserialize)
)]
#[derive(PartialEq, Eq, Hash, Copy, Clone, Debug, Zeroize)]
pub struct PublicKey(pub(crate) MontgomeryPoint);

impl From<[u8; 32]> for PublicKey {
    /// Given a byte array, construct a x25519 `PublicKey`.
    fn from(bytes: [u8; 32]) -> PublicKey {
        PublicKey(MontgomeryPoint(bytes))
    }
}

impl PublicKey {
    /// Convert this public key to a byte array.
    #[inline]
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.to_bytes()
    }

    /// View this public key as a byte array.
    #[inline]
    pub fn as_bytes(&self) -> &[u8; 32] {
        self.0.as_bytes()
    }
}

/// A short-lived Diffie-Hellman secret key that can only be used to compute a single
/// [`SharedSecret`].
///
/// This type is identical to the [`StaticSecret`] type, except that the
/// [`EphemeralSecret::diffie_hellman`] method consumes and then wipes the secret key, and there
/// are no serialization methods defined.  This means that [`EphemeralSecret`]s can only be
/// generated from fresh randomness by [`EphemeralSecret::new`] and the compiler statically checks
/// that the resulting secret is used at most once.
#[derive(Zeroize)]
#[zeroize(drop)]
pub struct EphemeralSecret(pub(crate) Scalar);

impl EphemeralSecret {
    /// Perform a Diffie-Hellman key agreement between `self` and
    /// `their_public` key to produce a [`SharedSecret`].
    pub fn diffie_hellman(self, their_public: &PublicKey) -> SharedSecret {
        SharedSecret(self.0 * their_public.0)
    }

    /// Generate an x25519 [`EphemeralSecret`] key.
    pub fn new<T: RngCore + CryptoRng>(mut csprng: T) -> Self {
        let mut bytes = [0u8; 32];

        csprng.fill_bytes(&mut bytes);

        EphemeralSecret(clamp_scalar(bytes))
    }
}

impl<'a> From<&'a EphemeralSecret> for PublicKey {
    /// Given an x25519 [`EphemeralSecret`] key, compute its corresponding [`PublicKey`].
    fn from(secret: &'a EphemeralSecret) -> PublicKey {
        PublicKey((&ED25519_BASEPOINT_TABLE * &secret.0).to_montgomery())
    }
}

/// A Diffie-Hellman secret key which may be used more than once, but is
/// purposefully not serialiseable in order to discourage key-reuse.  This is
/// implemented to facilitate protocols such as Noise (e.g. Noise IK key usage,
/// etc.) and X3DH which require an "ephemeral" key to conduct the
/// Diffie-Hellman operation multiple times throughout the protocol, while the
/// protocol run at a higher level is only conducted once per key.
///
/// Similarly to [`EphemeralSecret`], this type does _not_ have serialisation
/// methods, in order to discourage long-term usage of secret key material. (For
/// long-term secret keys, see [`StaticSecret`].)
///
/// # Warning
///
/// If you're uncertain about whether you should use this, then you likely
/// should not be using this.  Our strongly recommended advice is to use
/// [`EphemeralSecret`] at all times, as that type enforces at compile-time that
/// secret keys are never reused, which can have very serious security
/// implications for many protocols.
#[cfg(feature = "reusable_secrets")]
#[derive(Clone, Zeroize)]
#[zeroize(drop)]
pub struct ReusableSecret(pub(crate) Scalar);

#[cfg(feature = "reusable_secrets")]
impl ReusableSecret {
    /// Perform a Diffie-Hellman key agreement between `self` and
    /// `their_public` key to produce a [`SharedSecret`].
    pub fn diffie_hellman(&self, their_public: &PublicKey) -> SharedSecret {
        SharedSecret(&self.0 * their_public.0)
    }

    /// Generate a non-serializeable x25519 [`ReuseableSecret`] key.
    pub fn new<T: RngCore + CryptoRng>(mut csprng: T) -> Self {
        let mut bytes = [0u8; 32];

        csprng.fill_bytes(&mut bytes);

        ReusableSecret(clamp_scalar(bytes))
    }
}

#[cfg(feature = "reusable_secrets")]
impl<'a> From<&'a ReusableSecret> for PublicKey {
    /// Given an x25519 [`ReusableSecret`] key, compute its corresponding [`PublicKey`].
    fn from(secret: &'a ReusableSecret) -> PublicKey {
        PublicKey((&ED25519_BASEPOINT_TABLE * &secret.0).to_montgomery())
    }
}

/// A Diffie-Hellman secret key that can be used to compute multiple [`SharedSecret`]s.
///
/// This type is identical to the [`EphemeralSecret`] type, except that the
/// [`StaticSecret::diffie_hellman`] method does not consume the secret key, and the type provides
/// serialization methods to save and load key material.  This means that the secret may be used
/// multiple times (but does not *have to be*).
///
/// # Warning
///
/// If you're uncertain about whether you should use this, then you likely
/// should not be using this.  Our strongly recommended advice is to use
/// [`EphemeralSecret`] at all times, as that type enforces at compile-time that
/// secret keys are never reused, which can have very serious security
/// implications for many protocols.
#[cfg_attr(feature = "serde", serde(crate = "our_serde"))]
#[cfg_attr(
    feature = "serde",
    derive(our_serde::Serialize, our_serde::Deserialize)
)]
#[derive(Clone, Zeroize)]
#[zeroize(drop)]
pub struct StaticSecret(
    #[cfg_attr(feature = "serde", serde(with = "AllowUnreducedScalarBytes"))] pub(crate) Scalar,
);

impl StaticSecret {
    /// Perform a Diffie-Hellman key agreement between `self` and
    /// `their_public` key to produce a `SharedSecret`.
    pub fn diffie_hellman(&self, their_public: &PublicKey) -> SharedSecret {
        SharedSecret(&self.0 * their_public.0)
    }

    /// Generate an x25519 key.
    pub fn new<T: RngCore + CryptoRng>(mut csprng: T) -> Self {
        let mut bytes = [0u8; 32];

        csprng.fill_bytes(&mut bytes);

        StaticSecret(clamp_scalar(bytes))
    }

    /// Extract this key's bytes for serialization.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.to_bytes()
    }
}

impl From<[u8; 32]> for StaticSecret {
    /// Load a secret key from a byte array.
    fn from(bytes: [u8; 32]) -> StaticSecret {
        StaticSecret(clamp_scalar(bytes))
    }
}

impl<'a> From<&'a StaticSecret> for PublicKey {
    /// Given an x25519 [`StaticSecret`] key, compute its corresponding [`PublicKey`].
    fn from(secret: &'a StaticSecret) -> PublicKey {
        PublicKey((&ED25519_BASEPOINT_TABLE * &secret.0).to_montgomery())
    }
}

/// The result of a Diffie-Hellman key exchange.
///
/// Each party computes this using their [`EphemeralSecret`] or [`StaticSecret`] and their
/// counterparty's [`PublicKey`].
#[derive(Zeroize)]
#[zeroize(drop)]
pub struct SharedSecret(pub(crate) MontgomeryPoint);

impl SharedSecret {
    /// Convert this shared secret to a byte array.
    #[inline]
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.to_bytes()
    }

    /// View this shared secret key as a byte array.
    #[inline]
    pub fn as_bytes(&self) -> &[u8; 32] {
        self.0.as_bytes()
    }

    /// Ensure in constant-time that this shared secret did not result from a
    /// key exchange with non-contributory behaviour.
    ///
    /// In some more exotic protocols which need to guarantee "contributory"
    /// behaviour for both parties, that is, that each party contibuted a public
    /// value which increased the security of the resulting shared secret.
    /// To take an example protocol attack where this could lead to undesireable
    /// results [from Thái "thaidn" Dương](https://vnhacker.blogspot.com/2015/09/why-not-validating-curve25519-public.html):
    ///
    /// > If Mallory replaces Alice's and Bob's public keys with zero, which is
    /// > a valid Curve25519 public key, he would be able to force the ECDH
    /// > shared value to be zero, which is the encoding of the point at infinity,
    /// > and thus get to dictate some publicly known values as the shared
    /// > keys. It still requires an active man-in-the-middle attack to pull the
    /// > trick, after which, however, not only Mallory can decode Alice's data,
    /// > but everyone too! It is also impossible for Alice and Bob to detect the
    /// > intrusion, as they still share the same keys, and can communicate with
    /// > each other as normal.
    ///
    /// The original Curve25519 specification argues that checks for
    /// non-contributory behaviour are "unnecessary for Diffie-Hellman".
    /// Whether this check is necessary for any particular given protocol is
    /// often a matter of debate, which we will not re-hash here, but simply
    /// cite some of the [relevant] [public] [discussions].
    ///
    /// # Returns
    ///
    /// Returns `true` if the key exchange was contributory (good), and `false`
    /// otherwise (can be bad for some protocols).
    ///
    /// [relevant]: https://tools.ietf.org/html/rfc7748#page-15
    /// [public]: https://vnhacker.blogspot.com/2015/09/why-not-validating-curve25519-public.html
    /// [discussions]: https://vnhacker.blogspot.com/2016/08/the-internet-of-broken-protocols.html
    #[must_use]
    pub fn was_contributory(&self) -> bool {
        !self.0.is_identity()
    }
}

/// "Decode" a scalar from a 32-byte array.
///
/// By "decode" here, what is really meant is applying key clamping by twiddling
/// some bits.
///
/// # Returns
///
/// A `Scalar`.
fn clamp_scalar(mut scalar: [u8; 32]) -> Scalar {
    scalar[0] &= 248;
    scalar[31] &= 127;
    scalar[31] |= 64;

    Scalar::from_bits(scalar)
}

/// The bare, byte-oriented x25519 function, exactly as specified in RFC7748.
///
/// This can be used with [`X25519_BASEPOINT_BYTES`] for people who
/// cannot use the better, safer, and faster ephemeral DH API.
///
/// # Example
/// ```
/// # extern crate rand_core;
/// #
/// use rand_core::OsRng;
/// use rand_core::RngCore;
///
/// use x25519_dalek::x25519;
/// use x25519_dalek::StaticSecret;
/// use x25519_dalek::PublicKey;
///
/// // Generate Alice's key pair.
/// let alice_secret = StaticSecret::new(&mut OsRng);
/// let alice_public = PublicKey::from(&alice_secret);
///
/// // Generate Bob's key pair.
/// let bob_secret = StaticSecret::new(&mut OsRng);
/// let bob_public = PublicKey::from(&bob_secret);
///
/// // Alice and Bob should now exchange their public keys.
///
/// // Once they've done so, they may generate a shared secret.
/// let alice_shared = x25519(alice_secret.to_bytes(), bob_public.to_bytes());
/// let bob_shared = x25519(bob_secret.to_bytes(), alice_public.to_bytes());
///
/// assert_eq!(alice_shared, bob_shared);
/// ```
pub fn x25519(k: [u8; 32], u: [u8; 32]) -> [u8; 32] {
    (clamp_scalar(k) * MontgomeryPoint(u)).to_bytes()
}

/// The X25519 basepoint, for use with the bare, byte-oriented x25519
/// function.  This is provided for people who cannot use the typed
/// DH API for some reason.
pub const X25519_BASEPOINT_BYTES: [u8; 32] = [
    9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
];

/// Derived serialization methods will not work on a StaticSecret because x25519 requires
/// non-canonical scalars which are rejected by curve25519-dalek. Thus we provide a way to convert
/// the bytes directly to a scalar using Serde's remote derive functionality.
#[cfg_attr(feature = "serde", serde(crate = "our_serde"))]
#[cfg_attr(
    feature = "serde",
    derive(our_serde::Serialize, our_serde::Deserialize)
)]
#[cfg_attr(feature = "serde", serde(remote = "Scalar"))]
struct AllowUnreducedScalarBytes(
    #[cfg_attr(feature = "serde", serde(getter = "Scalar::to_bytes"))] [u8; 32],
);
impl From<AllowUnreducedScalarBytes> for Scalar {
    fn from(bytes: AllowUnreducedScalarBytes) -> Scalar {
        clamp_scalar(bytes.0)
    }
}
