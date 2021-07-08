//! Object ID (OID) representations.
//!
//! The parser does not copy oids when parsing. The [Oid struct](struct.Oid.html)
//! only has a reference to the DER encoded form of the oid.
//!
//! # The `der_parser::oid!` macro
//!
//! Since the DER encoded oids are not very readable we provide a
//! procedural macro `oid!`. The macro can be used the following ways:
//!
//! - `oid!(1.4.42.23)`: Create a const expression for the corresponding `Oid<'static>`
//! - `oid!(rel 42.23)`: Create a const expression for the corresponding relative `Oid<'static>`
//! - `oid!(raw 1.4.42.23)`/`oid!(raw rel 42.23)`: Obtain the DER encoded form as a byte array.
//!
//! # Comparing oids
//!
//! Comparing a parsed oid to a static oid is probably the most common
//! thing done with oids in your code. The `oid!` macro can be used in expression positions for
//! this purpose. For example
//! ```
//! use der_parser::{oid, oid::Oid};
//!
//! # let some_oid: Oid<'static> = oid!(1.2.456);
//! const SOME_STATIC_OID: Oid<'static> = oid!(1.2.456);
//! assert_eq!(some_oid, SOME_STATIC_OID)
//! ```
//! To get a relative Oid use `oid!(rel 1.2)`.
//!
//! Because of limitations for procedural macros ([rust issue](https://github.com/rust-lang/rust/issues/54727))
//! and constants used in patterns ([rust issue](https://github.com/rust-lang/rust/issues/31434))
//! the `oid` macro can not directly be used in patterns, also not through constants.
//! You can do this, though:
//! ```
//! # use der_parser::{oid, oid::Oid};
//! # let some_oid: Oid<'static> = oid!(1.2.456);
//! const SOME_OID: Oid<'static> = oid!(1.2.456);
//! if some_oid == SOME_OID || some_oid == oid!(1.2.456) {
//!     println!("match");
//! }
//!
//! // Alternatively, compare the DER encoded form directly:
//! const SOME_OID_RAW: &[u8] = &oid!(raw 1.2.456);
//! match some_oid.bytes() {
//!     SOME_OID_RAW => println!("match"),
//!     _ => panic!("no match"),
//! }
//! ```
//! *Attention*, be aware that the latter version might not handle the case of a relative oid correctly. An
//! extra check might be necessary.
use std::borrow::Cow;
use std::convert::From;
use std::fmt;
use std::iter::{ExactSizeIterator, FusedIterator, Iterator};
use std::ops::Shl;
use std::str::FromStr;

#[cfg(feature = "bigint")]
use num_bigint::BigUint;
use num_traits::Num;

#[derive(Debug)]
pub enum ParseError {
    TooShort,
    /// Signalizes that the first or second component is too large.
    /// The first must be within the range 0 to 6 (inclusive).
    /// The second component must be less than 40.
    FirstComponentsTooLarge,
    ParseIntError,
}

/// Object ID (OID) representation which can be relative or non-relative.
/// An example for an oid in string representation is "1.2.840.113549.1.1.5".
///
/// For non-relative oids restrictions apply to the first two components.
///
/// This library contains a procedural macro `oid` which can be used to
/// create oids. For example `oid!(1.2.44.233)` or `oid!(rel 44.233)`
/// for relative oids. See the [module documentation](index.html) for more information.
#[derive(Hash, PartialEq, Eq, Clone)]
pub struct Oid<'a> {
    asn1: Cow<'a, [u8]>,
    pub relative: bool,
}

fn encode_relative(ids: &'_ [u64]) -> impl Iterator<Item = u8> + '_ {
    ids.iter()
        .map(|id| {
            let bit_count = 64 - id.leading_zeros();
            let octets_needed = ((bit_count + 6) / 7).max(1);
            (0..octets_needed).map(move |i| {
                let flag = if i == octets_needed - 1 { 0 } else { 1 << 7 };
                ((id >> (7 * (octets_needed - 1 - i))) & 0b111_1111) as u8 | flag
            })
        })
        .flatten()
}

impl<'a> Oid<'a> {
    /// Create an OID from the ASN.1 DER encoded form. See the [module documentation](index.html)
    /// for other ways to create oids.
    pub const fn new(asn1: Cow<'a, [u8]>) -> Oid {
        Oid {
            asn1,
            relative: false,
        }
    }

    /// Create a relative OID from the ASN.1 DER encoded form. See the [module documentation](index.html)
    /// for other ways to create relative oids.
    pub const fn new_relative(asn1: Cow<'a, [u8]>) -> Oid {
        Oid {
            asn1,
            relative: true,
        }
    }

    /// Build an OID from an array of object identifier components.
    /// This method allocates memory on the heap.
    // we do not use .copied() for compatibility with 1.34
    #[allow(clippy::map_clone)]
    pub fn from<'b>(s: &'b [u64]) -> Result<Oid<'static>, ParseError> {
        if s.len() < 2 {
            if s.len() == 1 && s[0] == 0 {
                return Ok(Oid {
                    asn1: Cow::Borrowed(&[0]),
                    relative: false,
                });
            }
            return Err(ParseError::TooShort);
        }
        if s[0] >= 7 || s[1] >= 40 {
            return Err(ParseError::FirstComponentsTooLarge);
        }
        let asn1_encoded: Vec<u8> = [(s[0] * 40 + s[1]) as u8]
            .iter()
            .map(|&x| x)
            .chain(encode_relative(&s[2..]))
            .collect();
        Ok(Oid {
            asn1: Cow::from(asn1_encoded),
            relative: false,
        })
    }

    /// Build a relative OID from an array of object identifier components.
    pub fn from_relative<'b>(s: &'b [u64]) -> Result<Oid<'static>, ParseError> {
        if s.is_empty() {
            return Err(ParseError::TooShort);
        }
        let asn1_encoded: Vec<u8> = encode_relative(s).collect();
        Ok(Oid {
            asn1: Cow::from(asn1_encoded),
            relative: true,
        })
    }

    /// Create a deep copy of the oid.
    ///
    /// This method allocates data on the heap. The returned oid
    /// can be used without keeping the ASN.1 representation around.
    ///
    /// Cloning the returned oid does again allocate data.
    pub fn to_owned(&self) -> Oid<'static> {
        Oid {
            asn1: Cow::from(self.asn1.to_vec()),
            relative: self.relative,
        }
    }

    /// Get the encoded oid without the header.
    pub fn bytes(&self) -> &[u8] {
        self.asn1.as_ref()
    }

    /// Convert the OID to a string representation.
    /// The string contains the IDs separated by dots, for ex: "1.2.840.113549.1.1.5"
    #[cfg(feature = "bigint")]
    pub fn to_id_string(&self) -> String {
        let ints: Vec<String> = self.iter_bigint().map(|i| i.to_string()).collect();
        ints.join(".")
    }

    #[cfg(not(feature = "bigint"))]
    /// Convert the OID to a string representation.
    ///
    /// If every arc fits into a u64 a string like "1.2.840.113549.1.1.5"
    /// is returned, otherwise a hex representation.
    ///
    /// See also the "bigint" feature of this crate.
    pub fn to_id_string(&self) -> String {
        if let Some(arcs) = self.iter() {
            let ints: Vec<String> = arcs.map(|i| i.to_string()).collect();
            ints.join(".")
        } else {
            let mut ret = String::with_capacity(self.asn1.len() * 3);
            for (i, o) in self.asn1.iter().enumerate() {
                ret.push_str(&format!("{:02x}", o));
                if i + 1 != self.asn1.len() {
                    ret.push(' ');
                }
            }
            ret
        }
    }

    /// Return an iterator over the sub-identifiers (arcs).
    #[cfg(feature = "bigint")]
    pub fn iter_bigint(
        &'_ self,
    ) -> impl Iterator<Item = BigUint> + FusedIterator + ExactSizeIterator + '_ {
        SubIdentifierIterator {
            oid: &self,
            pos: 0,
            first: false,
            n: std::marker::PhantomData,
        }
    }

    /// Return an iterator over the sub-identifiers (arcs).
    /// Returns `None` if at least one arc does not fit into `u64`.
    pub fn iter(
        &'_ self,
    ) -> Option<impl Iterator<Item = u64> + FusedIterator + ExactSizeIterator + '_> {
        // Check that every arc fits into u64
        let bytes = if self.relative {
            &self.asn1
        } else if self.asn1.is_empty() {
            &[]
        } else {
            &self.asn1[1..]
        };
        let max_bits = bytes
            .iter()
            .fold((0usize, 0usize), |(max, cur), c| {
                let is_end = (c >> 7) == 0u8;
                if is_end {
                    (max.max(cur + 7), 0)
                } else {
                    (max, cur + 7)
                }
            })
            .0;
        if max_bits > 64 {
            return None;
        }

        Some(SubIdentifierIterator {
            oid: &self,
            pos: 0,
            first: false,
            n: std::marker::PhantomData,
        })
    }
}

trait Repr: Num + Shl<usize, Output = Self> + From<u8> {}
impl<N> Repr for N where N: Num + Shl<usize, Output = N> + From<u8> {}

struct SubIdentifierIterator<'a, N: Repr> {
    oid: &'a Oid<'a>,
    pos: usize,
    first: bool,
    n: std::marker::PhantomData<&'a N>,
}

impl<'a, N: Repr> Iterator for SubIdentifierIterator<'a, N> {
    type Item = N;

    fn next(&mut self) -> Option<Self::Item> {
        use num_traits::identities::Zero;

        if self.pos == self.oid.asn1.len() {
            return None;
        }
        if !self.oid.relative {
            if !self.first {
                debug_assert!(self.pos == 0);
                self.first = true;
                return Some((self.oid.asn1[0] / 40).into());
            } else if self.pos == 0 {
                self.pos += 1;
                if self.oid.asn1[0] == 0 && self.oid.asn1.len() == 1 {
                    return None;
                }
                return Some((self.oid.asn1[0] % 40).into());
            }
        }
        // decode objet sub-identifier according to the asn.1 standard
        let mut res = <N as Zero>::zero();
        for o in self.oid.asn1[self.pos..].iter() {
            self.pos += 1;
            res = (res << 7) + (o & 0b111_1111).into();
            let flag = o >> 7;
            if flag == 0u8 {
                break;
            }
        }
        Some(res)
    }
}

impl<'a, N: Repr> FusedIterator for SubIdentifierIterator<'a, N> {}

impl<'a, N: Repr> ExactSizeIterator for SubIdentifierIterator<'a, N> {
    fn len(&self) -> usize {
        if self.oid.relative {
            self.oid.asn1.iter().filter(|o| (*o >> 7) == 0u8).count()
        } else if self.oid.asn1.len() == 0 {
            0
        } else if self.oid.asn1.len() == 1 {
            if self.oid.asn1[0] == 0 {
                1
            } else {
                2
            }
        } else {
            2 + self.oid.asn1[2..]
                .iter()
                .filter(|o| (*o >> 7) == 0u8)
                .count()
        }
    }

    #[cfg(feature = "exact_size_is_empty")]
    fn is_empty(&self) -> bool {
        self.oid.asn1.is_empty()
    }
}

impl<'a> fmt::Display for Oid<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.relative {
            f.write_str("rel. ")?;
        }
        f.write_str(&self.to_id_string())
    }
}

impl<'a> fmt::Debug for Oid<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("OID(")?;
        <Oid as fmt::Display>::fmt(self, f)?;
        f.write_str(")")
    }
}

impl<'a> FromStr for Oid<'a> {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let v: Result<Vec<_>, _> = s.split('.').map(|c| c.parse::<u64>()).collect();
        v.map_err(|_| ParseError::ParseIntError)
            .and_then(|v| Oid::from(&v))
    }
}

#[cfg(test)]
mod tests {
    use crate::oid::Oid;
    use std::borrow::Cow;
    use std::str::FromStr;

    #[test]
    fn test_oid_fmt() {
        let oid = Oid::from(&[1, 2, 840, 113_549, 1, 1, 5]).unwrap();
        assert_eq!(format!("{}", oid), "1.2.840.113549.1.1.5".to_owned());
        assert_eq!(format!("{:?}", oid), "OID(1.2.840.113549.1.1.5)".to_owned());

        let oid = Oid::from_relative(&[840, 113_549, 1, 1, 5]).unwrap();
        let byte_ref = [0x86, 0x48, 0x86, 0xf7, 0x0d, 1, 1, 5];
        assert_eq!(byte_ref.as_ref(), oid.asn1.as_ref());
        assert_eq!(format!("{}", oid), "rel. 840.113549.1.1.5".to_owned());
        assert_eq!(
            format!("{:?}", oid),
            "OID(rel. 840.113549.1.1.5)".to_owned()
        );
    }

    #[test]
    fn test_iter_len() {
        #[cfg(feature = "bigint")]
        {
            assert_eq!(Oid::new(Cow::Borrowed(&[])).iter_bigint().len(), 0);
            assert_eq!(Oid::from(&[0]).unwrap().iter_bigint().len(), 1);
            assert_eq!(Oid::from(&[1, 2]).unwrap().iter_bigint().len(), 2);
            assert_eq!(
                Oid::from(&[1, 29, 459, 342]).unwrap().iter_bigint().len(),
                4
            );
            assert_eq!(
                Oid::from_relative(&[459, 342]).unwrap().iter_bigint().len(),
                2
            );
        }
        {
            assert_eq!(Oid::new(Cow::Borrowed(&[])).iter().unwrap().len(), 0);
            assert_eq!(Oid::from(&[0]).unwrap().iter().unwrap().len(), 1);
            assert_eq!(Oid::from(&[1, 2]).unwrap().iter().unwrap().len(), 2);
            assert_eq!(
                Oid::from(&[1, 29, 459, 342]).unwrap().iter().unwrap().len(),
                4
            );
            assert_eq!(
                Oid::from_relative(&[459, 342])
                    .unwrap()
                    .iter()
                    .unwrap()
                    .len(),
                2
            );
        }
    }

    #[test]
    fn test_oid_from_str() {
        let oid_ref = Oid::from(&[1, 2, 840, 113_549, 1, 1, 5]).unwrap();
        let byte_ref = [42, 0x86, 0x48, 0x86, 0xf7, 0x0d, 1, 1, 5];
        let oid = Oid::from_str("1.2.840.113549.1.1.5").unwrap();
        assert_eq!(byte_ref.as_ref(), oid.asn1.as_ref());
        assert_eq!(oid_ref, oid);
    }

    /// This test case will test an OID beginning with two zero
    /// subidentifiers (literally: "itu-t recommendation"), as
    /// used for example in the TCAP (Q.773) specification.

    #[test]
    fn test_itu_t_rec_oid() {
        let oid = Oid::from(&[0, 0, 17, 773, 1, 1, 1]).unwrap();
        assert_eq!(format!("{}", oid), "0.0.17.773.1.1.1".to_owned());
        assert_eq!(format!("{:?}", oid), "OID(0.0.17.773.1.1.1)".to_owned());
    }

    #[test]
    fn test_zero_oid() {
        #[cfg(feature = "bigint")]
        {
            use num_bigint::BigUint;
            use num_traits::FromPrimitive;

            let oid_raw = Oid::new(Cow::Borrowed(&[0]));
            let ids: Vec<BigUint> = oid_raw.iter_bigint().collect();
            assert_eq!(vec![BigUint::from_u8(0).unwrap()], ids);
            assert_eq!(oid_raw.iter_bigint().len(), 1);
        }
        {
            let oid_raw = Oid::new(Cow::Borrowed(&[0]));
            let ids: Vec<u64> = oid_raw.iter().unwrap().collect();
            assert_eq!(vec![0], ids);
            assert_eq!(oid_raw.iter().unwrap().len(), 1);
        }
        let oid_from = Oid::from(&[0]).unwrap();
        assert_eq!(oid_from.asn1.as_ref(), &[0]);
    }
}
