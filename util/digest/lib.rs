//
// Copyright 2025 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

//! Provides native Rust structs around digests and related conversion:
//!
//!   Digest:
//!       An enum capturing the result of common hashing algorithms.

#![no_std]

extern crate alloc;

use alloc::vec::Vec;

use sha2::{
    Digest as Sha2DigestTrait, Sha256 as Sha256Hasher, Sha384 as Sha384Hasher,
    Sha512 as Sha512Hasher,
};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sha1([u8; 20]);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sha256([u8; 32]);

impl Sha256 {
    pub fn from_contents(input: &[u8]) -> Self {
        let mut hasher = Sha256Hasher::new();
        hasher.update(input);
        Self(hasher.finalize().into())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sha384([u8; 48]);

impl Sha384 {
    pub fn from_contents(input: &[u8]) -> Self {
        let mut hasher = Sha384Hasher::new();
        hasher.update(input);
        Self(hasher.finalize().into())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sha512([u8; 64]);

impl Sha512 {
    pub fn from_contents(input: &[u8]) -> Self {
        let mut hasher = Sha512Hasher::new();
        hasher.update(input);
        Self(hasher.finalize().into())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sha3_224([u8; 28]);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sha3_256([u8; 32]);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sha3_384([u8; 48]);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sha3_512([u8; 64]);

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Psha2(Vec<u8>);

impl Psha2 {
    pub fn from_contents(_input: &[u8]) -> Self {
        todo!("unimplemented")
    }
}

impl From<[u8; 20]> for Sha1 {
    fn from(v: [u8; 20]) -> Self {
        Self(v)
    }
}
impl From<[u8; 32]> for Sha256 {
    fn from(v: [u8; 32]) -> Self {
        Self(v)
    }
}
impl From<[u8; 48]> for Sha384 {
    fn from(v: [u8; 48]) -> Self {
        Self(v)
    }
}
impl From<[u8; 64]> for Sha512 {
    fn from(v: [u8; 64]) -> Self {
        Self(v)
    }
}
impl From<[u8; 28]> for Sha3_224 {
    fn from(v: [u8; 28]) -> Self {
        Self(v)
    }
}
impl From<[u8; 32]> for Sha3_256 {
    fn from(v: [u8; 32]) -> Self {
        Self(v)
    }
}
impl From<[u8; 48]> for Sha3_384 {
    fn from(v: [u8; 48]) -> Self {
        Self(v)
    }
}
impl From<[u8; 64]> for Sha3_512 {
    fn from(v: [u8; 64]) -> Self {
        Self(v)
    }
}
impl From<Vec<u8>> for Psha2 {
    fn from(v: Vec<u8>) -> Self {
        Self(v)
    }
}

impl AsRef<[u8]> for Sha1 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}
impl AsRef<[u8]> for Sha256 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}
impl AsRef<[u8]> for Sha384 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}
impl AsRef<[u8]> for Sha512 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}
impl AsRef<[u8]> for Sha3_224 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}
impl AsRef<[u8]> for Sha3_256 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}
impl AsRef<[u8]> for Sha3_384 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}
impl AsRef<[u8]> for Sha3_512 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}
impl AsRef<[u8]> for Psha2 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

/// Represents a specific digest type and its (mostly) fixed-size data.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Digest {
    Sha1(Sha1),
    Psha2(Psha2),
    Sha256(Sha256),
    Sha384(Sha384),
    Sha512(Sha512),
    Sha3_224(Sha3_224),
    Sha3_256(Sha3_256),
    Sha3_384(Sha3_384),
    Sha3_512(Sha3_512),
}

impl From<Sha1> for Digest {
    fn from(h: Sha1) -> Self {
        Digest::Sha1(h)
    }
}
impl From<Psha2> for Digest {
    fn from(h: Psha2) -> Self {
        Digest::Psha2(h)
    }
}
impl From<Sha256> for Digest {
    fn from(h: Sha256) -> Self {
        Digest::Sha256(h)
    }
}
impl From<Sha384> for Digest {
    fn from(h: Sha384) -> Self {
        Digest::Sha384(h)
    }
}
impl From<Sha512> for Digest {
    fn from(h: Sha512) -> Self {
        Digest::Sha512(h)
    }
}
impl From<Sha3_224> for Digest {
    fn from(h: Sha3_224) -> Self {
        Digest::Sha3_224(h)
    }
}
impl From<Sha3_256> for Digest {
    fn from(h: Sha3_256) -> Self {
        Digest::Sha3_256(h)
    }
}
impl From<Sha3_384> for Digest {
    fn from(h: Sha3_384) -> Self {
        Digest::Sha3_384(h)
    }
}
impl From<Sha3_512> for Digest {
    fn from(h: Sha3_512) -> Self {
        Digest::Sha3_512(h)
    }
}
