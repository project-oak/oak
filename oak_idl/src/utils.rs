// Copyright 2022 The Project Oak Authors
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

//! Utilities for improving the ergonomics of FlatBuffers in Rust.

use alloc::vec::Vec;
use core::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

/// A helper struct to facilitate building a [`OwnedFlatbuffer`].
///
/// [`OwnedFlatbufferBuilder`] delegates to the underlying [`flatbuffers::FlatBufferBuilder`]
/// instance, and it adds a [`OwnedFlatbufferBuilder::finish`] method that returns a completed
/// [`OwnedFlatbuffer`] instance which owns the underlying buffer.
///
/// We need to have an instance of [`PhantomData`] in the struct in order to use the type paramter
/// `T`.
///
/// ```
/// # struct Request<'a> {
/// #     pub _tab: flatbuffers::Table<'a>,
/// # };
/// #
/// # impl flatbuffers::Verifiable for Request<'_> {
/// #     fn run_verifier(
/// #         v: &mut flatbuffers::Verifier,
/// #         pos: usize,
/// #     ) -> Result<(), flatbuffers::InvalidFlatbuffer> {
/// #         Ok(())
/// #     }
/// # }
/// #
/// # impl<'a> flatbuffers::Follow<'a> for Request<'a> {
/// #     type Inner = Self;
/// #     fn follow(buf: &'a [u8], loc: usize) -> Self::Inner {
/// #         Self {
/// #             _tab: flatbuffers::Table { buf, loc },
/// #         }
/// #     }
/// # }
/// #
/// # impl Request<'_> {
/// #     pub fn create<'bldr: 'args, 'args:'mut_bldr, 'mut_bldr>(b: &'mut_bldr mut flatbuffers::FlatBufferBuilder<'bldr>,
/// #      args: &'args RequestArgs<'args>) -> flatbuffers::WIPOffset<Request<'bldr>> {
/// #         flatbuffers::WIPOffset::new(0)
/// #     }
/// # }
/// #
/// # pub struct RequestArgs<'a> {
/// #     pub value: Option<flatbuffers::WIPOffset<flatbuffers::Vector<'a, u8>>>,
/// # }
/// #
/// let mut b = oak_idl::utils::OwnedFlatbufferBuilder::<Request>::default();
/// let v = b.create_vector::<u8>(&[14, 12]);
/// let req = Request::create(&mut b, &RequestArgs {
///     value: Some(v),
/// });
/// let m = b.finish(req);
/// ```
pub struct OwnedFlatbufferBuilder<'a, T> {
    buf: flatbuffers::FlatBufferBuilder<'a>,
    _phantom: PhantomData<T>,
}

impl<'a, T: flatbuffers::Verifiable + flatbuffers::Follow<'a>> Default
    for OwnedFlatbufferBuilder<'a, T>
{
    fn default() -> Self {
        Self {
            buf: flatbuffers::FlatBufferBuilder::default(),
            _phantom: PhantomData,
        }
    }
}

impl<'a, T: flatbuffers::Verifiable + flatbuffers::Follow<'a>> OwnedFlatbufferBuilder<'a, T> {
    pub fn finish(
        self,
        offset: flatbuffers::WIPOffset<T>,
    ) -> Result<OwnedFlatbuffer<T>, flatbuffers::InvalidFlatbuffer> {
        let mut s = self;
        s.buf.finish(offset, None);
        OwnedFlatbuffer::from_vec(s.buf.finished_data().to_vec())
    }
}

/// Delegate to the underlying [`OwnedFlatbufferBuilder`].
impl<'a, T> Deref for OwnedFlatbufferBuilder<'a, T> {
    type Target = flatbuffers::FlatBufferBuilder<'a>;

    fn deref(&self) -> &Self::Target {
        &self.buf
    }
}

/// Delegate to the underlying [`OwnedFlatbufferBuilder`].
impl<'a, T> DerefMut for OwnedFlatbufferBuilder<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.buf
    }
}

/// An owned flatbuffer message, which owns the underlying buffer.
#[derive(Debug)]
pub struct OwnedFlatbuffer<T> {
    buf: Vec<u8>,
    _phantom: PhantomData<T>,
}

impl<T: flatbuffers::Verifiable> OwnedFlatbuffer<T> {
    pub fn from_vec(buf: Vec<u8>) -> Result<Self, flatbuffers::InvalidFlatbuffer> {
        use flatbuffers::Verifiable;
        let opts = flatbuffers::VerifierOptions::default();
        let mut v = flatbuffers::Verifier::new(&opts, &buf);
        <flatbuffers::ForwardsUOffset<T>>::run_verifier(&mut v, 0)?;
        Ok(Self {
            buf,
            _phantom: PhantomData,
        })
    }
}

impl<T> OwnedFlatbuffer<T> {
    /// Returns a reference to the underlying owned buffer.
    pub fn buf(&self) -> &[u8] {
        &self.buf
    }
    /// Returns the underlying owned buffer.
    pub fn into_vec(self) -> Vec<u8> {
        self.buf
    }
}

impl<'a, T: flatbuffers::Follow<'a> + flatbuffers::Verifiable> OwnedFlatbuffer<T> {
    /// Returns a reference to the flatbuffer object, pointing within the underlying owned buffer.
    pub fn get(&'a self) -> T::Inner {
        flatbuffers::root::<T>(&self.buf).unwrap()
    }
}
