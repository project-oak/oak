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

use std::collections::VecDeque;

use bytes::{Buf, Bytes};

/// Buffer that is backed by non-contiguous slices of memory.
///
/// The purpose of this struct is to provide a way to iterate over the data in
/// order (hence it implements `bytes::Buf`) but without having to copy all the
/// data into one contiguous slice of memory, as it would be the case for `Vec`.
///
/// This is similar to what bytes::Chain would achieve, but without the number
/// of buffers leaking into the types.
#[derive(Clone, Default)]
pub struct Buffer {
    // VecDeque so that appends would be cheap; Bytes so that clone() would be (relatively) cheap.
    buffers: VecDeque<Bytes>,

    // Current buffer for iteration.
    index: usize,
}

impl Buffer {
    pub fn new() -> Self {
        Self { buffers: VecDeque::new(), index: 0 }
    }

    pub fn push_back(&mut self, buffer: Bytes) {
        self.buffers.push_back(buffer);
    }
}

impl Buf for Buffer {
    fn remaining(&self) -> usize {
        if self.index > self.buffers.len() {
            0
        } else {
            self.buffers.range(self.index..).map(|cur| cur.remaining()).sum()
        }
    }

    fn chunk(&self) -> &[u8] {
        self.buffers.get(self.index).map(|cur| cur.chunk()).unwrap_or(&[])
    }

    fn advance(&mut self, mut cnt: usize) {
        while self.index < self.buffers.len() && cnt >= self.buffers[self.index].remaining() {
            cnt -= self.buffers[self.index].remaining();
            self.index += 1;
        }

        // If we advance to remaining(), don't crash, as now the index is now past the
        // boundary.
        if self.index < self.buffers.len() {
            self.buffers[self.index].advance(cnt);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple() {
        let mut buf = Buffer::new();
        buf.push_back(Bytes::from_static(b"Hello world"));
        assert_eq!(buf.remaining(), 11);
        assert_eq!(buf.chunk(), &b"Hello world"[..]);
        buf.advance(6);
        assert_eq!(buf.chunk(), &b"world"[..]);
    }

    #[test]
    fn test_two() {
        let mut buf = Buffer::new();
        buf.push_back(Bytes::from_static(b"Hello "));
        buf.push_back(Bytes::from_static(b"world"));
        assert_eq!(buf.remaining(), 11);
        assert_eq!(buf.chunk(), &b"Hello "[..]);
        buf.advance(6);
        assert_eq!(buf.remaining(), 5);
        assert_eq!(buf.chunk(), &b"world"[..]);
        buf.advance(5);
        assert_eq!(buf.remaining(), 0);
    }
}
