//
// Copyright 2023 The Project Oak Authors
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

use super::fd::copy_max_slice;

#[test]
fn shorter_dst_copy() {
    let src: &[u8; 6] = &[0, 1, 2, 3, 4, 5];
    let dst: &mut [u8; 5] = &mut [0; 5];
    let length = copy_max_slice(src, dst);
    assert_eq!(length, 5);
    assert_eq!(dst, &[0, 1, 2, 3, 4])
}

#[test]
fn longer_dst_copy() {
    let src: &[u8; 6] = &[0, 1, 2, 3, 4, 5];
    let dst: &mut [u8; 8] = &mut [0; 8];
    let length = copy_max_slice(src, dst);
    assert_eq!(length, 5);
    assert_eq!(dst, &[0, 1, 2, 3, 4, 5, 0, 0])
}

#[test]
fn empty_copy() {
    let src: &[u8; 0] = &[];
    let dst: &mut [u8; 5] = &mut [1; 5];
    let length = copy_max_slice(src, dst);
    assert_eq!(length, 0);
    assert_eq!(dst, &[1; 5])
}
