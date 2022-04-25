// Copyright © 2019 Intel Corporation
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

// SAFETY: Requires that addr point to a static, null-terminated C-string.
// The returned slice does not include the null-terminator.
pub unsafe fn from_cstring(addr: u64) -> &'static [u8] {
    if addr == 0 {
        return &[];
    }
    let start = addr as *const u8;
    let mut size: usize = 0;
    while start.add(size).read() != 0 {
        size += 1;
    }
    core::slice::from_raw_parts(start, size)
}
