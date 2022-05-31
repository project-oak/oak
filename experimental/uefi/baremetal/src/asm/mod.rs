//
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

// Even if we ask for the feature, _don't_ include the multiboot header in the
// test builds. Otherwise, the tests will fail as qemu will notice the
// multiboot header, and refuse to load the binary (as it's a 64-bit ELF binary
// and multiboot is nominally a 32-bit protocol.)

core::arch::global_asm!(include_str!("multiboot.s"), options(raw));
