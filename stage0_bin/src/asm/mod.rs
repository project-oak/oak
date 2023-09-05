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

use core::arch::global_asm;

global_asm!(
    include_str!("boot.s"),
    pml4 = sym crate::paging::PML4,
    pdpt = sym crate::paging::PDPT,
    pd_0 = sym crate::paging::PD_0,
    pd_3 = sym crate::paging::PD_3,
    options(att_syntax));
global_asm!(include_str!("ap_boot.s"), options(att_syntax, raw));
global_asm!(include_str!("reset_vector.s"), options(att_syntax, raw));
