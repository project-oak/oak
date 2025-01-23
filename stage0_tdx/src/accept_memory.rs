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

use core::sync::atomic::Ordering;

use x86_64::{
    structures::paging::{frame::PhysFrameRange, page::NotGiantPageSize, PhysFrame, Size4KiB},
    PhysAddr,
};

pub mod counters {
    use core::sync::atomic::AtomicUsize;

    /// Number of FAIL_SIZEMISMATCH errors when invoking TDG.MEM.PAGE.ACCEPT on
    /// 2 MiB pages.
    pub static ERROR_FAIL_SIZE_MISMATCH: AtomicUsize = AtomicUsize::new(0);

    /// Number of successful TDG.MEM.PAGE.ACCEPT invocations on 2 MiB pages.
    pub static ACCEPTED_2M: AtomicUsize = AtomicUsize::new(0);

    /// Number of successful TDG.MEM.PAGE.ACCEPT invocations on 4 KiB pages.
    pub static ACCEPTED_4K: AtomicUsize = AtomicUsize::new(0);
}

pub trait TdAcceptPage {
    fn accept_page(&self) -> Result<(), &'static str>;
}

impl<S: NotGiantPageSize + oak_tdx_guest::tdcall::TdxSize> TdAcceptPage for PhysFrameRange<S> {
    fn accept_page(&self) -> Result<(), &'static str> {
        for frame in *self {
            if frame.size() == 4096 {
                oak_tdx_guest::tdcall::accept_memory(frame).expect("map 4k cannot fail");
                counters::ACCEPTED_4K.fetch_add(1, Ordering::SeqCst);
            } else {
                use oak_tdx_guest::tdcall::AcceptMemoryError;
                match oak_tdx_guest::tdcall::accept_memory(frame) {
                    Ok(()) => {
                        counters::ACCEPTED_2M.fetch_add(1, Ordering::SeqCst);
                    }
                    Err(AcceptMemoryError::AlreadyAccepted) => continue,
                    Err(AcceptMemoryError::PageSizeMisMatch) => {
                        // cannot accept as 2MiB. let's try 4KiB
                        counters::ERROR_FAIL_SIZE_MISMATCH.fetch_add(1, Ordering::SeqCst);
                        let start_addr_u64 = frame.start_address().as_u64();
                        let limit_addr_u64 = start_addr_u64 + 2 * 1024 * 1024;
                        let start_address = PhysAddr::new(start_addr_u64);
                        let limit = PhysAddr::new(limit_addr_u64);
                        let range = PhysFrame::<Size4KiB>::range(
                            PhysFrame::from_start_address(start_address).unwrap(),
                            PhysFrame::from_start_address(limit).unwrap(),
                        );
                        range.accept_page().unwrap();
                    }
                    _ => {
                        // InvalidOperandInRcx or OperandBusy
                        panic!("oops");
                    }
                }
            }
        }

        Ok(())
    }
}
