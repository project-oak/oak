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

use core::{ffi::CStr, ops::Range};

use x86_64::align_down;
use zerocopy::IntoBytes;

use crate::{Platform, ZeroPage, fw_cfg::Firmware};

const PCI_MMIO32_HOLE_BASE_FILE_NAME: &CStr = c"etc/pci-mmio32-hole-base";
const MMCFG_MEM_RESERVATION_FILE: &CStr = c"etc/mmcfg_mem_reservation";

pub trait Machine {
    const PCI_VENDOR_ID: u16;
    const PCI_DEVICE_ID: u16;

    fn io_port_range(
        _firmware: &mut dyn Firmware,
        _zero_page: &ZeroPage,
    ) -> Result<Range<u16>, &'static str> {
        // 16-bit I/O port ranges.
        // According to SeaBIOS here:
        // https://github.com/qemu/seabios/blob/b686f4600792c504f01929f761be473e298de33d/src/fw/pciinit.c#L1009
        // there are two common port ranges, depending on how many I/O assignments we
        // will need.
        //
        // For now, hard-code the (smaller) range of 0xc000 + 0x4000.

        Ok(0xc000..0xffff)
    }

    fn mmio32_hole(
        firmware: &mut dyn Firmware,
        zero_page: &ZeroPage,
    ) -> Result<Range<u32>, &'static str>;

    fn mmio64_hole<P: Platform>(
        firmware: &mut dyn Firmware,
        zero_page: &ZeroPage,
    ) -> Result<Range<u64>, &'static str>;
}

// How much memory to reserve for the 64-bit PCI hole. When GPUs come into play,
// they want fairly large BARs -- 128 GB -- so we go for a whopping 512 GB for
// the hole. In the future we may want to make it dynamic and start the MMIO
// hole just past the end of physical memory.
const MMIO64_HOLE_SIZE: usize = 0x80_0000_0000;

pub struct I440fx {}

impl Machine for I440fx {
    const PCI_VENDOR_ID: u16 = 0x8086;
    const PCI_DEVICE_ID: u16 = 0x1237;

    fn mmio32_hole(
        firmware: &mut dyn Firmware,
        zero_page: &ZeroPage,
    ) -> Result<Range<u32>, &'static str> {
        let mut mmio32_hole_base = firmware
            .find(PCI_MMIO32_HOLE_BASE_FILE_NAME)
            .and_then(|file| {
                // The VMM is providing us the start of the hole.
                if file.size() > core::mem::size_of::<u64>() {
                    return None;
                }
                let mut hole: u64 = 0;
                // reading can fail, so now we will have an Option<Result> so that we can
                // propagate the error
                Some(firmware.read_file(&file, hole.as_mut_bytes()).and_then(|_| {
                    hole.try_into().map_err(|_| "VMM reported MMIO hole did not fit in u32")
                }))
            })
            .unwrap_or_else(|| {
                // No base from the VMM. Try to guess reasonable defaults; for this we look if
                // some well-known memory addresses are backed by real RAM or not. If not,
                // that's where we guess the hole will be.
                //
                // This mirrors what SeaBIOS is doing:
                // https://github.com/coreboot/seabios/blob/b686f4600792c504f01929f761be473e298de33d/src/fw/pciinit.c#L470
                // In EDK2, the magic happens here:
                // https://github.com/tianocore/edk2/blob/b58ce4c226768ced972bd49886e20c5ae6dfd8f0/OvmfPkg/Library/PlatformInitLib/Platform.c#L186
                // with `Uc32Base` determined here:
                // https://github.com/tianocore/edk2/blob/b58ce4c226768ced972bd49886e20c5ae6dfd8f0/OvmfPkg/Library/PlatformInitLib/MemDetect.c#L84
                //
                // SeaBIOS/EDK2 keep track of the "low" and "high" memory separately. We don't,
                // but we have a full e820 map to check whether the addresses are backed by real
                // memory or not.
                if zero_page.find_e820_entry(0x8000_0000).is_none() {
                    return Ok(0x8000_0000);
                }
                if zero_page.find_e820_entry(0xC000_0000).is_none() {
                    return Ok(0xC000_0000);
                }
                // We have no idea where the hole should go :(
                Err("could not find memory region for 32-bit PCI MMIO hole")
            })?;

        if let Some(file) = firmware.find(MMCFG_MEM_RESERVATION_FILE) {
            if file.size() <= core::mem::size_of::<u64>() {
                let mut should_reserve: u64 = 0;
                firmware.read_file(&file, should_reserve.as_mut_bytes())?;
                if should_reserve == 1 {
                    // Bump the base by 256 MoB
                    mmio32_hole_base += 0x10000000;
                }
            }
        }

        // EDK2 code:
        // https://github.com/tianocore/edk2/blob/b58ce4c226768ced972bd49886e20c5ae6dfd8f0/OvmfPkg/Library/PlatformInitLib/Platform.c#L187 (defined ad 0xFC00_0000)
        // SeaBIOS code:
        // https://github.com/coreboot/seabios/blob/b686f4600792c504f01929f761be473e298de33d/src/fw/pciinit.c#L51 (defined at 0xFEC0_0000)
        // For now we choose the lower of the two.
        let mmio32_hole_end = 0xFC00_0000;

        Ok(mmio32_hole_base..mmio32_hole_end)
    }

    fn mmio64_hole<P: Platform>(
        firmware: &mut dyn Firmware,
        zero_page: &ZeroPage,
    ) -> Result<Range<u64>, &'static str> {
        // It is possible for the host to provide PCI bridge address information in a
        // fw_cfg file, `etc/hardware-info`. EDK2 supports that mechanism, but I don't
        // see that mechanism being used in any the VMMs that immediately interest us.
        // Thus, let's kick that particular can down the road until we encounter a VMM
        // that requires us to support that mechanism.
        // But we should still print a warning if that file exists so that it wouldn't
        // come as a complete surprise.
        if firmware.find(c"etc/hardware-info").is_some() {
            log::warn!(
                "your VMM exposes `etc/hardware-info`; stage0 currently does not support parsing that file and will ignore it!"
            );
        }

        // EDK2 places the 64-bit hole at (2^(physmem_bits-3)..2^physmem_bits) (unless
        // otherwise instructed):
        //
        // https://github.com/tianocore/edk2/blob/d46aa46c8361194521391aa581593e556c707c6e/OvmfPkg/Library/PlatformInitLib/MemDetect.c#L796
        //
        // After which it moves it down if there is a conflict:
        //
        // https://github.com/tianocore/edk2/blob/d46aa46c8361194521391aa581593e556c707c6e/OvmfPkg/Library/PlatformInitLib/MemDetect.c#L809
        //
        // This is known as the "dynamic MMIO window".
        //
        // Otherwise, the window size is at least 32 GB (look for `PcdPciMmio64Size` in
        // the dsc files), the "classic MMIO window".
        //
        // SeaBIOS prefers to place the window somewhere around 512 GiB..1024 GiB mark:
        // BUILD_PCIMEM64_START = 0x80_0000_0000 (512 GB mark)
        // BUILD_PCIMEM64_END = 0x100_0000_0000 (1024 GB mark)
        // These are the build time defaults. But also see:
        // https://github.com/coreboot/seabios/blob/b686f4600792c504f01929f761be473e298de33d/src/fw/pciinit.c#L1138
        // https://github.com/coreboot/seabios/blob/b686f4600792c504f01929f761be473e298de33d/src/fw/pciinit.c#L1157
        //
        // Let's make some simplifying assumptions and try to fit a 32 GiB window
        // somewhere at the top of the available physical memory. You'd hope we can just
        // assume (at least) 48 bits available, but no.

        // We've now run into a VM where CPUID reports 48 bits of physical address
        // space, but the VMM is only backing it with 41.6 bits of address space, and we
        // place the MMIO range outside of what the VMM supports.
        //
        // Oops.
        //
        // We'll have to come back to this and figure out how to see through the VMM's
        // lies, but for now, let's lie and say 41 bits. As 40 bits is 1 TiB, we can fit
        // a fairly large MMIO range in the upper TiB.
        let addr_size = 41;
        //let addr_size = P::guest_phys_addr_size();
        let top_of_memory: u64 = 1 << addr_size;

        // The hole should be aligned to 1G addresses. With enough bits, that should be
        // vacuously true, but just in case let's ensure that the top_of_memory is a
        // multiple of the hole size.
        let top_of_memory = align_down(top_of_memory, MMIO64_HOLE_SIZE as u64) as usize;

        // Let's start by sticking it at the very end of the address space.
        let mut mmio64_hole = top_of_memory - MMIO64_HOLE_SIZE..top_of_memory;

        // Keep scaling down until we find a hole or run out of memory.
        // In theory we could scale down by 1G chunks until we get to the 4G boundary,
        // but there should be enough address space available to use bigger, hole-sized
        // chunks.
        while !zero_page.check_e820_gap(mmio64_hole.clone())
            && mmio64_hole.start >= MMIO64_HOLE_SIZE
        {
            mmio64_hole.start -= MMIO64_HOLE_SIZE;
            mmio64_hole.end -= MMIO64_HOLE_SIZE;
        }

        if mmio64_hole.start < MMIO64_HOLE_SIZE {
            Err("could not find memory region for 64-bit PCI MMIO hole")
        } else {
            Ok(mmio64_hole.start as u64..mmio64_hole.end as u64)
        }
    }
}

pub struct Q35 {}

impl Machine for Q35 {
    const PCI_VENDOR_ID: u16 = 0x8086;
    const PCI_DEVICE_ID: u16 = 0x29C0;

    fn mmio32_hole(
        _firmware: &mut dyn Firmware,
        _zero_page: &ZeroPage,
    ) -> Result<Range<u32>, &'static str> {
        // SeaBIOS: PCI EXBAR start is hardcoded to 0xB000_0000 and size is 256 MiB:
        // https://github.com/coreboot/seabios/blob/b686f4600792c504f01929f761be473e298de33d/src/fw/dev-q35.h#L11
        // The PCI memory starts just past that (at 0xC000_0000, the 3G mark).
        // PCI memory end is hardcoded, same constant as with 440fx above.
        //
        // EDK2:
        // Uc32Base and Uc32Size determined here:
        // https://github.com/tianocore/edk2/blob/b58ce4c226768ced972bd49886e20c5ae6dfd8f0/OvmfPkg/Library/PlatformInitLib/MemDetect.c#L84
        // PCIe base address fixed at build to 0xE000_0000:
        // https://github.com/tianocore/edk2/blob/8d984e6a5742220d2b28bd85121000136d820fcb/OvmfPkg/OvmfPkgX64.dsc#L646
        //
        // Interestingly enough this means that the PCI MMIO and MMCONFIG regions are in
        // effect flipped for SeaBIOS and EDK2.

        // SeaBIOS memory layout (starts at 2.75 GiB):
        // [0xB000_0000, 0xC000_0000) - 256 MiB, PCI EXBAR
        // [0xC000_0000, 0xFC00_0000) - 960 MiB, PCI MMIO
        // [0xFC00_0000, 0xFFFF_FFFF) -  64 MiB, IO-APIC, HPET, LAPIC etc
        //
        // EDK2 memory layout:
        // [Uc32Base, 0xE000_0000) - PCI MMIO
        // [0xE000_0000, 0xF000_0000) - 256 MiB, MMCONFIG
        // [0xF000_0000, 0xFC00_0000) - 192 MiB, unused
        // [0xFC00_0000, 0xFFFF_FFFF) -  64 MiB, IO-APIC, HPET, LAPIC etc

        // For now we choose a hybrid approach. PCI MMIO will start at 0xB000_0000, the
        // 3G mark. This should always be unused with QEMU.
        let mmio32_hole_start = 0xB000_0000;
        // The end will be at 0xE000_0000, similar to EDK2. We will put MMCONFIG after
        // that, similar to EDK2. This leaves 768 MiB for the PCI MMIO memory.
        let mmio32_hole_end = 0xE000_0000;

        Ok(mmio32_hole_start..mmio32_hole_end)
    }

    fn mmio64_hole<P: Platform>(
        firmware: &mut dyn Firmware,
        zero_page: &ZeroPage,
    ) -> Result<Range<u64>, &'static str> {
        // No special treatment here.
        I440fx::mmio64_hole::<P>(firmware, zero_page)
    }
}

#[cfg(test)]
mod tests {
    use googletest::prelude::*;
    use oak_linux_boot_params::{BootE820Entry, E820EntryType};

    use super::*;
    use crate::{fw_cfg::TestFirmware, hal::MockPlatform};

    #[googletest::test]
    fn pc_hole_from_fwcfg() {
        let mut firmware = TestFirmware::default();
        let zero_page = ZeroPage::new();

        firmware.files.insert(
            PCI_MMIO32_HOLE_BASE_FILE_NAME.to_owned(),
            Box::new(0x1234_0000u64.to_le_bytes()),
        );

        // We don't really test for the end right now; as long as it's after the start,
        // we're fine.
        assert_that!(
            I440fx::mmio32_hole(&mut firmware, &zero_page),
            ok(all!(field!(&Range.start, 0x1234_0000), field!(&Range.end, gt(0x1234_0000))))
        );
    }

    #[googletest::test]
    fn pc_hole_from_low_memory() {
        let mut firmware = TestFirmware::default();
        let mut zero_page = ZeroPage::new();
        // 32 MiB of memory. Welcome to the 90s!
        zero_page.insert_e820_entry(BootE820Entry::new(0x0, 0x200_0000, E820EntryType::RAM));
        // the hole should be at the 2 GiB mark
        assert_that!(
            I440fx::mmio32_hole(&mut firmware, &zero_page),
            ok(all!(field!(&Range.start, 0x8000_0000), field!(&Range.end, gt(0x8000_0000))))
        );
    }

    #[googletest::test]
    fn pc_hole_from_high_memory() {
        let mut firmware = TestFirmware::default();
        let mut zero_page = ZeroPage::new();
        // 2.5 GiB of memory. Welcome to the 00s! This guarantees we cover the 2GiB
        // mark, but don't fill the full 3G space.
        zero_page.insert_e820_entry(BootE820Entry::new(0x0, 0xA000_0000, E820EntryType::RAM));
        // the hole should now be at 3 GiB mark
        assert_that!(
            I440fx::mmio32_hole(&mut firmware, &zero_page),
            ok(all!(field!(&Range.start, 0xC000_0000), field!(&Range.end, gt(0xC000_0000))))
        );
    }

    #[googletest::test]
    fn q35_hole() {
        // Not much to test, besides there being a hole.
        let mut firmware = TestFirmware::default();
        let zero_page = ZeroPage::new();
        assert_that!(
            Q35::mmio32_hole(&mut firmware, &zero_page),
            ok(all!(
                field!(&Range.start, gt(0x8000_0000)), // higher than 2 GiB
                field!(&Range.end, le(0xFE00_0000))    // less than the reserved location
            ))
        )
    }

    #[googletest::test]
    fn mmio64_hole() {
        let gpa_bits = 41;

        // This sets global state for MockPlatform, so beware! However, I don't think
        // we'll ever need different values in other tests.
        let ctx = MockPlatform::guest_phys_addr_size_context();
        ctx.expect().returning(move || gpa_bits);

        let mut firmware = TestFirmware::default();
        let mut zero_page = ZeroPage::new();
        let hole = I440fx::mmio64_hole::<MockPlatform>(&mut firmware, &zero_page);

        // We didn't reserve any memory, so the hole should be right at the very top.
        assert_that!(
            hole,
            ok(all!(
                field!(&Range.start, le(1 << gpa_bits)),
                field!(&Range.end, eq(1 << gpa_bits))
            ))
        );

        // 1 GB at the very top is reserved. The hole should have moved down.
        zero_page.insert_e820_entry(BootE820Entry::new(
            (1 << gpa_bits) - 0x4000_0000,
            0x4000_0000,
            E820EntryType::RAM,
        ));
        let hole = I440fx::mmio64_hole::<MockPlatform>(&mut firmware, &zero_page);
        assert_that!(
            hole,
            ok(all!(
                field!(&Range.start, le((1 << gpa_bits) - 0x4000_0000)),
                field!(&Range.end, le((1 << gpa_bits) - 0x4000_0000))
            ))
        );

        // There is no address space available. How did you get such a machine?
        zero_page.insert_e820_entry(BootE820Entry::new(
            0,
            (1 << gpa_bits) - 0x4000_0000,
            E820EntryType::RAM,
        ));
        let hole = I440fx::mmio64_hole::<MockPlatform>(&mut firmware, &zero_page);
        assert_that!(hole, err(anything()));

        // Okay, _fine_, there is a hole. But it's too small.
        let mut zero_page = ZeroPage::new();
        zero_page.insert_e820_entry(BootE820Entry::new(0, MMIO64_HOLE_SIZE, E820EntryType::RAM));
        zero_page.insert_e820_entry(BootE820Entry::new(
            MMIO64_HOLE_SIZE + (MMIO64_HOLE_SIZE / 2),
            (1 << gpa_bits) - MMIO64_HOLE_SIZE - (MMIO64_HOLE_SIZE / 2),
            E820EntryType::RAM,
        ));
        let hole = I440fx::mmio64_hole::<MockPlatform>(&mut firmware, &zero_page);
        assert_that!(hole, err(anything()));

        // There is an exactly perfect hole.
        let mut zero_page = ZeroPage::new();
        zero_page.insert_e820_entry(BootE820Entry::new(0, MMIO64_HOLE_SIZE, E820EntryType::RAM));
        zero_page.insert_e820_entry(BootE820Entry::new(
            MMIO64_HOLE_SIZE + MMIO64_HOLE_SIZE,
            (1 << gpa_bits) - MMIO64_HOLE_SIZE - MMIO64_HOLE_SIZE,
            E820EntryType::RAM,
        ));
        let hole = I440fx::mmio64_hole::<MockPlatform>(&mut firmware, &zero_page);
        assert_that!(
            hole,
            ok(all!(
                field!(&Range.start, eq(MMIO64_HOLE_SIZE as u64)),
                field!(&Range.end, eq((MMIO64_HOLE_SIZE + MMIO64_HOLE_SIZE) as u64))
            ))
        );
    }
}
