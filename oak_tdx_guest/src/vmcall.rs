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

//! Rust implementation of the sub-functions of the TDX TDCALL[TDG.VP.VMCALL]
//! leaf.
//!
//! See section 2.4.1 of [Guest-Host-Communication Interface (GHCI) for Intel®
//! Trust Domain Extensions (Intel® TDX)](https://cdrdv2.intel.com/v1/dl/getContent/726792)
//! for more information.

use core::arch::{asm, x86_64::CpuidResult};

use bitflags::bitflags;
use x86_64::{
    PhysAddr,
    structures::paging::{frame::PhysFrameRange, page::Size4KiB},
};
/// The result from an instruction that indicates success.
const SUCCESS: u64 = 0;

// TDCALL[TDG.VP.VMCALL] sub-function invocation must be retried
const RETRY: u64 = 1;

// The result from an instruction if the input was invalid.
const INVALID_OPERAND: u64 = 1 << 63;

// The result from an instruction if the input GPA is already in use.
const GPA_INUSE: u64 = (1 << 63) | 1;

// The result from an instruction if the input size or GPA is not properly
// aligned.
const ALIGN_ERROR: u64 = (1 << 63) | (1 << 1);

// GetQuote Status Code: GET_QUOTE_SUCCESS
const GET_QUOTE_SUCCESS: u64 = 0;

// GetQuote Status Code: GET_QUOTE_IN_FLIGHT
// TDG.VP.VMCALL<GetQuote> is under processing. The shared GPA isn’t ready
// for TD to consume.
const GET_QUOTE_IN_FLIGHT: u64 = u64::MAX;

// GetQuote Status Code: GET_QUOTE_ERROR
// Error without specifying any reason.
const GET_QUOTE_ERROR: u64 = 1 << 63;

// GetQuote Status Code: GET_QUOTE_SERVICE_UNAVAILABLE
// Quoting service isn’t available
const GET_QUOTE_SERVICE_UNAVAILABLE: u64 = (1 << 63) | 1;

/// The TDG.VP.VMCALL leaf number for TDCALL.
const VM_CALL_LEAF: u64 = 0;

/// Indicator that the sub-function specified is intended to be used as defined
/// in the GHCI spec.
const DEFAULT_SUB_FUNCTION_USAGE: u64 = 0;

bitflags! {
    /// Registers that will be passed unaltered between the guest and the VMM during TDG.VP.VMCALL.
    ///
    /// RAX (bit 0), RCX (bit 1) and RSP (bit 4) must always be zero, so are not defined below.
    ///
    /// See section 2.4.1 of [Guest-Host-Communication Interface (GHCI) for Intel® Trust Domain
    /// Extensions (Intel® TDX)](https://cdrdv2.intel.com/v1/dl/getContent/726792)
    /// for more information.
    struct Registers: u64 {
        const RBX = 1 << 2;
        const RDX = 1 << 3;
        const RBP = 1 << 5;
        const RSI = 1 << 6;
        const RDI = 1 << 7;
        const R8 = 1 << 8;
        const R9 = 1 << 9;
        const R10 = 1 << 10;
        const R11 = 1 << 11;
        const R12 = 1 << 12;
        const R13 = 1 << 13;
        const R14 = 1 << 14;
        const R15 = 1 << 15;
        const XMM0 = 1 << 16;
        const XMM1 = 1 << 17;
        const XMM2 = 1 << 18;
        const XMM3 = 1 << 19;
        const XMM4 = 1 << 20;
        const XMM5 = 1 << 20;
        const XMM6 = 1 << 22;
        const XMM7 = 1 << 23;
        const XMM8 = 1 << 24;
        const XMM9 = 1 << 25;
        const XMM10 = 1 << 26;
        const XMM11 = 1 << 27;
        const XMM12 = 1 << 28;
        const XMM13 = 1 << 29;
        const XMM14 = 1 << 30;
        const XMM15 = 1 << 31;
    }
}

impl Default for Registers {
    fn default() -> Self {
        // R10 (bit 10) and R11 (bit 11) must always be 1.
        Registers::empty().union(Registers::R10).union(Registers::R11)
    }
}

/// Error when mapping a guest-physical address (GPA) as shared or private.
#[derive(Debug)]
pub enum MapGpaError {
    InvalidOperand(PhysAddr),
    GPAInUse(PhysAddr),
    AlignError(PhysAddr),
    RetriedTooManyTimes(PhysAddr),
    UnknownError(PhysAddr),
}

/// Maps a range of guest-physical addresses (GPAs) as shared with the
/// hypervisor or guest-private.
///
/// If the shared bit of the GPA is set to 1 it will change the page mappings
/// from private to shared.
///
/// If the guest changes pages back from shared to private, these will be added
/// to the guest as pending pages, so the guest must also call
/// `TDCALL[TDG.MEM.PAGE.ACCEPT]` before using them again.
///
/// The function will return an error if the page was already mapped in the
/// desired state (e.g. trying to share a page that was already shared).
///
/// On error `VMCALL_RETRY`, R11 contains a GPA where the guest needs to retry.
/// On error `VMCALL_GPA_INUSE`, the hypervisor believes that the memory has
/// been already in use by the TD, e.g. GPA used for hosting memory dedicated
/// for IO. R11 specifies which GPA in the requested range was in use. on error
/// `VMCALL_ALIGN_ERROR` it means the size or start GPA has alignment error.
///
///
/// See section 3.6 of [Guest-Host-Communication Interface (GHCI) for Intel®
/// Trust Domain Extensions (Intel® TDX)](https://cdrdv2.intel.com/v1/dl/getContent/726792)
/// for more information.
///
/// # Safety
///
/// Sharing or unsharing a pages changes the guest-physical address for those
/// pages, so the caller must make sure that the pages are appropriately mapped
/// in the page tables after the operation is successful.
pub unsafe fn map_gpa(frames: PhysFrameRange<Size4KiB>) -> Result<(), MapGpaError> {
    // The VMCALL sub-function for MAP_GPA.
    const SUB_FUNCTION: u64 = 0x10001;
    // We use the same threshold as OVMF
    // https://github.com/tianocore/edk2/blob/b0f43dd3fdec2363e3548ec31eb455dc1c4ac761/OvmfPkg/Library/BaseMemEncryptTdxLib/MemoryEncryption.c#L41
    const MAX_RETRY_PER_PAGE: u32 = 3;

    let mut vm_call_result: u64;
    let mut sub_function_result: u64;
    let registers = Registers::default().union(Registers::R12).union(Registers::R13);
    let gpa_start = frames.start.start_address().as_u64();
    let gpa_size = frames.end.start_address().as_u64().checked_sub(gpa_start).unwrap();
    let mut failing_gpa: u64 = u64::MAX;
    let mut current_start = gpa_start;
    let mut current_size = gpa_size;
    let mut retry_times: u32 = 0;

    while retry_times < MAX_RETRY_PER_PAGE {
        retry_times += 1;
        // The TDCALL leaf 0 goes into RAX. RAX returns the top-level result (0 is
        // success). The bitflags of registers to be passed through to the VMM goes
        // into RCX. The sub-function usage (always 0 when conforming to the GHCI
        // spec) goes into R10, and the result of the subfunction is returned in
        // R10. The sub-function to call goes into R11 and the failing address is
        // returned in R11 in case of failure. The start GPA goes into R12 (must be
        // 4KiB-aligned) and the size of the range (must be a multiple of 4KiB) goes
        // into R13.
        //
        // Safety: as long as the changed physical address of the page is handled
        // correctly by the caller, calling TDCALL here is safe since it does not
        // alter memory directly and all the affected registers are specified, so no
        // unspecified registers will be clobbered.
        unsafe {
            asm!(
                "tdcall",
                inout("rax") VM_CALL_LEAF => vm_call_result,
                in("rcx") registers.bits(),
                inout("r10") DEFAULT_SUB_FUNCTION_USAGE => sub_function_result,
                inout("r11") SUB_FUNCTION => failing_gpa,
                in("r12") current_start,
                in("r13") current_size,
                options(nomem, nostack),
            );
        }

        // According to the spec the top-level result for this sub-function will aways
        // be 0 as long as the specified sub-function leaf is correct.
        assert_eq!(vm_call_result, SUCCESS, "TDG.VP.VMCALL returned an invalid result");

        match sub_function_result {
            SUCCESS => return Ok(()),
            RETRY => {
                if failing_gpa > current_start && failing_gpa < gpa_start + gpa_size {
                    // Successfully mapped some memory but not enough. Restart counting.
                    retry_times = 0;
                    // TD must retry this operation for the pages in the region starting
                    // at the GPA specified in R11.
                    // [start_gpa, current_start) has been processed. Memory region to be retried
                    // is [current_start, start_gpa + size)
                    current_start = failing_gpa;
                    current_size = (gpa_start + gpa_size).checked_sub(current_start).unwrap();
                } else if failing_gpa == current_start {
                    continue;
                } else {
                    return Err(MapGpaError::UnknownError(PhysAddr::new(failing_gpa)));
                }
            }
            INVALID_OPERAND => {
                return Err(MapGpaError::InvalidOperand(PhysAddr::new(failing_gpa)));
            }
            GPA_INUSE => return Err(MapGpaError::GPAInUse(PhysAddr::new(failing_gpa))),
            ALIGN_ERROR => return Err(MapGpaError::AlignError(PhysAddr::new(failing_gpa))),
            _ => return Err(MapGpaError::UnknownError(PhysAddr::new(failing_gpa))),
        }
    } // while retry_times < MAX_RETRY_PER_PAGE

    // Retried MAX_RETRY_PER_PAGE times but the map_gpa request is still incomplete.
    Err(MapGpaError::RetriedTooManyTimes(PhysAddr::new(failing_gpa)))
}

/// Executes CPUID for the specified leaf and sub-leaf.
///
/// See section 3.6 of [Guest-Host-Communication Interface (GHCI) for Intel®
/// Trust Domain Extensions (Intel® TDX)](https://cdrdv2.intel.com/v1/dl/getContent/726792)
/// for more information.
pub fn call_cpuid(leaf: u32, sub_leaf: u32) -> Result<CpuidResult, &'static str> {
    // The VMCALL sub-function for Instruction.CPUID.
    const SUB_FUNCTION: u64 = 10;

    let mut vm_call_result: u64;
    let mut sub_function_result: u64;
    let mut eax: u64;
    let mut ebx: u64;
    let mut ecx: u64;
    let mut edx: u64;

    let registers = Registers::default()
        .union(Registers::R12)
        .union(Registers::R13)
        .union(Registers::R14)
        .union(Registers::R15);

    // The TDCALL leaf 0 goes into RAX. RAX returns the top-level result (0 is
    // success). The bitflags of registers to be passed through to the VMM goes
    // into RCX. The sub-function usage (always 0 when conforming to the GHCI
    // spec) goes into R10, and the result of the subfunction is returned in
    // R10. The sub-function to call goes into R11. The CPUID leaf goes into R12
    // and the subleaf into R13. The CPUID EAX values is returned in R12, the EBX
    // value in R13, the ECX value in R14 and the EDX value in R15. We zero out all
    // output registers in the input to make sure old register values don't
    // accidentally leak to the hypervisor.
    //
    // Safety: calling TDCALL here is safe since it does not alter memory and all
    // the affected registers are specified, so no unspecified registers will be
    // clobbered.
    unsafe {
        asm!(
            "tdcall",
            inout("rax") VM_CALL_LEAF => vm_call_result,
            in("rcx") registers.bits(),
            inout("r10") DEFAULT_SUB_FUNCTION_USAGE => sub_function_result,
            in("r11") SUB_FUNCTION,
            inout("r12") leaf as u64 => eax,
            inout("r13") sub_leaf as u64 => ebx,
            inout("r14") 0u64 => ecx,
            inout("r15") 0u64 => edx,
            options(nomem, nostack),
        );
    }

    // According to the spec the top-level result for this sub-function will aways
    // be 0 as long as the specified sub-function leaf is correct.
    assert_eq!(vm_call_result, SUCCESS, "TDG.VP.VMCALL returned an invalid result");

    if sub_function_result == INVALID_OPERAND {
        return Err("invalid CPUID request");
    }
    // According to the spec this sub-function will always return either 0 or
    // INVALID_OPERAND.
    assert_eq!(
        sub_function_result, SUCCESS,
        "TDG.VP.VMCALL<Instruction.CPUID> returned an invalid result"
    );

    Ok(CpuidResult { eax: eax as u32, ebx: ebx as u32, ecx: ecx as u32, edx: edx as u32 })
}

/// Reads a single byte from the specified IO port.
pub fn io_read_u8(port: u32) -> Result<u8, &'static str> {
    io_read(port, IoWidth::Io8).map(|data| data as u8)
}

/// Reads two bytes from the specified IO port.
pub fn io_read_u16(port: u32) -> Result<u16, &'static str> {
    io_read(port, IoWidth::Io16).map(|data| data as u16)
}

/// Reads four bytes from the specified IO port.
pub fn io_read_u32(port: u32) -> Result<u32, &'static str> {
    io_read(port, IoWidth::Io32).map(|data| data as u32)
}

/// Writes a single byte to the specified IO port.
pub fn io_write_u8(port: u32, data: u8) -> Result<(), &'static str> {
    io_write(port, IoWidth::Io8, data as u64)
}

/// Writes two bytes to the specified IO port.
pub fn io_write_u16(port: u32, data: u16) -> Result<(), &'static str> {
    io_write(port, IoWidth::Io16, data as u64)
}

/// Writes four bytes to the specified IO port.
pub fn io_write_u32(port: u32, data: u32) -> Result<(), &'static str> {
    io_write(port, IoWidth::Io32, data as u64)
}

/// IO width for the port-based io instruction.
#[repr(u64)]
enum IoWidth {
    /// A single byte is being read or written.
    Io8 = 1,
    /// Two bytes are being read or written.
    Io16 = 2,
    /// Four bytes are being read or written.
    Io32 = 4,
}

/// Direction the port-based io instruction.
#[repr(u64)]
enum IoDirection {
    /// Reading data.
    Read = 0,
    /// Writing data.
    Write = 1,
}

/// Performs a port-based IO read operation.
///
/// See section 3.9 of [Guest-Host-Communication Interface (GHCI) for Intel®
/// Trust Domain Extensions (Intel® TDX)](https://cdrdv2.intel.com/v1/dl/getContent/726792)
/// for more information.
fn io_read(port: u32, size: IoWidth) -> Result<u64, &'static str> {
    // The VMCALL sub-function for Instruction.IO.
    const SUB_FUNCTION: u64 = 30;

    let mut vm_call_result: u64;
    let mut sub_function_result: u64;
    let registers =
        Registers::default().union(Registers::R12).union(Registers::R13).union(Registers::R14);

    let mut data: u64;

    // The TDCALL leaf 0 goes into RAX. RAX returns the top-level result (0 is
    // success). The bitflags of registers to be passed through to the VMM goes
    // into RCX. The sub-function usage (always 0 when conforming to the GHCI
    // spec) goes into R10, and the result of the subfunction is returned in
    // R10. The sub-function to call goes into R11 and the data is returned in
    // R11 if the read is successful. The size of the read (1,2 or 4 bytes) goes
    // into R12. The direction (read) goes into R13. The IO port number goes into
    // R14.
    //
    // Safety: calling TDCALL here is safe since it does not alter memory and all
    // the affected registers are specified, so no unspecified registers will be
    // clobbered.
    unsafe {
        asm!(
            "tdcall",
            inout("rax") VM_CALL_LEAF => vm_call_result,
            in("rcx") registers.bits(),
            inout("r10") DEFAULT_SUB_FUNCTION_USAGE => sub_function_result,
            inout("r11") SUB_FUNCTION => data,
            in("r12") size as u64,
            in("r13") IoDirection::Read as u64,
            in("r14") port as u64,
            options(nomem, nostack),
        );
    }

    // According to the spec the top-level result for this sub-function will aways
    // be 0 as long as the specified sub-function leaf is correct.
    assert_eq!(vm_call_result, SUCCESS, "TDG.VP.VMCALL returned an invalid result");

    if sub_function_result == INVALID_OPERAND {
        return Err("IO read operation failed");
    }
    // According to the spec this sub-function will always return either 0 or
    // INVALID_OPERAND.
    assert_eq!(
        sub_function_result, SUCCESS,
        "TDG.VP.VMCALL<Instruction.IO> returned an invalid result"
    );

    Ok(data)
}

/// Performs a port-based IO write operation.
///
/// See section 3.9 of [Guest-Host-Communication Interface (GHCI) for Intel®
/// Trust Domain Extensions (Intel® TDX)](https://cdrdv2.intel.com/v1/dl/getContent/726792)
/// for more information.
fn io_write(port: u32, size: IoWidth, data: u64) -> Result<(), &'static str> {
    // The VMCALL sub-function for Instruction.IO.
    const SUB_FUNCTION: u64 = 30;
    // The result if the IO operation was invalid.
    const INVALID_OPERAND: u64 = 1 << 63;

    let mut vm_call_result: u64;
    let mut sub_function_result: u64;
    let registers = Registers::default()
        .union(Registers::R12)
        .union(Registers::R13)
        .union(Registers::R14)
        .union(Registers::R15);

    // The TDCALL leaf 0 goes into RAX. RAX returns the top-level result (0 is
    // success). The bitflags of registers to be passed through to the VMM goes
    // into RCX. The sub-function usage (always 0 when conforming to the GHCI
    // spec) goes into R10, and the result of the subfunction is returned in
    // R10. The sub-function to call goes into R11. The size of the write (1,2
    // or 4 bytes) goes into R12. The direction (write) goes into R13. The IO port
    // number goes into R14. The data to write goes into R15.
    //
    // Safety: calling TDCALL here is safe since it does not alter memory and all
    // the affected registers are specified, so no unspecified registers will be
    // clobbered.
    unsafe {
        asm!(
            "tdcall",
            inout("rax") VM_CALL_LEAF => vm_call_result,
            in("rcx") registers.bits(),
            inout("r10") DEFAULT_SUB_FUNCTION_USAGE => sub_function_result,
            in("r11") SUB_FUNCTION,
            in("r12") size as u64,
            in("r13") IoDirection::Write as u64,
            in("r14") port as u64,
            in("r15") data,
            options(nomem, nostack),
        );
    }

    // According to the spec the top-level result for this sub-function will aways
    // be 0 as long as the specified sub-function leaf is correct.
    assert_eq!(vm_call_result, SUCCESS, "TDG.VP.VMCALL returned an invalid result");

    if sub_function_result == INVALID_OPERAND {
        return Err("IO write operation failed");
    }
    // According to the spec this sub-function will always return either 0 or
    // INVALID_OPERAND.
    assert_eq!(
        sub_function_result, SUCCESS,
        "TDG.VP.VMCALL<Instruction.IO> returned an invalid result"
    );

    Ok(())
}

/// Writes a value to the specified model-specific register.
///
/// See section 3.11 of [Guest-Host-Communication Interface (GHCI) for Intel®
/// Trust Domain Extensions (Intel® TDX)](https://cdrdv2.intel.com/v1/dl/getContent/726792)
/// for more information.
///
/// # Safety
///
/// Modifying an MSR could impact the execution environment, so the caller must
/// ensure that the MSR modification will not lead to undefined behavior.
pub unsafe fn msr_write(msr: u32, data: u64) -> Result<(), &'static str> {
    // The VMCALL sub-function for Instruction.WRMSR.
    const SUB_FUNCTION: u64 = 32;

    let mut vm_call_result: u64;
    let mut sub_function_result: u64;
    let registers = Registers::default().union(Registers::R12);

    // The TDCALL leaf 0 goes into RAX. RAX returns the top-level result (0 is
    // success). The bitflags of registers to be passed through to the VMM goes
    // into RCX. The sub-function usage (always 0 when conforming to the GHCI
    // spec) goes into R10, and the result of the subfunction is returned in
    // R10. The sub-function to call goes into R11, and the MSR value is
    // returned in T11. The MSR index goes into R12.
    //
    // Safety: if the MSR modification is safe, calling TDCALL here is safe since it
    // does not alter memory and all the affected registers are specified, so no
    // unspecified registers will be clobbered. It is up to the caller to ensure
    // that the MSR modification itself is safe.
    unsafe {
        asm!(
            "tdcall",
            inout("rax") VM_CALL_LEAF => vm_call_result,
            in("rcx") registers.bits(),
            inout("r10") DEFAULT_SUB_FUNCTION_USAGE => sub_function_result,
            in("r11") SUB_FUNCTION,
            in("r12") msr as u64,
            in("r13") data,
            options(nomem, nostack),
        );
    }

    // According to the spec the top-level result for this sub-function will aways
    // be 0 as long as the specified sub-function leaf is correct.
    assert_eq!(vm_call_result, SUCCESS, "TDG.VP.VMCALL returned an invalid result");

    if sub_function_result == INVALID_OPERAND {
        return Err("MSR write operation failed");
    }
    // According to the spec this sub-function will always return either 0 or
    // INVALID_OPERAND.
    assert_eq!(
        sub_function_result, SUCCESS,
        "TDG.VP.VMCALL<Instruction.WRMSR> returned an invalid result"
    );

    Ok(())
}

/// Reads a value from the specified model-specific register.
///
/// See section 3.10 of [Guest-Host-Communication Interface (GHCI) for Intel®
/// Trust Domain Extensions (Intel® TDX)](https://cdrdv2.intel.com/v1/dl/getContent/726792)
/// for more information.
pub fn msr_read(msr: u32) -> Result<u64, &'static str> {
    // The VMCALL sub-function for Instruction.RDMSR.
    const SUB_FUNCTION: u64 = 31;

    let mut vm_call_result: u64;
    let mut sub_function_result: u64;
    let registers = Registers::default().union(Registers::R12);

    let mut data: u64;

    // The TDCALL leaf 0 goes into RAX. RAX returns the top-level result (0 is
    // success). The bitflags of registers to be passed through to the VMM goes
    // into RCX. The sub-function usage (always 0 when conforming to the GHCI
    // spec) goes into R10, and the result of the subfunction is returned in
    // R10. The sub-function to call goes into R11, and the MSR value is
    // returned in T11. The MSR index goes into R12.
    //
    // Safety: calling TDCALL here is safe since it does not alter memory and all
    // the affected registers are specified, so no unspecified registers will be
    // clobbered.
    unsafe {
        asm!(
            "tdcall",
            inout("rax") VM_CALL_LEAF => vm_call_result,
            in("rcx") registers.bits(),
            inout("r10") DEFAULT_SUB_FUNCTION_USAGE => sub_function_result,
            inout("r11") SUB_FUNCTION => data,
            in("r12") msr as u64,
            options(nomem, nostack),
        );
    }

    // According to the spec the top-level result for this sub-function will aways
    // be 0 as long as the specified sub-function leaf is correct.
    assert_eq!(vm_call_result, SUCCESS, "TDG.VP.VMCALL returned an invalid result");

    if sub_function_result == INVALID_OPERAND {
        return Err("MSR read operation failed");
    }
    // According to the spec this sub-function will always return either 0 or
    // INVALID_OPERAND.
    assert_eq!(
        sub_function_result, SUCCESS,
        "TDG.VP.VMCALL<Instruction.RDMSR> returned an invalid result"
    );

    Ok(data)
}

/// Emulated MMIO-write with help from tdx-module and VMM
///
/// See section 3.7 of [Guest-Host-Communication Interface (GHCI) for Intel®
/// Trust Domain Extensions (Intel® TDX)](https://cdrdv2.intel.com/v1/dl/getContent/726792)
/// for more information.
pub fn mmio_write_u32(address: *const u32, data: u32) -> Result<(), &'static str> {
    // The VMCALL sub-function for #VE.RequestMMIO
    const SUB_FUNCTION: u64 = 0x30;

    let mut vm_call_result: u64;
    let mut sub_function_result: u64;
    let registers = Registers::default()
        .union(Registers::R12)
        .union(Registers::R13)
        .union(Registers::R14)
        .union(Registers::R15);

    // The TDCALL leaf 0 goes into RAX. RAX returns the top-level result (0 is
    // success). The bitflags of registers to be passed through to the VMM goes
    // into RCX. The sub-function usage (always 0 when conforming to the GHCI
    // spec) goes into R10, and the result of the subfunction is returned in
    // R10. The sub-function to call goes into R11. The size of access (1/2/4/8)
    // goes into R12. The direction (0=Read, 1=Write) goes into R13. The MMIO
    // address goes into R14 and the data to write (if R13 is 1) goes into R15.
    // The return code of the sub function goes to R10.
    //
    // Safety: calling TDCALL here is safe since it does not alter memory and all
    // the affected registers are specified, so no unspecified registers will be
    // clobbered.
    unsafe {
        asm!(
            "tdcall",
            inout("rax") VM_CALL_LEAF => vm_call_result,
            in("rcx") registers.bits(),
            inout("r10") DEFAULT_SUB_FUNCTION_USAGE => sub_function_result,
            in("r11") SUB_FUNCTION,
            in("r12") IoWidth::Io32 as u64,
            in("r13") IoDirection::Write as u64,
            in("r14") address as u64,
            in("r15") data as u64,
            options(nomem, nostack),
        );
    }

    // According to the spec the top-level result for this sub-function will aways
    // be 0 as long as the specified sub-function leaf is correct.
    assert_eq!(vm_call_result, SUCCESS, "TDG.VP.VMCALL returned an invalid result");

    if sub_function_result == INVALID_OPERAND {
        return Err("invalid operands provided by the TD, e.g., MMIO address");
    }

    // According to the spec this sub-function will always return either 0 or
    // INVALID_OPERAND.
    assert_eq!(
        sub_function_result, SUCCESS,
        "TDG.VP.VMCALL<#VE.RequestMMIO> returned an invalid result"
    );

    Ok(())
}

/// Emulated MMIO-read with help from tdx-module and VMM
///
/// See section 3.7 of [Guest-Host-Communication Interface (GHCI) for Intel®
/// Trust Domain Extensions (Intel® TDX)](https://cdrdv2.intel.com/v1/dl/getContent/726792)
/// for more information.
pub fn mmio_read_u32(address: *const u32) -> Result<u32, &'static str> {
    // The VMCALL sub-function for #VE.RequestMMIO
    const SUB_FUNCTION: u64 = 0x30;

    let mut vm_call_result: u64;
    let mut sub_function_result: u64;
    let registers =
        Registers::default().union(Registers::R12).union(Registers::R13).union(Registers::R14);

    let mut value_from_mmio_read: u64;

    // The TDCALL leaf 0 goes into RAX. RAX returns the top-level result (0 is
    // success). The bitflags of registers to be passed through to the VMM goes
    // into RCX. The sub-function usage (always 0 when conforming to the GHCI
    // spec) goes into R10, and the result of the subfunction is returned in
    // R10. The sub-function to call goes into R11. The size of access (1/2/4/8)
    // goes into R12. The direction (0=Read, 1=Write) goes into R13. The MMIO
    // address goes into R14. The return code of the sub function goes to R10.
    // The value read from MMIO goes into R11.
    //
    // Safety: calling TDCALL here is safe since it does not alter memory and all
    // the affected registers are specified, so no unspecified registers will be
    // clobbered.
    unsafe {
        asm!(
            "tdcall",
            inout("rax") VM_CALL_LEAF => vm_call_result,
            in("rcx") registers.bits(),
            inout("r10") DEFAULT_SUB_FUNCTION_USAGE => sub_function_result,
            inout("r11") SUB_FUNCTION => value_from_mmio_read,
            in("r12") IoWidth::Io32 as u64,
            in("r13") IoDirection::Read as u64,
            in("r14") address as u64,
            options(nomem, nostack),
        );
    }

    // According to the spec the top-level result for this sub-function will aways
    // be 0 as long as the specified sub-function leaf is correct.
    assert_eq!(vm_call_result, SUCCESS, "TDG.VP.VMCALL returned an invalid result");

    if sub_function_result == INVALID_OPERAND {
        return Err("invalid operands provided by the TD, e.g., MMIO address");
    }

    // According to the spec this sub-function will always return either 0 or
    // INVALID_OPERAND.
    assert_eq!(
        sub_function_result, SUCCESS,
        "TDG.VP.VMCALL<#VE.RequestMMIO> returned an invalid result"
    );

    Ok(value_from_mmio_read as u32)
}

/// TDVMCall Instruction.WBINVD
///
/// See section 3.12 of [Guest-Host-Communication Interface (GHCI) for Intel®
/// Trust Domain Extensions (Intel® TDX)](https://cdrdv2.intel.com/v1/dl/getContent/726792)
/// for more information.
fn instruction_wbinvd(invalidate: bool) -> Result<(), &'static str> {
    // The VMCALL sub-function for Instruction.WBINVD
    const SUB_FUNCTION: u64 = 0x36;

    let mut vm_call_result: u64;
    let mut sub_function_result: u64;
    let registers = Registers::default().union(Registers::R12);

    let operation = if invalidate {
        0 /* WBINVD */
    } else {
        1 /* WBNOINVD */
    };

    // The TDCALL leaf 0 goes into RAX. RAX returns the top-level result (0 is
    // success). The bitflags of registers to be passed through to the VMM goes
    // into RCX. The sub-function usage (always 0 when conforming to the GHCI
    // spec) goes into R10, and the result of the subfunction is returned in
    // R10. The sub-function to call goes into R11. WBINVD/WBNOINVD (0/1) goes
    // into R12. The return code of the sub function goes to R10.
    //
    // Safety: calling TDCALL here is safe since it does not alter memory and all
    // the affected registers are specified, so no unspecified registers will be
    // clobbered.
    unsafe {
        asm!(
            "tdcall",
            inout("rax") VM_CALL_LEAF => vm_call_result,
            in("rcx") registers.bits(),
            inout("r10") DEFAULT_SUB_FUNCTION_USAGE => sub_function_result,
            in("r11") SUB_FUNCTION,
            in("r12") operation as u64, // 0: WBINVD, 1: WBNOINVD
            options(nomem, nostack),
        );
    }

    // According to the spec the top-level result for this sub-function will aways
    // be 0 as long as the specified sub-function leaf is correct.
    assert_eq!(vm_call_result, SUCCESS, "TDG.VP.VMCALL returned an invalid result");

    if sub_function_result == INVALID_OPERAND {
        return Err("Invalid R12 value requested.");
    }

    // According to the spec this sub-function will always return either 0 or
    // INVALID_OPERAND.
    assert_eq!(
        sub_function_result, SUCCESS,
        "TDG.VP.VMCALL<Instruction.WBINVD> returned an invalid result"
    );

    Ok(())
}

/// TDVMCALL WBINVD - Write Back and Invalidate Cache
pub fn tdvmcall_wbinvd() -> Result<(), &'static str> {
    instruction_wbinvd(true /* invalidate_cache */)
}

/// TDVMCALL WBNOINVD - Write Back and Do Not Invalidate Cache
pub fn tdvmcall_wbnoinvd() -> Result<(), &'static str> {
    instruction_wbinvd(false /* invalidate_cache */)
}

/// TDVMCall GetTdVmCallInfo
///
/// See section 3.1 of [Guest-Host-Communication Interface (GHCI) for Intel®
/// Trust Domain Extensions (Intel® TDX)](https://cdrdv2.intel.com/v1/dl/getContent/726792)
/// for more information.
pub fn get_td_vm_call_info() -> Result<(), &'static str> {
    // The VMCALL sub-function for GetTdVmCallInfo
    const SUB_FUNCTION: u64 = 0x10000;

    let mut vm_call_result: u64;
    let mut sub_function_result: u64;
    let registers = Registers::default().union(Registers::R12);

    let mut r11_out: u64;
    let mut r12_out: u64;
    let mut r13_out: u64;
    let mut r14_out: u64;

    // The TDCALL leaf 0 goes into RAX. RAX returns the top-level result (0 is
    // success). The bitflags of registers to be passed through to the VMM goes
    // into RCX. The sub-function usage (always 0 when conforming to the GHCI
    // spec) goes into R10, and the result of the subfunction is returned in
    // R10. The sub-function to call goes into R11. The return code of the sub
    // function goes to R10. R11/R12/R13/R14 are Leaf-specific output. They will
    // be returned as 0.
    //
    // Safety: calling TDCALL here is safe since it does not alter memory and all
    // the affected registers are specified, so no unspecified registers will be
    // clobbered.
    unsafe {
        asm!(
            "tdcall",
            inout("rax") VM_CALL_LEAF => vm_call_result,
            in("rcx") registers.bits(),
            inout("r10") DEFAULT_SUB_FUNCTION_USAGE => sub_function_result,
            inout("r11") SUB_FUNCTION => r11_out,
            inout("r12") 0u64 => r12_out, // Must be set to 0
            out("r13") r13_out,
            out("r14") r14_out,
            options(nomem, nostack),
        );
    }

    // According to the spec the top-level result for this sub-function will aways
    // be 0 as long as the specified sub-function leaf is correct.
    assert_eq!(vm_call_result, SUCCESS, "TDG.VP.VMCALL returned an invalid result");

    // According to the spec, on success, the status code should be 0, also R11
    // to R14 have to be 0.
    if (sub_function_result | r11_out | r12_out | r13_out | r14_out) != SUCCESS {
        Err("This TD cannot use all features defined in spec")
    } else {
        Ok(())
    }
}

#[derive(Debug)]
pub enum GetQuoteError {
    InvalidOperand(PhysAddr),
    TooManyRetry,
    QuoteInFlight,
    QuoteError,
    ServiceUnavailable,
    UnknownError,
}

/// TDVMCall GetQuote
///
/// GetQuote TDG.VP.VMCALL is a doorbell-like interface used to help send a
/// message to the host VMM to queue operations that tend to be long-running
/// operations. GetQuote is designed to invoke a request to generate a TD-Quote
/// signing by a service hosting TD-Quoting Enclave operating in the host
/// environment for a TD Report passed as a parameter by the TD. TDREPORT_STRUCT
/// is a memory operand intended to be sent via the GetQuote TDG.VP.VMCALL to
/// indicate the asynchronous service requested.
///
/// For the GetQuote operation, the goal is for the TDREPORT_STRUCT to be
/// received by the TD via a prior TDCALL[TDG.MR.REPORT] in a buffer and placed
/// in a shared-GPA space passed to the VMM as an operand in the GetQuote
/// TDG.VP.VMCALL. In the case of this operation, the VMM can access the
/// TDREPORT_STRUCT, queue the operation for a service hosting TD-Quoting
/// enclave, and, when completed, return the Quote via the same, shared-memory
/// area.
///
/// For the TD to invoke the TDG.VP.VMCALL<GetQuote>, the host VMM can
/// signal the event completion to the TD OS via a notification interrupt the
/// host VMM injects into the TD (using the Event-notification vector registered
/// via the SetupEventNotifyInterrupt TDG.VP.VMCALL).
///
///
/// See section 3.3 of
/// [Guest-Host-Communication Interface (GHCI) for Intel® Trust Domain Extensions (Intel® TDX)](https://cdrdv2.intel.com/v1/dl/getContent/726792)
/// for more information.
pub fn get_quote(frames: PhysFrameRange<Size4KiB>) -> Result<(), GetQuoteError> {
    // The VMCALL sub-function for GetQuote
    // GetQuote sends TDREPORT_STRUCT to VMM to request a TD Quote
    const SUB_FUNCTION: u64 = 0x10002;
    const MAX_RETRY: u32 = 3;

    let mut vm_call_result: u64;
    let mut sub_function_result: u64;
    let registers = Registers::default().union(Registers::R13);
    let gpa_start = frames.start.start_address().as_u64();
    let gpa_size = frames.end.start_address().as_u64().checked_sub(gpa_start).unwrap();

    for _ in 0..MAX_RETRY {
        // The TDCALL leaf 0 goes into RAX. RAX returns the top-level result (0 is
        // success). The bitflags of registers to be passed through to the VMM goes
        // into RCX. The sub-function usage (always 0 when conforming to the GHCI
        // spec) goes into R10, and the result of the subfunction is returned in
        // R10. The sub-function to call goes into R11 and the failing address is
        // returned in R11 in case of failure. The start GPA goes into R12 (must be
        // 4KiB-aligned) and the size of the range (must be a multiple of 4KiB) goes
        // into R13.
        //
        // Safety: as long as the changed physical address of the page is handled
        // correctly by the caller, calling TDCALL here is safe since it does not
        // alter memory directly and all the affected registers are specified, so no
        // unspecified registers will be clobbered.
        unsafe {
            asm!(
                "tdcall",
                inout("rax") VM_CALL_LEAF => vm_call_result,
                in("rcx") registers.bits(),
                inout("r10") DEFAULT_SUB_FUNCTION_USAGE => sub_function_result,
                in("r11") SUB_FUNCTION,
                in("r12") gpa_start,
                in("r13") gpa_size,
                options(nomem, nostack),
            );
        }

        // According to the spec the top-level result for this sub-function will aways
        // be 0 as long as the specified sub-function leaf is correct.
        assert_eq!(vm_call_result, SUCCESS, "TDG.VP.VMCALL returned an invalid result");

        match sub_function_result {
            GET_QUOTE_SUCCESS => return Ok(()),
            RETRY => continue,
            GET_QUOTE_IN_FLIGHT => {
                return Err(GetQuoteError::QuoteInFlight);
            }
            GET_QUOTE_ERROR => {
                return Err(GetQuoteError::QuoteError);
            }
            GET_QUOTE_SERVICE_UNAVAILABLE => {
                return Err(GetQuoteError::ServiceUnavailable);
            }
            _ => {
                return Err(GetQuoteError::UnknownError);
            }
        }
    }

    // At this point the status cannot be SUCCESS or INVALID_OPERAND
    Err(GetQuoteError::TooManyRetry)
}
