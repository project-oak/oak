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

//! This module contains an implementation of the guest-hypervisor communications block (GHCB) page
//! that can be used for communicating with the hypervisor.

use crate::{
    cpuid::{CpuidInput, CpuidOutput},
    msr::{
        register_ghcb_location, set_ghcb_address_and_exit, GhcbGpa, RegisterGhcbGpaError,
        RegisterGhcbGpaRequest,
    },
    Translator,
};
use bitflags::bitflags;
use x86_64::{PhysAddr, VirtAddr};
use zerocopy::FromBytes;

/// The size of the GHCB page.
pub const GHCB_PAGE_SIZE: usize = 4096;

/// The version of the GHCB protocol and page layout that we expect to use.
pub const GHCB_PROTOCOL_VERSION: u16 = 2;

/// The value of the sw_exit_code field when doing the IOIO protocol.
///
/// See section 4.1.2 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
const SW_EXIT_CODE_IOIO_PROT: u64 = 0x7B;

/// The value of the sw_exit_code field when doing the MSR reading or writing protocol.
///
/// See section 4.1.3 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
const SW_EXIT_CODE_MSR_PROT: u64 = 0x7C;

/// The value of the sw_exit_code field when doing a CPUID request.
///
/// See section 4 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
const SW_EXIT_CODE_CPUID: u64 = 0x72;

/// The value of the sw_exit_code field when doing a Guest Message request.
///
/// See table 6 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
const SW_EXIT_CODE_GUEST_REQUEST: u64 = 0x8000_0011;

/// Indicator bit that the address is a 16 bit number.
///
/// See section 15.10.2 of <https://www.amd.com/system/files/TechDocs/24593.pdf> for more details.
const IOIO_ADDRESS_SIZE_16: u64 = 1 << 7;

/// Indicator bit that the IO port will be used for reading data.
///
/// See section 15.10.2 of <https://www.amd.com/system/files/TechDocs/24593.pdf> for more details.
const IOIO_READ: u64 = 1;

/// Indicator bit that the IO data is an 8 bit number.
///
/// See section 15.10.2 of <https://www.amd.com/system/files/TechDocs/24593.pdf> for more details.
const IOIO_DATA_SIZE_8: u64 = 1 << 4;

/// Indicator bit that the IO data is an 16 bit number.
///
/// See section 15.10.2 of <https://www.amd.com/system/files/TechDocs/24593.pdf> for more details.
const IOIO_DATA_SIZE_16: u64 = 1 << 5;

/// Indicator bit that the IO data is a 32 bit number.
///
/// See section 15.10.2 of <https://www.amd.com/system/files/TechDocs/24593.pdf> for more details.
const IOIO_DATA_SIZE_32: u64 = 1 << 6;

/// The bitmap representing the minimum fields that must always be valid.
const BASE_VALID_BITMAP: ValidBitmap = ValidBitmap::SW_EXIT_CODE
    .union(ValidBitmap::SW_EXIT_INFO_1)
    .union(ValidBitmap::SW_EXIT_INFO_2);

/// The mask to use on MSR register values.
///
/// RDMSR and WRMSR only use the 32-bit EAX and EDX registers, not 64-bit RAX and RDX, so we only
/// use the least significant 32 bits.
const MSR_REGISTER_MASK: u64 = 0xffff_ffff;

/// The guest-host communications block.
///
/// See: Table 3 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>
#[repr(C, align(4096))]
#[derive(Debug, FromBytes)]
pub struct Ghcb {
    /// Reserved. Must be 0.
    _reserved_0: [u8; 203],
    /// The current privilege level of the executing code.
    pub cpl: u8,
    /// Reserved. Must be 0.
    _reserved_1: [u8; 116],
    /// The value of the IA32_XSS model-specific reqister.
    pub xss: u64,
    /// Reserved. Must be 0.
    _reserved_2: [u8; 24],
    /// The value of the DR7 debug register.
    pub dr7: u64,
    /// Reserved. Must be 0.
    _reserved_3: [u8; 144],
    /// The value of the RAX register.
    pub rax: u64,
    /// Reserved. Must be 0.
    _reserved_4: [u8; 264],
    /// The value of the RCX register.
    pub rcx: u64,
    /// The value of the RDX register.
    pub rdx: u64,
    /// The value of the RBX register.
    pub rbx: u64,
    /// Reserved. Must be 0.
    _reserved_5: [u8; 112],
    /// Guest-controlled exit code.
    pub sw_exit_code: u64,
    /// Guest-controlled exit information 1.
    pub sw_exit_info_1: u64,
    /// Guest-controlled exit information 2.
    pub sw_exit_info_2: u64,
    /// Guest-controlled additional information.
    pub sw_scratch: u64,
    /// Reserved. Must be 0.
    _reserved_6: [u8; 56],
    /// Value of the XCR0 extended control register.
    pub xcr0: u64,
    /// Bitmap indicating which quadwords of the save state area are valid in the range from offset
    /// 0x000 through to offset 0x3ef.
    ///
    /// A flag must be set for each field that is set as part of handling a non-automatic exit
    /// event. The value must also be checked on the return from the hypervisor.
    pub valid_bitmap: ValidBitmap,
    /// The guest-physical address of the page that contains the x87-related saved state.
    pub x87_state_gpa: u64,
    /// Reserved. Must be 0.
    _reserved_7: [u8; 1016],
    /// Area that can be used as a shared buffer for communicating additional information.
    pub shared_buffer: [u8; 2032],
    /// Reserved. Must be 0.
    _reserved_8: [u8; 10],
    /// The version of the GHCB protocol and page layout in use.
    pub protocol_version: u16,
    /// The usage of the GHCB page. A value of 0 indicates the usage is in line with the definition
    /// as specified in this struct. Any other value indicates a hypervisor-defined usage.
    pub ghcb_usage: u32,
}

impl Default for Ghcb {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, G> AsMut<GhcbProtocol<'a, G>> for GhcbProtocol<'a, G>
where
    G: AsMut<Ghcb> + AsRef<Ghcb> + ?Sized,
{
    #[inline]
    fn as_mut(&mut self) -> &mut GhcbProtocol<'a, G> {
        self
    }
}

impl<'a, G> AsRef<GhcbProtocol<'a, G>> for GhcbProtocol<'a, G>
where
    G: AsMut<Ghcb> + AsRef<Ghcb> + ?Sized,
{
    #[inline]
    fn as_ref(&self) -> &GhcbProtocol<'a, G> {
        self
    }
}

impl AsMut<Ghcb> for Ghcb {
    #[inline]
    fn as_mut(&mut self) -> &mut Ghcb {
        self
    }
}

impl AsRef<Ghcb> for Ghcb {
    #[inline]
    fn as_ref(&self) -> &Ghcb {
        self
    }
}

static_assertions::assert_eq_size!(Ghcb, [u8; GHCB_PAGE_SIZE]);

/// Flags indicating which fields in a specific GHCB instance are valid.
#[derive(Debug, Default, FromBytes)]
#[repr(transparent)]
pub struct ValidBitmap(u128);

bitflags! {
    impl ValidBitmap: u128 {
        const CPL = (1 << 25);
        const XSS = (1 << 40);
        const DR7 = (1 << 44);
        const RAX = (1 << 63);
        const RCX = (1 << 97);
        const RDX = (1 << 98);
        const RBX = (1 << 99);
        const SW_EXIT_CODE = (1 << 114);
        const SW_EXIT_INFO_1 = (1 << 115);
        const SW_EXIT_INFO_2 = (1 << 116);
        const SW_SCRATCH = (1 << 117);
        const XCR0 = (1 << 125);
    }
}

impl Ghcb {
    pub const fn new() -> Self {
        Ghcb {
            _reserved_0: [0; 203],
            cpl: 0,
            _reserved_1: [0; 116],
            xss: 0,
            _reserved_2: [0; 24],
            dr7: 0,
            _reserved_3: [0; 144],
            rax: 0,
            _reserved_4: [0; 264],
            rbx: 0,
            rcx: 0,
            rdx: 0,
            _reserved_5: [0; 112],
            sw_exit_code: 0,
            sw_exit_info_1: 0,
            sw_exit_info_2: 0,
            sw_scratch: 0,
            _reserved_6: [0; 56],
            xcr0: 0,
            valid_bitmap: ValidBitmap::empty(),
            x87_state_gpa: 0,
            _reserved_7: [0; 1016],
            shared_buffer: [0; 2032],
            _reserved_8: [0; 10],
            protocol_version: 0,
            ghcb_usage: 0,
        }
    }

    /// Zeroes the entire GHCB.
    pub fn reset(&mut self) {
        reset_slice(&mut self._reserved_0[..]);
        self.cpl = 0;
        reset_slice(&mut self._reserved_1[..]);
        self.xss = 0;
        reset_slice(&mut self._reserved_2[..]);
        self.dr7 = 0;
        reset_slice(&mut self._reserved_3[..]);
        self.rax = 0;
        reset_slice(&mut self._reserved_4[..]);
        self.rbx = 0;
        self.rcx = 0;
        self.rcx = 0;
        reset_slice(&mut self._reserved_5[..]);
        self.sw_exit_code = 0;
        self.sw_exit_info_1 = 0;
        self.sw_exit_info_2 = 0;
        self.sw_scratch = 0;
        reset_slice(&mut self._reserved_6[..]);
        self.xcr0 = 0;
        self.valid_bitmap = ValidBitmap::empty();
        self.x87_state_gpa = 0;
        reset_slice(&mut self._reserved_7[..]);
        reset_slice(&mut self.shared_buffer[..]);
        reset_slice(&mut self._reserved_8[..]);
        self.protocol_version = 0;
        self.ghcb_usage = 0;
    }
}

/// Implementation of the GHCB protocol using the wrapped GHCB data structure.
pub struct GhcbProtocol<'a, G: AsMut<Ghcb> + ?Sized> {
    ghcb: &'a mut G,
    gpa: PhysAddr,
}

impl<'a, G> GhcbProtocol<'a, G>
where
    G: AsMut<Ghcb> + AsRef<Ghcb> + ?Sized,
{
    pub fn new<VP: Translator>(ghcb: &'a mut G, translate: VP) -> Self {
        let virtual_address = VirtAddr::from_ptr(ghcb.as_ref() as *const Ghcb);
        // Crashing is OK if we cannot find the physical address for the GHCB.
        let gpa = translate(virtual_address)
            .expect("couldn't translate the GHCB virtual address to a physical address");
        Self { ghcb, gpa }
    }

    /// Resets all of the inner GHCB information to its original state.
    pub fn reset(&mut self) {
        self.ghcb.as_mut().reset();
    }

    /// Gets the guest-physical address for the guest-hypervisor communication block.
    pub fn get_gpa(&self) -> PhysAddr {
        self.gpa
    }

    /// Registers the address of the GHCB with the hypervisor.
    pub fn register_with_hypervisor(&self) -> Result<(), RegisterGhcbGpaError> {
        register_ghcb_location(RegisterGhcbGpaRequest::new(
            self.get_gpa().as_u64() as usize
        )?)
    }

    /// Writes an 8 bit number to an IO port via the IOIO protocol.
    ///
    /// See section 4.1.2 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
    pub fn io_write_u8(&mut self, port: u16, data: u8) -> Result<(), &'static str> {
        let io_port = IOIO_ADDRESS_SIZE_16 | IOIO_DATA_SIZE_8 | ((port as u64) << 16);

        self.ghcb.as_mut().sw_exit_code = SW_EXIT_CODE_IOIO_PROT;
        self.ghcb.as_mut().sw_exit_info_1 = io_port;
        self.ghcb.as_mut().sw_exit_info_2 = 0;
        self.ghcb.as_mut().rax = data as u64;
        self.ghcb.as_mut().valid_bitmap = BASE_VALID_BITMAP.union(ValidBitmap::RAX);
        self.do_vmg_exit()
    }

    /// Read an 8 bit number from an IO port via the IOIO protocol.
    ///
    /// See section 4.1.2 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
    pub fn io_read_u8(&mut self, port: u16) -> Result<u8, &'static str> {
        let io_port = IOIO_ADDRESS_SIZE_16 | IOIO_DATA_SIZE_8 | IOIO_READ | ((port as u64) << 16);

        self.ghcb.as_mut().sw_exit_code = SW_EXIT_CODE_IOIO_PROT;
        self.ghcb.as_mut().sw_exit_info_1 = io_port;
        self.ghcb.as_mut().sw_exit_info_2 = 0;
        self.ghcb.as_mut().valid_bitmap = BASE_VALID_BITMAP;
        self.do_vmg_exit()?;
        Ok(self.ghcb.as_mut().rax as u8)
    }

    /// Writes a 16 bit number to an IO port via the IOIO protocol.
    ///
    /// See section 4.1.2 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
    pub fn io_write_u16(&mut self, port: u16, data: u16) -> Result<(), &'static str> {
        let io_port = IOIO_ADDRESS_SIZE_16 | IOIO_DATA_SIZE_16 | ((port as u64) << 16);

        self.ghcb.as_mut().sw_exit_code = SW_EXIT_CODE_IOIO_PROT;
        self.ghcb.as_mut().sw_exit_info_1 = io_port;
        self.ghcb.as_mut().sw_exit_info_2 = 0;
        self.ghcb.as_mut().rax = data as u64;
        self.ghcb.as_mut().valid_bitmap = BASE_VALID_BITMAP.union(ValidBitmap::RAX);
        self.do_vmg_exit()
    }

    /// Read a 16 bit number from an IO port via the IOIO protocol.
    ///
    /// See section 4.1.2 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
    pub fn io_read_u16(&mut self, port: u16) -> Result<u16, &'static str> {
        let io_port = IOIO_ADDRESS_SIZE_16 | IOIO_DATA_SIZE_16 | IOIO_READ | ((port as u64) << 16);

        self.ghcb.as_mut().sw_exit_code = SW_EXIT_CODE_IOIO_PROT;
        self.ghcb.as_mut().sw_exit_info_1 = io_port;
        self.ghcb.as_mut().sw_exit_info_2 = 0;
        self.ghcb.as_mut().valid_bitmap = BASE_VALID_BITMAP;
        self.do_vmg_exit()?;
        Ok(self.ghcb.as_mut().rax as u16)
    }

    /// Writes a 32 bit number to an IO port via the IOIO protocol.
    ///
    /// See section 4.1.2 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
    pub fn io_write_u32(&mut self, port: u16, data: u32) -> Result<(), &'static str> {
        let io_port = IOIO_ADDRESS_SIZE_16 | IOIO_DATA_SIZE_32 | ((port as u64) << 16);

        self.ghcb.as_mut().sw_exit_code = SW_EXIT_CODE_IOIO_PROT;
        self.ghcb.as_mut().sw_exit_info_1 = io_port;
        self.ghcb.as_mut().sw_exit_info_2 = 0;
        self.ghcb.as_mut().rax = data as u64;
        self.ghcb.as_mut().valid_bitmap = BASE_VALID_BITMAP.union(ValidBitmap::RAX);
        self.do_vmg_exit()
    }

    /// Read a 32 bit number from an IO port via the IOIO protocol.
    ///
    /// See section 4.1.2 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
    pub fn io_read_u32(&mut self, port: u16) -> Result<u32, &'static str> {
        let io_port = IOIO_ADDRESS_SIZE_16 | IOIO_DATA_SIZE_32 | IOIO_READ | ((port as u64) << 16);

        self.ghcb.as_mut().sw_exit_code = SW_EXIT_CODE_IOIO_PROT;
        self.ghcb.as_mut().sw_exit_info_1 = io_port;
        self.ghcb.as_mut().sw_exit_info_2 = 0;
        self.ghcb.as_mut().valid_bitmap = BASE_VALID_BITMAP;
        self.do_vmg_exit()?;
        Ok(self.ghcb.as_mut().rax as u32)
    }

    /// Calls a CPUID function for the given input using the GHCB protocol.
    pub fn get_cpuid(&mut self, request: CpuidInput) -> Result<CpuidOutput, &'static str> {
        let ghcb = self.ghcb.as_mut();
        ghcb.sw_exit_code = SW_EXIT_CODE_CPUID;
        ghcb.sw_exit_info_1 = 0;
        ghcb.sw_exit_info_2 = 0;
        ghcb.rax = request.eax as u64;
        ghcb.rcx = request.ecx as u64;
        ghcb.xcr0 = request.xcr0;
        // We don't set the value for XSS , as it is not supported for SEV-ES (v1 of the GHCB
        // protocol). We can use the CPUID page when SEV-SNP is enabled so this function will only
        // be used with SEV-ES.
        ghcb.valid_bitmap = BASE_VALID_BITMAP
            .union(ValidBitmap::RAX)
            .union(ValidBitmap::RCX)
            .union(ValidBitmap::XCR0);
        self.do_vmg_exit()?;
        let ghcb = self.ghcb.as_mut();
        Ok(CpuidOutput {
            eax: ghcb.rax as u32,
            ebx: ghcb.rbx as u32,
            ecx: ghcb.rcx as u32,
            edx: ghcb.rdx as u32,
        })
    }

    /// Writes a value to the specified model-specific register.
    ///
    /// See section 4.1.3 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
    pub fn msr_write(&mut self, msr: u32, data: u64) -> Result<(), &'static str> {
        self.ghcb.as_mut().sw_exit_code = SW_EXIT_CODE_MSR_PROT;
        self.ghcb.as_mut().sw_exit_info_1 = 1;
        self.ghcb.as_mut().sw_exit_info_2 = 0;
        self.ghcb.as_mut().rcx = msr as u64;
        // Split the data into the lower halves of RDX and RAX.
        self.ghcb.as_mut().rax = data & MSR_REGISTER_MASK;
        self.ghcb.as_mut().rdx = data >> 32;
        self.ghcb.as_mut().valid_bitmap = BASE_VALID_BITMAP
            .union(ValidBitmap::RAX)
            .union(ValidBitmap::RCX)
            .union(ValidBitmap::RDX);
        self.do_vmg_exit()
    }

    /// Reads a value from the specified model-specific register.
    ///
    /// See section 4.1.2 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
    pub fn msr_read(&mut self, msr: u32) -> Result<u64, &'static str> {
        self.ghcb.as_mut().sw_exit_code = SW_EXIT_CODE_MSR_PROT;
        self.ghcb.as_mut().sw_exit_info_1 = 0;
        self.ghcb.as_mut().sw_exit_info_2 = 0;
        self.ghcb.as_mut().rcx = msr as u64;
        self.ghcb.as_mut().valid_bitmap = BASE_VALID_BITMAP.union(ValidBitmap::RCX);
        self.do_vmg_exit()?;
        // Reconstruct the value from the lower halves of RAX and RDX.
        let low = self.ghcb.as_mut().rax & MSR_REGISTER_MASK;
        let high = self.ghcb.as_mut().rdx & MSR_REGISTER_MASK;
        Ok(low | (high << 32))
    }

    /// Sends a guest request message to the Platform Secure Processor via the Guest Message
    /// Protocol.
    ///
    /// The memory containing the request and response data must already be shared with the
    /// hypervisor.
    pub fn do_guest_message_request(
        &mut self,
        request_address: PhysAddr,
        response_address: PhysAddr,
    ) -> Result<(), &'static str> {
        let ghcb = self.ghcb.as_mut();
        ghcb.sw_exit_code = SW_EXIT_CODE_GUEST_REQUEST;
        ghcb.sw_exit_info_1 = request_address.as_u64();
        ghcb.sw_exit_info_2 = response_address.as_u64();
        ghcb.valid_bitmap = BASE_VALID_BITMAP;
        self.do_vmg_exit()?;
        if self.ghcb.as_mut().sw_exit_info_2 == 0 {
            Ok(())
        } else {
            // For now we treat all non-zero return values as unrecoverable errors.
            Err("guest message response indicates an error")
        }
    }

    /// Sets the address of the GHCB, exits to the hypervisor, and checks the return value when
    /// execution resumes.
    fn do_vmg_exit(&mut self) -> Result<(), &'static str> {
        self.ghcb.as_mut().protocol_version = GHCB_PROTOCOL_VERSION;
        // Use a memory fence to ensure all writes happen before we hand over to the VMM.
        core::sync::atomic::fence(core::sync::atomic::Ordering::SeqCst);
        set_ghcb_address_and_exit(GhcbGpa::new(self.get_gpa().as_u64() as usize)?);
        // Use a memory fence to ensure that all earlier writes are commited before we read from the
        // GHCB.
        core::sync::atomic::fence(core::sync::atomic::Ordering::SeqCst);

        // The mask for extracting the hypervisor's return value from the sw_exit_info_1 field.
        const SW_EXIT_INFO_1_RETURN_MASK: u64 = 0xffff_ffff;

        if self.ghcb.as_mut().sw_exit_info_1 & SW_EXIT_INFO_1_RETURN_MASK == 0 {
            Ok(())
        } else {
            // For now we treat all non-zero return values as unrecoverable errors.
            Err("VMGEXIT call returned an error")
        }
    }
}

/// Resets a byte slice to all zeroes.
fn reset_slice(slice: &mut [u8]) {
    for byte in slice {
        *byte = 0;
    }
}
