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

//! This module contains an implementation of the guest-hypervisor
//! communications block (GHCB) page that can be used for communicating with the
//! hypervisor.

use bitflags::bitflags;
use x86_64::{
    structures::paging::{page::NotGiantPageSize, PageSize, PhysFrame, Size2MiB, Size4KiB},
    PhysAddr, VirtAddr,
};
use zerocopy::{FromBytes, FromZeros, Immutable, IntoBytes};

use crate::{
    cpuid::{CpuidInput, CpuidOutput},
    instructions::PageSize as SevPageSize,
    msr::{
        register_ghcb_location, set_ghcb_address_and_exit, GhcbGpa, PageAssignment,
        RegisterGhcbGpaError, RegisterGhcbGpaRequest,
    },
    Translator,
};

/// The size of the GHCB page.
pub const GHCB_PAGE_SIZE: usize = 4096;

/// The version of the GHCB protocol and page layout that we expect to use.
pub const GHCB_PROTOCOL_VERSION: u16 = 2;

/// The value of the sw_exit_code field when doing the IOIO protocol.
///
/// See section 4.1.2 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
const SW_EXIT_CODE_IOIO_PROT: u64 = 0x7B;

/// The value of the sw_exit_code field when doing the MSR reading or writing
/// protocol.
///
/// See section 4.1.3 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
const SW_EXIT_CODE_MSR_PROT: u64 = 0x7C;

/// The value of the sw_exit_code field when doing a CPUID request.
///
/// See section 4 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
const SW_EXIT_CODE_CPUID: u64 = 0x72;

/// The value of the sw_exit_code field when doing a MMIO read.
///
/// See section 4 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
const SW_EXIT_CODE_MMIO_READ: u64 = 0x8000_0001;

/// The value of the sw_exit_code field when doing a MMIO read.
///
/// See section 4 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
const SW_EXIT_CODE_MMIO_WRITE: u64 = 0x8000_0002;

/// The value of the sw_exit_code field when managing the AP Jump Table under
/// SEV-ES.
///
/// See table 6 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
const SW_EXIT_CODE_AP_JUMP_TABLE: u64 = 0x8000_0005;

///
/// The value of the sw_exit_code field when doing a Page State Change request.
///
/// See table 6 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
const SW_EXIT_CODE_PAGE_STATE_CHANGE: u64 = 0x8000_0010;

///
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
const BASE_VALID_BITMAP: ValidBitmap =
    ValidBitmap::SW_EXIT_CODE.union(ValidBitmap::SW_EXIT_INFO_1).union(ValidBitmap::SW_EXIT_INFO_2);

/// The mask to use on MSR register values.
///
/// RDMSR and WRMSR only use the 32-bit EAX and EDX registers, not 64-bit RAX
/// and RDX, so we only use the least significant 32 bits.
const MSR_REGISTER_MASK: u64 = 0xffff_ffff;

/// Size of the shared buffer space in the GHCB structure.
const SHARED_BUFFER_SIZE: usize = 2032;

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
    /// The value of the IA32_XSS model-specific register.
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
    /// Bitmap indicating which quadwords of the save state area are valid in
    /// the range from offset 0x000 through to offset 0x3ef.
    ///
    /// A flag must be set for each field that is set as part of handling a
    /// non-automatic exit event. The value must also be checked on the
    /// return from the hypervisor.
    pub valid_bitmap: ValidBitmap,
    /// The guest-physical address of the page that contains the x87-related
    /// saved state.
    pub x87_state_gpa: u64,
    /// Reserved. Must be 0.
    _reserved_7: [u8; 1016],
    /// Area that can be used as a shared buffer for communicating additional
    /// information.
    pub shared_buffer: [u8; SHARED_BUFFER_SIZE],
    /// Reserved. Must be 0.
    _reserved_8: [u8; 10],
    /// The version of the GHCB protocol and page layout in use.
    pub protocol_version: u16,
    /// The usage of the GHCB page. A value of 0 indicates the usage is in line
    /// with the definition as specified in this struct. Any other value
    /// indicates a hypervisor-defined usage.
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

    /// Consumes the GHCB protocol, yielding back the underlying GHCB block.
    pub fn into_inner(self) -> &'a mut G {
        self.ghcb
    }

    /// Resets all of the inner GHCB information to its original state.
    pub fn reset(&mut self) {
        self.ghcb.as_mut().reset();
    }

    /// Gets the guest-physical address for the guest-hypervisor communication
    /// block.
    pub fn get_gpa(&self) -> PhysAddr {
        self.gpa
    }

    /// Registers the address of the GHCB with the hypervisor.
    pub fn register_with_hypervisor(&self) -> Result<(), RegisterGhcbGpaError> {
        register_ghcb_location(RegisterGhcbGpaRequest::new(self.get_gpa().as_u64() as usize)?)
    }

    pub fn set_ap_jump_table(&mut self, jump_table: PhysAddr) -> Result<(), &'static str> {
        self.call(|ghcb| {
            ghcb.sw_exit_code = SW_EXIT_CODE_AP_JUMP_TABLE;
            ghcb.sw_exit_info_1 = 0; // SET
            ghcb.sw_exit_info_2 = jump_table.as_u64();
        })
    }

    pub fn get_ap_jump_table(&mut self) -> Result<PhysAddr, &'static str> {
        self.call(|ghcb| {
            ghcb.sw_exit_code = SW_EXIT_CODE_AP_JUMP_TABLE;
            ghcb.sw_exit_info_1 = 1; // GET
            ghcb.sw_exit_info_2 = 0;
        })?;

        Ok(PhysAddr::new(self.ghcb.as_ref().sw_exit_info_2))
    }

    /// Read a 32-bit value from a MMIO memory address via the MMIO Access
    /// protocol.
    ///
    /// See Section 4.1.5 in <https://www.amd.com/content/dam/amd/en/documents/epyc-technical-docs/specifications/56421-guest-hypervisor-communication-block-standardization.pdf>.
    pub fn mmio_read_u32(&mut self, source: PhysAddr) -> Result<u32, &'static str> {
        let gpa_base = self.get_gpa().as_u64();

        self.call(|ghcb| {
            ghcb.sw_exit_code = SW_EXIT_CODE_MMIO_READ;
            ghcb.sw_exit_info_1 = source.as_u64();
            ghcb.sw_exit_info_2 = core::mem::size_of::<u32>() as u64;
            // Use the shared_buffer as the unencrypted guest memory. This is mandated as of
            // Version 2 of the communication block.
            ghcb.sw_scratch = gpa_base + (core::mem::offset_of!(Ghcb, shared_buffer) as u64);
            ghcb.valid_bitmap |= ValidBitmap::SW_SCRATCH;
        })?;

        Ok(u32::from_ne_bytes(
            self.ghcb.as_ref().shared_buffer[0..core::mem::size_of::<u32>()]
                .as_bytes()
                .try_into()
                .unwrap(),
        ))
    }

    /// Write a 32-bit value to a MMIO memory address via the MMIO Access
    /// protocol.
    ///
    /// See Section 4.1.5 in <https://www.amd.com/content/dam/amd/en/documents/epyc-technical-docs/specifications/56421-guest-hypervisor-communication-block-standardization.pdf>.
    pub fn mmio_write_u32(
        &mut self,
        destination: PhysAddr,
        value: u32,
    ) -> Result<(), &'static str> {
        let gpa_base = self.get_gpa().as_u64();

        self.call(|ghcb| {
            ghcb.sw_exit_code = SW_EXIT_CODE_MMIO_WRITE;
            ghcb.sw_exit_info_1 = destination.as_u64();
            ghcb.sw_exit_info_2 = core::mem::size_of::<u32>() as u64;
            // Pointer to `shared_buffer` inside the GHCB.
            ghcb.sw_scratch = gpa_base + (core::mem::offset_of!(Ghcb, shared_buffer) as u64);
            ghcb.valid_bitmap |= ValidBitmap::SW_SCRATCH;
            // Safety: the shared buffer is bigger than an u32.
            ghcb.shared_buffer.as_mut_bytes()[0..core::mem::size_of::<u32>()]
                .copy_from_slice(value.as_bytes());
        })
    }

    /// Writes an 8 bit number to an IO port via the IOIO protocol.
    ///
    /// See section 4.1.2 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
    pub fn io_write_u8(&mut self, port: u16, data: u8) -> Result<(), &'static str> {
        let io_port = IOIO_ADDRESS_SIZE_16 | IOIO_DATA_SIZE_8 | ((port as u64) << 16);

        self.call(|ghcb| {
            ghcb.sw_exit_code = SW_EXIT_CODE_IOIO_PROT;
            ghcb.sw_exit_info_1 = io_port;
            ghcb.sw_exit_info_2 = 0;
            ghcb.rax = data as u64;
            ghcb.valid_bitmap |= ValidBitmap::RAX;
        })
    }

    /// Read an 8 bit number from an IO port via the IOIO protocol.
    ///
    /// See section 4.1.2 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
    pub fn io_read_u8(&mut self, port: u16) -> Result<u8, &'static str> {
        let io_port = IOIO_ADDRESS_SIZE_16 | IOIO_DATA_SIZE_8 | IOIO_READ | ((port as u64) << 16);

        self.call(|ghcb| {
            ghcb.sw_exit_code = SW_EXIT_CODE_IOIO_PROT;
            ghcb.sw_exit_info_1 = io_port;
            ghcb.sw_exit_info_2 = 0;
        })?;
        Ok(self.ghcb.as_ref().rax as u8)
    }

    /// Writes a 16 bit number to an IO port via the IOIO protocol.
    ///
    /// See section 4.1.2 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
    pub fn io_write_u16(&mut self, port: u16, data: u16) -> Result<(), &'static str> {
        let io_port = IOIO_ADDRESS_SIZE_16 | IOIO_DATA_SIZE_16 | ((port as u64) << 16);

        self.call(|ghcb| {
            ghcb.sw_exit_code = SW_EXIT_CODE_IOIO_PROT;
            ghcb.sw_exit_info_1 = io_port;
            ghcb.sw_exit_info_2 = 0;
            ghcb.rax = data as u64;
            ghcb.valid_bitmap |= ValidBitmap::RAX;
        })
    }

    /// Read a 16 bit number from an IO port via the IOIO protocol.
    ///
    /// See section 4.1.2 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
    pub fn io_read_u16(&mut self, port: u16) -> Result<u16, &'static str> {
        let io_port = IOIO_ADDRESS_SIZE_16 | IOIO_DATA_SIZE_16 | IOIO_READ | ((port as u64) << 16);

        self.call(|ghcb| {
            ghcb.sw_exit_code = SW_EXIT_CODE_IOIO_PROT;
            ghcb.sw_exit_info_1 = io_port;
            ghcb.sw_exit_info_2 = 0;
        })?;
        Ok(self.ghcb.as_mut().rax as u16)
    }

    /// Writes a 32 bit number to an IO port via the IOIO protocol.
    ///
    /// See section 4.1.2 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
    pub fn io_write_u32(&mut self, port: u16, data: u32) -> Result<(), &'static str> {
        let io_port = IOIO_ADDRESS_SIZE_16 | IOIO_DATA_SIZE_32 | ((port as u64) << 16);

        self.call(|ghcb| {
            ghcb.sw_exit_code = SW_EXIT_CODE_IOIO_PROT;
            ghcb.sw_exit_info_1 = io_port;
            ghcb.sw_exit_info_2 = 0;
            ghcb.rax = data as u64;
            ghcb.valid_bitmap |= ValidBitmap::RAX;
        })
    }

    /// Read a 32 bit number from an IO port via the IOIO protocol.
    ///
    /// See section 4.1.2 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
    pub fn io_read_u32(&mut self, port: u16) -> Result<u32, &'static str> {
        let io_port = IOIO_ADDRESS_SIZE_16 | IOIO_DATA_SIZE_32 | IOIO_READ | ((port as u64) << 16);

        self.call(|ghcb| {
            ghcb.sw_exit_code = SW_EXIT_CODE_IOIO_PROT;
            ghcb.sw_exit_info_1 = io_port;
            ghcb.sw_exit_info_2 = 0;
        })?;
        Ok(self.ghcb.as_mut().rax as u32)
    }

    /// Calls a CPUID function for the given input using the GHCB protocol.
    pub fn get_cpuid(&mut self, request: CpuidInput) -> Result<CpuidOutput, &'static str> {
        self.call(|ghcb| {
            ghcb.sw_exit_code = SW_EXIT_CODE_CPUID;
            ghcb.sw_exit_info_1 = 0;
            ghcb.sw_exit_info_2 = 0;
            ghcb.rax = request.eax as u64;
            ghcb.rcx = request.ecx as u64;
            ghcb.xcr0 = request.xcr0;
            // We don't set the value for XSS , as it is not supported for SEV-ES (v1 of the
            // GHCB protocol). We can use the CPUID page when SEV-SNP is enabled so
            // this function will only be used with SEV-ES.
            ghcb.valid_bitmap |= ValidBitmap::RAX | ValidBitmap::RCX | ValidBitmap::XCR0;
        })?;
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
        self.call(|ghcb| {
            ghcb.sw_exit_code = SW_EXIT_CODE_MSR_PROT;
            ghcb.sw_exit_info_1 = 1;
            ghcb.sw_exit_info_2 = 0;
            ghcb.rcx = msr as u64;
            // Split the data into the lower halves of RDX and RAX.
            ghcb.rax = data & MSR_REGISTER_MASK;
            ghcb.rdx = data >> 32;
            ghcb.valid_bitmap |= ValidBitmap::RAX | ValidBitmap::RCX | ValidBitmap::RDX;
        })
    }

    /// Reads a value from the specified model-specific register.
    ///
    /// See section 4.1.2 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
    pub fn msr_read(&mut self, msr: u32) -> Result<u64, &'static str> {
        self.call(|ghcb| {
            ghcb.sw_exit_code = SW_EXIT_CODE_MSR_PROT;
            ghcb.sw_exit_info_1 = 0;
            ghcb.sw_exit_info_2 = 0;
            ghcb.rcx = msr as u64;
            ghcb.valid_bitmap |= ValidBitmap::RCX;
        })?;
        // Reconstruct the value from the lower halves of RAX and RDX.
        let low = self.ghcb.as_ref().rax & MSR_REGISTER_MASK;
        let high = self.ghcb.as_ref().rdx & MSR_REGISTER_MASK;
        Ok(low | (high << 32))
    }

    /// Sends a guest request message to the Platform Secure Processor via the
    /// Guest Message Protocol.
    ///
    /// The memory containing the request and response data must already be
    /// shared with the hypervisor.
    pub fn do_guest_message_request(
        &mut self,
        request_address: PhysAddr,
        response_address: PhysAddr,
    ) -> Result<(), &'static str> {
        self.call(|ghcb| {
            ghcb.sw_exit_code = SW_EXIT_CODE_GUEST_REQUEST;
            ghcb.sw_exit_info_1 = request_address.as_u64();
            ghcb.sw_exit_info_2 = response_address.as_u64();
        })?;
        if self.ghcb.as_ref().sw_exit_info_2 == 0 {
            Ok(())
        } else {
            // For now we treat all non-zero return values as unrecoverable errors.
            Err("guest message response indicates an error")
        }
    }

    /// Performs a Page State Change operation on the given physical frame.
    ///
    /// See section 4.1.6 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
    pub fn page_state_change<S: NotGiantPageSize>(
        &mut self,
        frame: PhysFrame<S>,
        assignment: PageAssignment,
    ) -> Result<(), &'static str> {
        let mut page_state_change = PageStateChange::new_zeroed();
        page_state_change.header.cur_entry = 0;
        page_state_change.header.end_entry = 0;
        page_state_change.entry[0] =
            PageStateChangeEntry { page_operation: assignment, gfn: frame, current_page: 0 }.into();

        let gpa_base = self.get_gpa().as_u64();
        self.call(|ghcb| {
            ghcb.sw_exit_code = SW_EXIT_CODE_PAGE_STATE_CHANGE;
            ghcb.sw_scratch = gpa_base + (core::mem::offset_of!(Ghcb, shared_buffer) as u64);
            page_state_change
                .write_to(&mut ghcb.shared_buffer)
                .expect("Unexpected length mismatch between PSC request and GHCB shared buffer");
            ghcb.valid_bitmap |= ValidBitmap::SW_SCRATCH;
        })?;

        let ghcb = self.ghcb.as_ref();
        let page_state_change = PageStateChange::read_from_bytes(&ghcb.shared_buffer)
            .map_err(|_| "Unexpected length mismatch between PSC request and GHCB shared buffer")?;
        // If cur_entry did not move past end_entry, SW_EXITINFO2 will contain
        // additional information. For now, we just return a generic error.
        if page_state_change.header.cur_entry <= page_state_change.header.end_entry {
            return Err("cur_entry did not move!");
        };
        // According to documentation the `current_page` field in each
        // `PageStateChangeEntry` struct should change to show that a page has been
        // successfully processed, but I always get zeroes there.
        Ok(())
    }

    /// Simple wrapper for operations that rely on the GHCB.
    fn call<F>(&mut self, func: F) -> Result<(), &'static str>
    where
        F: FnOnce(&mut Ghcb),
    {
        let ghcb = self.ghcb.as_mut();
        ghcb.reset();
        ghcb.valid_bitmap = BASE_VALID_BITMAP;
        func(ghcb);
        self.do_vmg_exit()
    }

    /// Sets the address of the GHCB, exits to the hypervisor, and checks the
    /// return value when execution resumes.
    fn do_vmg_exit(&mut self) -> Result<(), &'static str> {
        self.ghcb.as_mut().protocol_version = GHCB_PROTOCOL_VERSION;
        // Use a memory fence to ensure all writes happen before we hand over to the
        // VMM.
        core::sync::atomic::fence(core::sync::atomic::Ordering::SeqCst);
        set_ghcb_address_and_exit(GhcbGpa::new(self.get_gpa().as_u64() as usize)?);
        // Use a memory fence to ensure that all earlier writes are commited before we
        // read from the GHCB.
        core::sync::atomic::fence(core::sync::atomic::Ordering::SeqCst);

        // The mask for extracting the hypervisor's return value from the sw_exit_info_1
        // field.
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

#[repr(C)]
#[derive(IntoBytes, FromBytes, Immutable)]
struct PageStateChangeHeader {
    cur_entry: u16,
    end_entry: u16,
    _reserved: u32,
}

/// Page State Change structure.
///
/// See section 4.1.6 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
#[repr(C)]
#[derive(IntoBytes, FromBytes, Immutable)]
struct PageStateChange {
    header: PageStateChangeHeader,
    entry: [u64; 253],
}
static_assertions::assert_eq_size!(PageStateChange, [u8; SHARED_BUFFER_SIZE]);

/// Page State Change Entry.
///
/// See Table 9 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>.
struct PageStateChangeEntry<S: NotGiantPageSize> {
    page_operation: PageAssignment,

    /// Physical frame in guest memory for the operation.
    gfn: PhysFrame<S>,

    /// Input: offset, in 4K increments, on which to bein the page state change
    /// operation. Output: offset of the current page in 4K increments that
    /// has been successfully processed.
    current_page: u16,
}

impl<S: NotGiantPageSize> From<PageStateChangeEntry<S>> for u64 {
    fn from(value: PageStateChangeEntry<S>) -> Self {
        // [63:57]: Reserved, must be zero. Reset the whole thing to zero.
        let mut entry = 0u64;
        // [56]: Page size.
        entry |= match S::SIZE {
            Size4KiB::SIZE => (SevPageSize::Page4KiB as u64) << 56,
            Size2MiB::SIZE => (SevPageSize::Page2MiB as u64) << 56,
            _ => unreachable!("Unexpected non-giant page size (not 4 KiB or 2 MiB)"),
        };
        // [55:52]: Page operation.
        entry |= (value.page_operation as u64) << 52;
        // [51:12]: Guest physical frame number
        // PhysFrame guarantees that the address is properly aligned.
        entry |= value.gfn.start_address().as_u64();
        // [11:0]: Current page.
        entry |= (value.current_page as u64) & 0xFFF;
        entry
    }
}

impl<S: NotGiantPageSize> TryFrom<u64> for PageStateChangeEntry<S> {
    type Error = &'static str;

    fn try_from(value: u64) -> Result<Self, Self::Error> {
        let page_operation = PageAssignment::from_repr(((value & 0x10_0000_0000_0000) >> 52) as u8)
            .ok_or("Invalid page assignment field value")?;
        let address = PhysAddr::new(value & 0x000F_FFFF_FFFF_F000);
        let gfn =
            PhysFrame::from_start_address(address).map_err(|_| "Frame address not aligned")?;
        let current_page = (value & 0x0FFF) as u16;

        Ok(PageStateChangeEntry { page_operation, gfn, current_page })
    }
}
