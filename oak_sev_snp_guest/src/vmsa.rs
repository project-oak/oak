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

//! This module provides an implementation of the State Save Area (VMSA) that is used to store
//! encrypted CPU-related state on AMD SEV-ES and SEV-SNP.

// TODO(#3703): Remove when fixed.
#![allow(clippy::extra_unused_type_parameters)]

use zerocopy::{AsBytes, FromBytes, FromZeroes};

pub const VMSA_PAGE_SIZE: usize = 4096;

pub const VMSA_SIZE: usize = 1992;

/// The page containing the Save State Area used for SEV-ES and SEV-SNP.
///
/// The VMSA for each vCPU is stored in a separate 4KiB page.
#[repr(C, align(4096))]
#[derive(Debug, FromZeroes, FromBytes, AsBytes)]
pub struct VmsaPage {
    pub vmsa: Vmsa,
    _reserved: [u8; VMSA_PAGE_SIZE - VMSA_SIZE],
}

static_assertions::assert_eq_size!(VmsaPage, [u8; VMSA_PAGE_SIZE]);

impl VmsaPage {
    pub fn new(vmsa: Vmsa) -> Self {
        Self {
            vmsa,
            _reserved: [0u8; VMSA_PAGE_SIZE - VMSA_SIZE],
        }
    }
}

impl Default for VmsaPage {
    fn default() -> Self {
        // We cannot derive Default because Default is only implemented for fixed-size arrays up to
        // size 32.
        Self {
            vmsa: Vmsa::default(),
            _reserved: [0u8; VMSA_PAGE_SIZE - VMSA_SIZE],
        }
    }
}

/// The State Save Area used for SEV-ES and SEV-SNP.
///
/// See table B-4 in <https://www.amd.com/system/files/TechDocs/24593.pdf>
#[repr(C)]
#[derive(Debug, FromZeroes, FromBytes, AsBytes)]
pub struct Vmsa {
    /// The extra segment.
    pub es: SegmentRegister,
    /// The code segment.
    pub cs: SegmentRegister,
    /// The stack segment.
    pub ss: SegmentRegister,
    /// The data segment.
    pub ds: SegmentRegister,
    /// General purpose segment.
    pub fs: SegmentRegister,
    /// General purpose segment.
    pub gs: SegmentRegister,
    /// Pointer to the global descriptor table.
    pub gdtr: SegmentRegister,
    /// Pointer to the local descriptor table.
    pub ldtr: SegmentRegister,
    /// Pointer to the interrupt descriptor table.
    pub idtr: SegmentRegister,
    /// Pointer to a valid task state secgement in the global descriptor table.
    pub tr: SegmentRegister,
    /// Shadow stack pointer for ring 0.
    pub pl0_ssp: u64,
    /// Shadow stack pointer for ring 1.
    pub pl1_ssp: u64,
    /// Shadow stack pointer for ring 2.
    pub pl2_ssp: u64,
    /// Shadow stack pointer for ring 3.
    pub pl3_ssp: u64,
    /// Shadow stack MSR for user mode settings.
    pub u_cet: u64,
    /// Reserved.
    _reserved_0: u16,
    /// The current VM protection level.
    pub vmpl: u8,
    /// The current protection level (ring).
    pub cpl: u8,
    /// Reserved.
    _reserved_1: u32,
    /// The extended feature enable register.
    pub efer: u64,
    /// Reserved.
    _reserved_2: [u8; 104],
    /// The IA32_XSS machine-specific register.
    pub xss: u64,
    /// Control Register 4.
    pub cr4: u64,
    /// Control Register 3.
    pub cr3: u64,
    /// Control Register 0.
    pub cr0: u64,
    /// Debug register 7.
    pub dr7: u64,
    /// Debug register 6.
    pub dr6: u64,
    /// The 64-bit flags register.
    pub rflags: u64,
    /// The instruction pointer.
    pub rip: u64,
    /// Debug register 0.
    pub dr0: u64,
    /// Debug register 1.
    pub dr1: u64,
    /// Debug register 2.
    pub dr2: u64,
    /// Debug register 3.
    pub dr3: u64,
    /// Debug register 0 address mask.
    pub dr0_addr_mask: u64,
    /// Debug register 1 address mask.
    pub dr1_addr_mask: u64,
    /// Debug register 2 address mask.
    pub dr2_addr_mask: u64,
    /// Debug register 3 address mask.
    pub dr3_addr_mask: u64,
    /// Reserved.
    _reserved_3: [u8; 24],
    /// The stack pointer.
    pub rsp: u64,
    /// Shadow stack MSR for supervisor mode settings.
    pub s_cet: u64,
    /// The shadow stack pointer.
    pub ssp: u64,
    /// The address of the interrupt shadow stack.
    pub isst_addr: u64,
    /// The RAX register.
    pub rax: u64,
    /// The target address, code segment and stack segment when making a syscall in legacy mode.
    pub star: u64,
    /// The target instruction pointer when making a syscall in 64-bit mode.
    pub lstar: u64,
    /// The target instruction pointer when making a syscall in compatibility mode.
    pub cstar: u64,
    /// The syscall flag mask.
    pub sfmask: u64,
    /// Register used by the SWAPGS instruction to swap the base of the GS general purpose segment.
    pub kernel_gs_base: u64,
    /// The code segment when using SYSENTER or SYSEXIT in legacy mode.
    pub sysenter_cs: u64,
    /// The stack pointer when using SYSENTER or SYSEXIT in legacy mode.
    pub sysenter_esp: u64,
    /// The instruction pointer when using SYSENTER or SYSEXIT in legacy mode.
    pub sysenter_eip: u64,
    /// The CR2 control register.
    pub cr2: u64,
    /// Reserved.
    _reserved_4: [u8; 32],
    /// The page attribute table for the guest.
    pub g_pat: u64,
    /// The value of the guest's DebugCTL MSR.
    pub dbgctl: u64,
    /// The value of the guest's LastBranchFromIP MSR.
    pub br_from: u64,
    /// The value of the guest's LastBranchToIP MSR.
    pub br_to: u64,
    /// The value of the guest's LastIntFromIP MSR.
    pub last_excp_from: u64,
    /// The value of the guest's LastIntToIP MSR.
    pub last_excp_to: u64,
    /// Reserved.
    _reserved_5: [u8; 80],
    /// The protect keys rights register.
    pub pkru: u32,
    /// Additional information read by the RDTSC instruction.
    pub tsc_aux: u32,
    /// The guest's time stamp counter scaling factor.
    pub guest_tsc_scale: u64,
    /// The guests time stamp counter offset.
    pub guest_tsc_offset: u64,
    /// Nonce used when VMSA register protection is enabled.
    pub reg_prot_nonce: u64,
    /// The RCX register.
    pub rcx: u64,
    /// The RDX register.
    pub rdx: u64,
    /// The RBX register.
    pub rbx: u64,
    /// Reserved.
    _reserved_6: u64,
    /// The RBP register.
    pub rbp: u64,
    /// The RSI register.
    pub rsi: u64,
    /// The RDI register.
    pub rdi: u64,
    /// The R8 register.
    pub r8: u64,
    /// The R9 register.
    pub r9: u64,
    /// The R10 register.
    pub r10: u64,
    /// The R11 register.
    pub r11: u64,
    /// The R12 register.
    pub r12: u64,
    /// The R13 register.
    pub r13: u64,
    /// The R14 register.
    pub r14: u64,
    /// The R14 register.
    pub r15: u64,
    /// Reserved.
    _reserved_7: [u8; 16],
    /// The info 1 value for automatic exits.
    pub guest_exit_info_1: u64,
    /// The info 2 value for automatic exits.
    pub guest_exit_info_2: u64,
    /// The interrupt info value for automatic exits.
    pub guest_exit_int_info: u64,
    /// The next instruction pointer for automatic exits.
    pub guest_nrip: u64,
    /// The guest-controlled SEV features that are selected.
    pub sev_features: u64,
    /// The guest-controlled interrupt injection control settings.
    pub vintr_ctrl: u64,
    /// The exit code for automatic exits.
    pub guest_exit_code: u64,
    /// The virtual top-of-memory setting for the guest.
    pub virtual_tom: u64,
    /// Used by the hardware to track TLB information for the guest.
    pub tlb_id: u64,
    /// Used to control flushing of the guest TLB. Writing 0 to this value will cause the TLB to be
    /// flushed on the next VMRUN.
    pub pcpu_id: u64,
    /// Field used for injecting events into the guest.
    pub event_inj: u64,
    /// The XCR0 extended control register.
    pub xcr0: u64,
    /// Reserved.
    _reserved_8: [u8; 16],
    /// The X87 floating point data pointer.
    pub x87_dp: u64,
    /// The Media eXtensions Control and Status Register.
    pub mxcsr: u32,
    /// The X87 floating point tag word.
    pub x87_ftw: u16,
    /// The X87 floating point status word.
    pub x87_fsw: u16,
    /// The X87 floating point control word.
    pub x87_fcw: u16,
    /// The X87 floating point opcode.
    pub x87_fop: u16,
    /// The X87 floating point data segment.
    pub x87_ds: u16,
    /// The X87 floating point code segment.
    pub x87_cs: u16,
    /// The X87 instruction pointer.
    pub x87_rip: u64,
    /// The X87 register state.
    pub fpreg_x87: [u8; 80],
    /// The XMM register state.
    pub fpreg_xmm: [u8; 256],
    /// The YMM register state.
    pub fpreg_ymm: [u8; 256],
    /// The last branch record stack state.
    pub lbr_stack_state: [u8; 256],
    /// The value of the guest's LastBranchStackSelect MSR.
    pub lbr_select: u64,
    /// The value of the guest's IbsFetchCtl MSR.
    pub ibs_fetch_ctl: u64,
    /// The value of the guest's IbsFetchCtl MSR.
    pub ibs_fetch_lin_addr: u64,
    /// The value of the guest's IbsOfCtl MSR.
    pub ibs_op_ctl: u64,
    /// The value of the guest's IbsOpRip MSR.
    pub ibs_op_rop: u64,
    /// The value of the guest's IbsOpData1 MSR.
    pub ibs_op_data: u64,
    /// The value of the guest's IbsOpData2 MSR.
    pub ibs_op_data2: u64,
    /// The value of the guest's IbsOpData3 MSR.
    pub ibs_op_data3: u64,
    /// The value of the guest's IbsDcLinAd MSR.
    pub ibs_dc_lin_addr: u64,
    /// The value of the guest's IbsBrTarget MSR.
    pub bp_ibs_tgt_rip: u64,
    /// The value of the guest's IbsFetchExtdCtl MSR.
    pub ic_ibs_extd_ctl: u64,
}

static_assertions::assert_eq_size!(Vmsa, [u8; VMSA_SIZE]);

impl Vmsa {
    /// Creates a new instance of the VMSA that represents the state of a newly reset vCPU at boot
    /// time.
    ///
    /// The current implementation tries to match the state of a new vCPU on QEMU running with KVM.
    ///
    /// The value of RDX depends on the family, model and stepping of the CPU and can be calculated
    /// using `calculate_rdx_from_fms`.
    ///
    /// For reference see <https://github.com/qemu/qemu/blob/master/target/i386/cpu.h>,
    /// <https://github.com/qemu/qemu/blob/master/target/i386/cpu.c> and
    /// <https://github.com/qemu/qemu/blob/master/target/i386/kvm.c>.
    pub fn new_vcpu_boot(rdx: u64) -> Self {
        Self {
            cs: SegmentRegister {
                selector: 0xf000,
                attributes: 0x9b, // (P|S|CS|R|A)
                limit: 0xffff,
                base: 0xffff0000,
            },
            ds: SegmentRegister {
                limit: 0xffff,
                attributes: 0x93, // (P|S|W|A)
                ..Default::default()
            },
            es: SegmentRegister {
                limit: 0xffff,
                attributes: 0x93, // (P|S|W|A)
                ..Default::default()
            },
            fs: SegmentRegister {
                limit: 0xffff,
                attributes: 0x93, // (P|S|W|A)
                ..Default::default()
            },
            gs: SegmentRegister {
                limit: 0xffff,
                attributes: 0x93, // (P|S|W|A)
                ..Default::default()
            },
            ss: SegmentRegister {
                limit: 0xffff,
                attributes: 0x93, // (P|S|W|A)
                ..Default::default()
            },
            gdtr: SegmentRegister {
                limit: 0xffff,
                ..Default::default()
            },
            idtr: SegmentRegister {
                limit: 0xffff,
                ..Default::default()
            },
            ldtr: SegmentRegister {
                limit: 0xffff,
                attributes: 0x82, // (P|LDT)
                ..Default::default()
            },
            tr: SegmentRegister {
                limit: 0xffff,
                attributes: 0x8b, // (P|"Busy 32-bit TSS")
                ..Default::default()
            },
            dr6: 0xffff0ff0,
            dr7: 0x0400,
            cr0: 0x10,
            cr4: 0x40,
            xcr0: 0x1,
            efer: 0x1000,
            g_pat: 0x0007040600070406,
            rflags: 0x2,
            rip: 0xfff0,
            rdx,

            ..Default::default()
        }
    }
}

impl Default for Vmsa {
    fn default() -> Self {
        // We cannot derive Default because Default is only implemented for fixed-size arrays up to
        // size 32.
        Self {
            es: SegmentRegister::default(),
            cs: SegmentRegister::default(),
            ss: SegmentRegister::default(),
            ds: SegmentRegister::default(),
            fs: SegmentRegister::default(),
            gs: SegmentRegister::default(),
            gdtr: SegmentRegister::default(),
            ldtr: SegmentRegister::default(),
            idtr: SegmentRegister::default(),
            tr: SegmentRegister::default(),
            pl0_ssp: 0,
            pl1_ssp: 0,
            pl2_ssp: 0,
            pl3_ssp: 0,
            u_cet: 0,
            _reserved_0: 0,
            vmpl: 0,
            cpl: 0,
            _reserved_1: 0,
            efer: 0,
            _reserved_2: [0; 104],
            xss: 0,
            cr4: 0,
            cr3: 0,
            cr0: 0,
            dr7: 0,
            dr6: 0,
            rflags: 0,
            rip: 0,
            dr0: 0,
            dr1: 0,
            dr2: 0,
            dr3: 0,
            dr0_addr_mask: 0,
            dr1_addr_mask: 0,
            dr2_addr_mask: 0,
            dr3_addr_mask: 0,
            _reserved_3: [0; 24],
            rsp: 0,
            s_cet: 0,
            ssp: 0,
            isst_addr: 0,
            rax: 0,
            star: 0,
            lstar: 0,
            cstar: 0,
            sfmask: 0,
            kernel_gs_base: 0,
            sysenter_cs: 0,
            sysenter_esp: 0,
            sysenter_eip: 0,
            cr2: 0,
            _reserved_4: [0; 32],
            g_pat: 0,
            dbgctl: 0,
            br_from: 0,
            br_to: 0,
            last_excp_from: 0,
            last_excp_to: 0,
            _reserved_5: [0; 80],
            pkru: 0,
            tsc_aux: 0,
            guest_tsc_scale: 0,
            guest_tsc_offset: 0,
            reg_prot_nonce: 0,
            rcx: 0,
            rdx: 0,
            rbx: 0,
            _reserved_6: 0,
            rbp: 0,
            rsi: 0,
            rdi: 0,
            r8: 0,
            r9: 0,
            r10: 0,
            r11: 0,
            r12: 0,
            r13: 0,
            r14: 0,
            r15: 0,
            _reserved_7: [0; 16],
            guest_exit_info_1: 0,
            guest_exit_info_2: 0,
            guest_exit_int_info: 0,
            guest_nrip: 0,
            sev_features: 0,
            vintr_ctrl: 0,
            guest_exit_code: 0,
            virtual_tom: 0,
            tlb_id: 0,
            pcpu_id: 0,
            event_inj: 0,
            xcr0: 0,
            _reserved_8: [0; 16],
            x87_dp: 0,
            mxcsr: 0,
            x87_ftw: 0,
            x87_fsw: 0,
            x87_fcw: 0,
            x87_fop: 0,
            x87_ds: 0,
            x87_cs: 0,
            x87_rip: 0,
            fpreg_x87: [0; 80],
            fpreg_xmm: [0; 256],
            fpreg_ymm: [0; 256],
            lbr_stack_state: [0; 256],
            lbr_select: 0,
            ibs_fetch_ctl: 0,
            ibs_fetch_lin_addr: 0,
            ibs_op_ctl: 0,
            ibs_op_rop: 0,
            ibs_op_data: 0,
            ibs_op_data2: 0,
            ibs_op_data3: 0,
            ibs_dc_lin_addr: 0,
            bp_ibs_tgt_rip: 0,
            ic_ibs_extd_ctl: 0,
        }
    }
}

/// When the CPU is reset, the value of RDX is set to the same value that would be returned in EAX
/// when calling CPUID for leaf 1.
///
/// See <https://en.wikipedia.org/wiki/CPUID#EAX=1:_Processor_Info_and_Feature_Bits>.
pub fn calculate_rdx_from_fms(family: u8, model: u8, stepping: u8) -> u64 {
    const STEPPING_MASK: u8 = 0xF;
    const MODEL_MASK: u8 = 0xF;
    const FAMILY_MAX: u8 = 0xF;
    const EXTENDED_MODEL_MASK: u8 = 0xF0;
    const MODEL_SHIFT: usize = 4;
    const FAMILY_SHIFT: usize = 8;
    const EXTENDED_MODEL_SHIFT: usize = 12;
    const EXTENDED_FAMILY_SHIFT: usize = 20;

    let stepping = (stepping & STEPPING_MASK) as u64;

    let model = if family == 6 || family == 15 {
        ((model & MODEL_MASK) as u64) << MODEL_SHIFT
            | (((model & EXTENDED_MODEL_MASK) as u64) << EXTENDED_MODEL_SHIFT)
    } else {
        ((model & MODEL_MASK) as u64) << MODEL_SHIFT
    };

    let family = if family > FAMILY_MAX {
        (FAMILY_MAX as u64) << FAMILY_SHIFT
            | (((family - FAMILY_MAX) as u64) << EXTENDED_FAMILY_SHIFT)
    } else {
        (family as u64) << FAMILY_SHIFT
    };

    model | stepping | family
}

/// Representation of a segment register in 64-bit mode.
///
/// See section 4.5.3 in <https://www.amd.com/system/files/TechDocs/24593.pdf>
#[repr(C)]
#[derive(Debug, Default, FromZeroes, FromBytes, AsBytes)]
pub struct SegmentRegister {
    /// The segment selector.
    pub selector: u16,
    /// The segment attributes. The meaning of the attribute bits is register-dependent.
    ///
    /// See section 4.7 in <https://www.amd.com/system/files/TechDocs/24593.pdf>.
    pub attributes: u16,
    /// The segment limit.
    pub limit: u32,
    /// The base address of the segment.
    pub base: u64,
}

static_assertions::assert_eq_size!(SegmentRegister, [u8; 16]);
