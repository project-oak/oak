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

// The GUID tables are as follows:
// https://github.com/tianocore/edk2/blob/master/OvmfPkg/AmdSev/BlobVerifierLibSevHashes/BlobVerifierSevHashes.c
//  9438d606-4f22-4cc9-b479-a793d411fd21  sev hashes table GUID
//  4de79437-abd2-427f-b835-d5b172d2045b  kernel
//  44baf731-3a2f-4bd7-9af1-41e29169781d  initrd
//  97d02dd8-bd20-4c94-aa78-e7714d36ab2a  cmdline

// These struct definitions are pulled from
// https://docs.rs/lit-sev-snp-utils/latest/src/lit_sev_snp_utils/guest/measure/sev_hashes.rs.html#65-71
// The structures are loosely taken from the measurement tool and from QEMU itself.

use hex;
use sha2::Sha256;
use sha2::Digest;

#[repr(transparent)]
#[derive(Debug, Clone, Copy)]
pub struct GuidLe([u8; 16]);

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct SevHashTableEntry {
    pub guid: GuidLe,
    length: u16,
    pub hash: [u8; u32::BITS as usize],
}

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct SevHashTable {
    guid: GuidLe,
    length: u16,
    pub cmdline: SevHashTableEntry,
    pub initrd: SevHashTableEntry,
    pub kernel: SevHashTableEntry,
}

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct PaddedSevHashTable {
    pub ht: SevHashTable,
    padding: [u8; ((core::mem::size_of::<SevHashTable>() + 15) & !15) -
        core::mem::size_of::<SevHashTable>()],
}

pub fn validate_hash_table(ht: &PaddedSevHashTable, cmdline: &[u8], initrd_digest: &[u8], kernel_setup_data: &[u8], kernel_bytes: &[u8]) -> bool {
    let expected_kernel_digest = hex::encode(ht.ht.kernel.hash);
    let mut kernel_hasher = Sha256::new();

    // QEMU embeds the kernel as a single blob
    kernel_hasher.update(kernel_setup_data);
    kernel_hasher.update(kernel_bytes);
    let kernel_digest = hex::encode(kernel_hasher.finalize());
    if expected_kernel_digest != kernel_digest {
        log::debug!("Kernel check failed, expected: {}, got {}", expected_kernel_digest, kernel_digest);
        return false;
    }

    let expected_initrd_digest = hex::encode(ht.ht.initrd.hash);
    let initrd_digest = hex::encode(initrd_digest);
    if expected_initrd_digest != initrd_digest {
         log::debug!("initrd check failed, expected: {}, got {}", expected_initrd_digest, initrd_digest);
         return false;
    }

    let expected_kernel_cmdline_digest = hex::encode(ht.ht.cmdline.hash);
    let mut cmdline_hasher = Sha256::new();
    let nul = &[0x0];
    // Current VirTEE measurement tooling adds a NUL terminator against cmdline hashes
    // https://github.com/virtee/sev-snp-measure/blob/3b3fc88e29f93aeb362ec37f321c76f92522a475/sevsnpmeasure/sev_hashes.py#L71-L75
    cmdline_hasher.update([cmdline, nul].concat());
    let cmdline_digest = hex::encode(cmdline_hasher.finalize());
    if expected_kernel_cmdline_digest != cmdline_digest {
        log::debug!("kernel cmdline check failed, expected: {}, got {}", expected_kernel_cmdline_digest, cmdline_digest);
        return false;
    }
    true
}
