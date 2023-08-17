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

use crate::acpi_tables::{Madt, ProcessorLocalApic, ProcessorLocalX2Apic, Rsdp};

// TODO(#4235): Bootstrap the APs.
pub fn bootstrap_aps(rsdp: &Rsdp) -> Result<(), &'static str> {
    // If XSDT exists, then per ACPI spec we have to prefer that. If it doesn't, see if we can use
    // the old RSDT. (If we have neither XSDT or RSDT, the ACPI tables are broken.)
    let madt = if let Ok(Some(xsdt)) = rsdp.xsdt() {
        xsdt.get(Madt::SIGNATURE)
            .ok_or("MADT table not found in XSDT")?
    } else {
        let rsdt = rsdp.rsdt()?.ok_or("RSDT not found")?;
        rsdt.get(Madt::SIGNATURE)
            .ok_or("MADT table not found in RSDT")?
    };
    let madt = Madt::new(madt).expect("invalid MADT");

    log::debug!("Found ACPI MADT table: {:?}", madt);
    for item in madt.iter() {
        match item.structure_type {
            ProcessorLocalApic::STRUCTURE_TYPE => {
                log::debug!("Local APIC: {:?}", ProcessorLocalApic::new(item).unwrap());
            }
            ProcessorLocalX2Apic::STRUCTURE_TYPE => {
                log::debug!(
                    "Local X2 APIC: {:?}",
                    ProcessorLocalX2Apic::new(item).unwrap()
                );
            }
            // We don't care about other interrupt controller structure types.
            _ => {
                log::debug!("uninteresting structure: {}", item.structure_type);
            }
        }
    }

    Ok(())
}
