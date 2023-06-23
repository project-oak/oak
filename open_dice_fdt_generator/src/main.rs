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

//! A utility for generating a Device Tree Blob containing the information for an Open DICE Reserved
//! Memory Linux Device.
//!
//! We want to generate a DTB that matches the Open DICE exmple, execept to the address:
//!
//! reserved-memory {
//!     #address-cells = <2>;
//!     #size-cells = <1>;
//!
//!     dice: dice@12340000 {
//!         compatible = "google,open-dice";
//!         reg = <0x00 0x12340000 0x2000>;
//!         no-map;
//!     };
//! };

use log::info;
use std::fs::write;
use vm_fdt::FdtWriter;

fn main() -> Result<(), anyhow::Error> {
    simple_logger::SimpleLogger::new().init().unwrap();
    const MEMORY_LOCATION: u32 = 0x1000;
    const MEMORY_SIZE: u32 = 0x1000;

    let mut fdt = FdtWriter::new()?;
    let root_node = fdt.begin_node("")?;
    fdt.property_u32("#address-cells", 0x2)?;
    fdt.property_u32("#size-cells", 0x2)?;
    fdt.property_string("compatible", "linux")?;

    let lapic = fdt.begin_node("interrupt-controller@fee00000")?;
    fdt.property_string("compatible", "intel,ce4100-lapic")?;
    fdt.property_array_u32("reg", &[0x0, 0xfee00000, 0x0, 0x1000])?;
    fdt.property_null("interrupt-controller")?;
    fdt.property_u32("#interrupt-cells", 0x2)?;
    fdt.property_null("intel,virtual-wire-mode")?;
    fdt.end_node(lapic)?;

    let reserved_memory = fdt.begin_node("reserved-memory")?;
    fdt.property_u32("#address-cells", 0x2)?;
    fdt.property_u32("#size-cells", 0x2)?;
    fdt.property_null("ranges")?;

    let dice = fdt.begin_node(&format!("open-dice@{:#x}", MEMORY_LOCATION))?;
    fdt.property_string("compatible", "google,open-dice")?;
    fdt.property_array_u32("reg", &[0, MEMORY_LOCATION, 0, MEMORY_SIZE])?;
    fdt.property_null("no-map")?;

    fdt.end_node(dice)?;
    fdt.end_node(reserved_memory)?;
    fdt.end_node(root_node)?;
    let result = fdt.finish()?;

    info!("DTB: {:?}", result);
    write("bin/open-dice.dtb", result)?;

    Ok(())
}
