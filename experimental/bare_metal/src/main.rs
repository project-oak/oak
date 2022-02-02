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

#![no_std]
#![no_main]

use bootloader::{entry_point, BootInfo};
use core::panic::PanicInfo;
use vga::{
    colors::{Color16, TextModeColor},
    writers::{ScreenCharacter, Text80x25, TextWriter},
};

entry_point!(runtime_main);

/// Initial entrypoint.
fn runtime_main(_boot_info: &'static BootInfo) -> ! {
    // Just write a string to the screen for now so that we can see something happened.
    write_to_screen("started");
    loop {}
}

/// Minimal panic handler.
#[panic_handler]
fn panic(_panic_info: &PanicInfo) -> ! {
    write_to_screen("panic!");
    loop {}
}

/// Writes a message to the screen.
///
/// This will clear the screen and the message will start at the top left.
fn write_to_screen(output: &str) {
    let vga_text = Text80x25::new();
    vga_text.clear_screen();
    for (i, byte) in output.bytes().enumerate() {
        let byte = match byte {
            // Byte is in the printable ASCII range.
            0x20..=0x7e => byte,
            // Byte is not in the printable ASCII range.
            _ => 0xfe,
        };
        let y = i / 80;
        if y >= 25 {
            return;
        }
        let x = i % 80;
        vga_text.write_character(
            x,
            y,
            ScreenCharacter::new(byte, TextModeColor::new(Color16::White, Color16::Black)),
        );
    }
}
