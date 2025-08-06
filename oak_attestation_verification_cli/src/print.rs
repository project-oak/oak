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

/// Prints a format string with the given arguments, with the provided indent
/// prefix. Defined as a macro to enable accepting a variable number of
/// arguments to the format string.
macro_rules! print_indented {
    ($indent:expr, $fmt:expr $(, $args:expr)*) => {
        {
            let formatted_text = format!($fmt $(, $args)*);
            println!("{}{}", "\t".repeat($indent), formatted_text);
        }
    };
}

pub(crate) use print_indented;
