//
// Copyright 2024 The Project Oak Authors
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

use oak_ffi_error::Error;

#[unsafe(no_mangle)]
extern "C" fn anyhow_error_with_three_contexts() -> *const Error {
    Error::new_raw(
        anyhow::anyhow!("Main error message")
            .context("first context")
            .context("second context")
            .context("third context"),
    )
}
