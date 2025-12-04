// Copyright 2025 Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::vec::Vec;

use proptest::prelude::*;

proptest! {
    #[test]
    fn test_unattested_nn_encryption_and_decryption(message: Vec<u8>) {
        oak_session_testing::test_unattested_nn_encryption_and_decryption_inner(message).expect("Testing test_unattested_nn_encryption_and_decryption_inner")
    }
}
