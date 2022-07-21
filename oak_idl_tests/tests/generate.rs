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

const OUTPUTS: [&str; 3] = [
    "test_schema_services_servers.rs",
    "test_schema_services_clients.rs",
    "test_schema_services_async_clients.rs",
];

#[test]
fn generate() {
    // This test simply copies the output created by the `build.rs` script back into the source
    // tree, so that it can be tracked in Git. We use the `.txt` extension so that other tools do
    // not attempt to format or lint it or warn about missing license header.
    //
    // This allows to see the current output of the generator, and see how changes in the generator
    // affect the output file.
    //
    // This test does not actually compare the current output to the expected one, it always
    // overwrite the current one whenever it is run. The actual comparison is performed by the
    // developer (who should notice that the generated file has changed), and also in CI (thanks to
    // the git_check_diff step).
    for output in OUTPUTS.into_iter() {
        std::fs::copy(
            format!("{}/{}", env!("OUT_DIR"), output),
            format!("{}.txt", output),
        )
        .unwrap();
    }
}
