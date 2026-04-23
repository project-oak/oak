#
# Copyright 2025 The Project Oak Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_visibility = ["//:__subpackages__"],
    licenses = ["notice"],
)

# Custom target to update the golden snapshot without running a test in CI.
genrule(
    name = "gen_update_script",
    outs = ["update_snapshot.sh"],
    cmd = "cat << 'EOF' > $@\n" +
          "#!/bin/bash\n" +
          "set -e\n" +
          "if [ -z \"$$BUILD_WORKSPACE_DIRECTORY\" ]; then\n" +
          "  echo \"Error: This script must be run with 'bazel run'\"\n" +
          "  exit 1\n" +
          "fi\n" +
          "# Run the generator and output directly to the source tree\n" +
          "$$BUILD_WORKSPACE_DIRECTORY/bazel-bin/database/tools/generate_golden_export $$BUILD_WORKSPACE_DIRECTORY/database/testdata/golden_icing_export.pb\n" +
          "echo \"Updated database/testdata/golden_icing_export.pb\"\n" +
          "EOF\n" +
          "chmod +x $@",
)

sh_binary(
    name = "update_golden_snapshot",
    srcs = [":gen_update_script"],
    data = ["//database/tools:generate_golden_export"],
)

rust_library(
    name = "oak_private_memory_database",
    srcs = glob(["*.rs"]),
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        "//:encryption",
        "//:external_db_client",
        "//proto:sealed_memory_rust_proto",
        "//src/icing",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:bytes",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:log",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:rand",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tonic",
        "@pm_crates//:cxx",
        "@pm_crates//:rand",
        "@pm_crates//:uuid",
    ],
)

rust_test(
    name = "database_test",
    crate = ":oak_private_memory_database",
    data = ["testdata/golden_icing_export.pb"],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        "@oak_crates_index//:googletest",
        "@rules_rust//tools/runfiles",
    ],
)

alias(
    name = "database",
    actual = "oak_private_memory_database",
)
