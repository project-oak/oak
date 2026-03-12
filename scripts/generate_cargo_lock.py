#!/usr/bin/env python3
#
# Copyright 2026 The Project Oak Authors
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
# This script generates a minimal Cargo.lock file by parsing MODULE.bazel.lock.
# The resulting Cargo.lock is intended ONLY for use with `cargo-audit` to
# check for vulnerabilities in Rust dependencies managed by Bazel.
#

import json
import re
import sys
import os

def main():
    """Generates a temporary Cargo.lock file by parsing MODULE.bazel.lock.

    This script extracts Rust crate names and versions from Bazel's module
    extension data (specifically from crate_universe generated specs). It
    produces a minimal Cargo.lock format suitable for use with `cargo-audit`.

    The script recurses through the JSON structure of MODULE.bazel.lock to find
    repository specifications that contain 'build_file_content'. This field
    reliably contains the original crate name and version as defined by
    crate_universe, which is more accurate than parsing Bazel's sanitized
    repository names.
    """
    lockfile_path = "MODULE.bazel.lock"
    if not os.path.exists(lockfile_path):
        print(f"Error: {lockfile_path} not found.", file=sys.stderr)
        sys.exit(1)

    with open(lockfile_path, "r") as f:
        data = json.load(f)

    packages = set()

    # Regex to extract crate name and version from build_file_content
    # e.g., 'tags = ["cargo-bazel", "crate-name=virtio-drivers", ...]'
    # and 'version = "0.12.0"'
    crate_name_pattern = re.compile(r'crate-name=([a-zA-Z0-9._-]+)')
    version_pattern = re.compile(r'version = "([^"]+)"')

    def find_crates(obj):
        """Recursively searches the JSON object for crate repository specifications.

        Args:
            obj: A dictionary or list from the parsed MODULE.bazel.lock JSON.
        """
        if isinstance(obj, dict):
            # Check if this is a repository specification
            # crate_universe stores the original crate metadata in the generated BUILD file content.
            build_file_content = obj.get("attributes", {}).get("build_file_content")
            if build_file_content:
                name_match = crate_name_pattern.search(build_file_content)
                version_match = version_pattern.search(build_file_content)
                if name_match and version_match:
                    packages.add((name_match.group(1), version_match.group(1)))

            for v in obj.values():
                find_crates(v)
        elif isinstance(obj, list):
            for item in obj:
                find_crates(item)

    find_crates(data)

    if not packages:
        print("No Rust packages found in MODULE.bazel.lock", file=sys.stderr)
        sys.exit(0)

    # Sort packages by name
    sorted_packages = sorted(list(packages))

    sys.stdout.write('version = 3\n\n')
    for name, version in sorted_packages:
        sys.stdout.write("[[package]]\n")
        sys.stdout.write(f'name = "{name}"\n')
        sys.stdout.write(f'version = "{version}"\n')
        sys.stdout.write('source = "registry+https://github.com/rust-lang/crates.io-index"\n')
        sys.stdout.write("\n")

    print(f"Successfully generated Cargo.lock with {len(sorted_packages)} packages.", file=sys.stderr)

if __name__ == "__main__":
    main()
