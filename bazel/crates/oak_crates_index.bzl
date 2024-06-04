#
# Copyright 2024 The Project Oak Authors
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
#
"""
 Defines the no_std crates repository.
 After being defined, it should be loaded using:

 load("@oak_crates_index//:defs.bzl", oak_crate_repositories = "crate_repositories")

 oak_crate_repositories()
 """

load("@rules_rust//crate_universe:defs.bzl", "crate", "crates_repository")
load("//bazel:defs.bzl", "RUST_NIGHTLY_VERSION")
load("//bazel/crates:jemalloc.bzl", "jemalloc_repository")

def oak_crates_index(cargo_lockfile, lockfile):
    jemalloc_repository()

    # Default crate repository - some crates may require std.
    crates_repository(
        name = "oak_crates_index",
        annotations = {
            # Provide the jemalloc library built by the library included above.
            # The tikv-jemalloc-sys crate using by tikv-jemallocator uses a build script to run
            # configure/make for libjemalloc. This doesn't work out of the box. The suggestion is to
            # instead build libjemalloc with bazel, and then provide the generated lbirary to the
            # build script.
            #
            # See: https://github.com/bazelbuild/rules_rust/issues/1670
            # The example there didn't work exactly as written in this context, but I was able
            # to modify it to get it working.
            "tikv-jemalloc-sys": [crate.annotation(
                build_script_data = [
                    "@jemalloc//:gen_dir",
                ],
                build_script_env = {
                    "JEMALLOC_OVERRIDE": "$(execpath @jemalloc//:gen_dir)/lib/libjemalloc.a",
                },
                data = ["@jemalloc//:gen_dir"],
                version = "*",
                deps = ["@jemalloc"],
            )],
        },
        cargo_lockfile = cargo_lockfile,  # In Cargo-free mode this is used as output, not input.
        lockfile = lockfile,  # Shares most contents with cargo_lockfile.
        packages = {
            "acpi": crate.spec(version = "*"),
            "aead": crate.spec(version = "*"),
            "aes-gcm": crate.spec(
                default_features = False,
                features = [
                    "aes",
                    "alloc",
                ],
                version = "*",
            ),
            "aml": crate.spec(version = "*"),
            "anyhow": crate.spec(
                default_features = False,
                version = "*",
            ),
            "async-stream": crate.spec(
                version = "*",
            ),
            "arrayvec": crate.spec(
                default_features = False,
                version = "*",
            ),
            "assertables": crate.spec(version = "*"),
            "async-trait": crate.spec(
                default_features = False,
                version = "*",
            ),
            "atomic_refcell": crate.spec(version = "*"),
            "base64": crate.spec(
                default_features = False,
                features = ["alloc"],
                version = "0.21",
            ),
            "bitflags": crate.spec(version = "*"),
            "bitvec": crate.spec(
                default_features = False,
                version = "*",
            ),
            "bytes": crate.spec(version = "*"),
            "ciborium": crate.spec(
                default_features = False,
                version = "*",
            ),
            "clap": crate.spec(
                features = ["derive"],
                version = "*",
            ),
            "coset": crate.spec(
                default_features = False,
                version = "*",
            ),
            # Pin to 4.1.1 see issue #4952
            # TODO: #4952 - Remove this pinning.
            "curve25519-dalek": crate.spec(
                default_features = False,
                version = "=4.1.1",
            ),
            "ecdsa": crate.spec(
                default_features = False,
                features = [
                    "der",
                    "pem",
                    "pkcs8",
                    "signing",
                ],
                version = "*",
            ),
            "futures-util": crate.spec(version = "*"),
            "getrandom": crate.spec(
                version = "*",
            ),
            "goblin": crate.spec(
                default_features = False,
                features = [
                    "elf32",
                    "elf64",
                    "endian_fd",
                ],
                version = "*",
            ),
            "hex": crate.spec(
                default_features = False,
                features = ["alloc"],
                version = "*",
            ),
            "hkdf": crate.spec(
                default_features = False,
                version = "*",
            ),
            "hpke": crate.spec(
                default_features = False,
                features = [
                    "alloc",
                    "x25519",
                ],
                version = "*",
            ),
            "libm": crate.spec(version = "*"),
            "linked_list_allocator": crate.spec(
                features = [
                    "alloc_ref",
                ],
                version = "*",
            ),
            "lock_api": crate.spec(
                features = ["arc_lock"],
            ),
            "log": crate.spec(
                default_features = False,
                version = "*",
            ),
            "nix": crate.spec(
                features = ["user"],
                version = "*",
            ),
            "oci-spec": crate.spec(
                version = "*",
            ),
            "opentelemetry": crate.spec(
                version = "*",
            ),
            "opentelemetry-otlp": crate.spec(
                features = ["metrics"],
                version = "*",
            ),
            "opentelemetry_sdk": crate.spec(
                features = [
                    "metrics",
                    "rt-tokio",
                ],
                version = "*",
            ),
            "p256": crate.spec(
                default_features = False,
                features = [
                    "alloc",
                    "ecdsa-core",
                    "ecdsa",
                    "pem",
                ],
                version = "*",
            ),
            "p384": crate.spec(
                default_features = False,
                features = [
                    "ecdsa",
                    "pem",
                ],
                version = "0.13.0",
            ),
            "pkcs8": crate.spec(
                default_features = False,
                features = ["alloc"],
                version = "*",
            ),
            "primeorder": crate.spec(
                default_features = False,
                version = "*",
            ),
            "procfs": crate.spec(
                version = "*",
            ),
            "prost": crate.spec(
                default_features = False,
                features = ["prost-derive"],
                version = "*",
            ),
            "prost-derive": crate.spec(
                version = "*",
            ),
            "prost-build": crate.spec(
                version = "*",
            ),
            "prost-types": crate.spec(
                version = "*",
            ),
            "rand_core": crate.spec(
                default_features = False,
                features = ["getrandom"],
                version = "*",
            ),
            "regex": crate.spec(
                default_features = False,
                version = "*",
            ),
            "rsa": crate.spec(
                default_features = False,
                version = "0.9.6",
            ),
            "self_cell": crate.spec(version = "*"),
            "serde": crate.spec(
                default_features = False,
                features = ["derive"],
                version = "*",
            ),
            "serde_json": crate.spec(
                default_features = False,
                features = ["alloc"],
                version = "*",
            ),
            "sha2": crate.spec(
                default_features = False,
                version = "*",
            ),
            "snafu": crate.spec(
                default_features = False,
                version = "*",
            ),
            "spinning_top": crate.spec(version = "*"),
            "static_assertions": crate.spec(version = "*"),
            "strum": crate.spec(
                default_features = False,
                features = ["derive"],
                version = "*",
            ),
            "syslog": crate.spec(
                version = "*",
            ),
            "tar": crate.spec(
                version = "*",
            ),
            "tikv-jemallocator": crate.spec(version = "*"),
            "time": crate.spec(
                default_features = False,
                features = [
                    "serde",
                    "parsing",
                ],
                version = "0.3.28",
            ),
            "tokio": crate.spec(
                features = [
                    "rt-multi-thread",
                    "macros",
                    "sync",
                    "fs",
                    "process",
                    "net",
                ],
                version = "*",
            ),
            "tokio-stream": crate.spec(
                features = ["net"],
                version = "*",
            ),
            "tokio-util": crate.spec(version = "*"),
            "tonic": crate.spec(version = "*"),
            "tonic-build": crate.spec(version = "*"),
            "tower": crate.spec(version = "*"),
            "uart_16550": crate.spec(version = "*"),
            "virtio-drivers": crate.spec(version = "*"),
            "walkdir": crate.spec(version = "*"),
            "x509-cert": crate.spec(
                default_features = False,
                features = ["pem"],
                version = "0.2.5",
            ),
            "x86_64": crate.spec(version = "0.14"),
            "zerocopy": crate.spec(
                default_features = False,
                features = ["derive"],
                version = "*",
            ),
            "zeroize": crate.spec(
                features = ["derive"],
                version = "*",
            ),
        },
        rust_version = RUST_NIGHTLY_VERSION,
        # We request bare metal support. Because of feature unification, some creates
        # in this repository may end up requiring std, thus not being compatible
        # for x86_64-unknown-none. When that happens, we move the dependency to the
        # oak_no_std_crates_index repository.
        supported_platform_triples = [
            "x86_64-unknown-linux-gnu",
            "x86_64-unknown-none",
        ],
    )
