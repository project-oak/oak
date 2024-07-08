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
 Defines the std crates repository.
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
            # Enable `tokio_unstable` so that we can access the Tokio runtime metrics.
            "tokio": [crate.annotation(
                rustc_flags = ["--cfg=tokio_unstable"],
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
            "async-recursion": crate.spec(version = "*"),
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
            "bmrng": crate.spec(version = "*"),
            "bytes": crate.spec(version = "*"),
            "chrono": crate.spec(
                default_features = False,
                features = [
                    "std",
                    "clock",
                ],
                version = "*",
            ),
            "ciborium": crate.spec(
                default_features = False,
                version = "*",
            ),
            "clap": crate.spec(
                features = [
                    "derive",
                    "env",
                ],
                version = "*",
            ),
            "clap_complete": crate.spec(version = "*"),
            "colored": crate.spec(version = "*"),
            "command-fds": crate.spec(
                features = ["tokio"],
                version = "*",
            ),
            "coset": crate.spec(
                default_features = False,
                version = "*",
            ),
            "criterion": crate.spec(version = "0.5"),
            "criterion-macro": crate.spec(version = "0.4"),
            # Pin to 4.1.1 see issue #4952
            # TODO: #4952 - Remove this pinning.
            "curve25519-dalek": crate.spec(
                default_features = False,
                version = "=4.1.1",
            ),
            "duct": crate.spec(version = "*"),
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
            "env_logger": crate.spec(version = "*"),
            "futures": crate.spec(version = "*"),
            "futures-util": crate.spec(version = "*"),
            "getrandom": crate.spec(version = "*"),
            "goblin": crate.spec(
                default_features = False,
                features = [
                    "elf32",
                    "elf64",
                    "endian_fd",
                ],
                version = "*",
            ),
            "hashbrown": crate.spec(
                default_features = False,
                version = "0.14",
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
            "hyper": crate.spec(
                features = [
                    "client",
                    "http1",
                    "runtime",
                    "server",
                ],
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
            "http": crate.spec(version = "*"),
            "ignore": crate.spec(version = "*"),
            "itertools": crate.spec(version = "*"),
            "lazy_static": crate.spec(version = "*"),
            "libloading": crate.spec(version = "*"),
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
            "maplit": crate.spec(version = "*"),
            "nix": crate.spec(
                features = [
                    "fs",
                    "mount",
                    "process",
                    "signal",
                    "term",
                    "ucontext",
                    "user",
                ],
                version = "0.27.1",
            ),
            "oci-spec": crate.spec(version = "*"),
            "once_cell": crate.spec(version = "*"),
            # TODO b/350061567 - Remove opentelemetry version pins
            "opentelemetry": crate.spec(version = "0.22.0"),
            "opentelemetry-proto": crate.spec(
                features = [
                    "gen-tonic",
                    "logs",
                    "metrics",
                ],
                version = "*",
            ),
            "opentelemetry-otlp": crate.spec(
                features = ["grpc-tonic", "logs", "metrics"],
                version = "0.15.0",
            ),
            "opentelemetry_sdk": crate.spec(
                features = [
                    "logs",
                    "metrics",
                    "rt-tokio",
                ],
                version = "0.22.1",
            ),
            "ouroboros": crate.spec(version = "*"),
            "portpicker": crate.spec(version = "*"),
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
            "parking_lot": crate.spec(version = "*"),
            "pkcs8": crate.spec(
                default_features = False,
                features = ["alloc"],
                version = "*",
            ),
            "port_check": crate.spec(version = "*"),
            "pprof": crate.spec(
                features = [
                    "frame-pointer",
                    "prost-codec",
                ],
                version = "*",
            ),
            "pretty_assertions": crate.spec(version = "*"),
            "primeorder": crate.spec(
                default_features = False,
                version = "*",
            ),
            "procfs": crate.spec(version = "*"),
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
            "quote": crate.spec(version = "*"),
            "rand": crate.spec(version = "*"),
            "rand_core": crate.spec(
                default_features = False,
                features = ["getrandom"],
                version = "*",
            ),
            "regex": crate.spec(
                default_features = False,
                version = "*",
            ),
            "regex-lite": crate.spec(
                default_features = False,
                features = [
                    "std",
                    "string",
                ],
                version = "0.1.6",
            ),
            "rlsf": crate.spec(version = "*"),
            "rsa": crate.spec(
                default_features = False,
                version = "0.9.6",
            ),
            "rtnetlink": crate.spec(version = "*"),
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
            "serde_yaml": crate.spec(version = "*"),
            "signal-hook": crate.spec(version = "*"),
            "signal-hook-tokio": crate.spec(
                features = ["futures-v0_3"],
                version = "*",
            ),
            "sha2": crate.spec(
                default_features = False,
                version = "*",
            ),
            "simple_logger": crate.spec(version = "*"),
            "snafu": crate.spec(
                default_features = False,
                version = "*",
            ),
            "spinning_top": crate.spec(version = "*"),
            "static_assertions": crate.spec(version = "*"),
            "stderrlog": crate.spec(version = "*"),
            "strum": crate.spec(
                default_features = False,
                features = ["derive"],
                version = "0.24",
            ),
            "strum_macros": crate.spec(version = "0.25"),
            "subprocess": crate.spec(version = "*"),
            "syn": crate.spec(
                features = ["full"],
                version = "*",
            ),
            "syslog": crate.spec(version = "*"),
            "tar": crate.spec(version = "*"),
            "tempfile": crate.spec(version = "*"),
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
                    "fs",
                    "io-util",
                    "macros",
                    "net",
                    "parking_lot",
                    "process",
                    "rt",
                    "rt-multi-thread",
                    "signal",
                    "sync",
                    "time",
                ],
                version = "*",
            ),
            "tokio-stream": crate.spec(
                features = ["net"],
                version = "*",
            ),
            "tokio-util": crate.spec(version = "*"),
            "tokio-vsock": crate.spec(
                # Pull the crate from github as the latest version
                # in the repository depends on tonic 10.0.2 that causes
                # compilation errors as the compiler thinks that `Connected`
                # is not implemented for `VsockStream`.
                # Other options is to patch the generated bazel file in the
                # create annotation or to write bazel for the local repository
                # in the third-party folder. Writing patches is fragile as
                # the generated build file might differ for repositories that
                # depends on Oak. In fact, the patched version in the
                # third-party folder changes the version of tonic to 11.0.0 in
                # the dependencies.
                git = "https://github.com/rust-vsock/tokio-vsock",
                rev = "2a52faeb4ede7d9712adbc096e547ab7ea766f4b",
                features = ["tonic-conn"],
            ),
            "toml": crate.spec(version = "*"),
            "tonic": crate.spec(version = "*"),
            "tonic-build": crate.spec(version = "*"),
            "tonic-web": crate.spec(version = "*"),
            "tower": crate.spec(version = "*"),
            "tower-http": crate.spec(
                features = ["trace"],
                version = "*",
            ),
            "tracing": crate.spec(version = "*"),
            "uart_16550": crate.spec(version = "*"),
            "ubyte": crate.spec(version = "*"),
            "walkdir": crate.spec(version = "*"),
            "wasmi": crate.spec(
                default_features = False,
                # same version as cargo, newer versions had compatibility issues
                version = "0.31.2",
            ),
            "wasmtime": crate.spec(version = "*"),
            "which": crate.spec(version = "*"),
            "x509-cert": crate.spec(
                default_features = False,
                features = ["pem"],
                version = "0.2.5",
            ),
            "x86_64": crate.spec(version = "0.14"),
            "xz2": crate.spec(version = "*"),
            "zerocopy": crate.spec(
                default_features = False,
                features = ["derive"],
                version = "*",
            ),
            "zeroize": crate.spec(
                features = ["derive"],
                version = "*",
            ),
            "rand_chacha": crate.spec(
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
