"""
cargo-raze crate workspace functions

DO NOT EDIT! Replaced on runs of cargo-raze
"""
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")
load("@bazel_tools//tools/build_defs/repo:git.bzl", "new_git_repository")

def _new_http_archive(name, **kwargs):
    if not native.existing_rule(name):
        http_archive(name=name, **kwargs)

def _new_git_repository(name, **kwargs):
    if not native.existing_rule(name):
        new_git_repository(name=name, **kwargs)

def raze_fetch_remote_crates():

    _new_http_archive(
        name = "raze__anyhow__1_0_28",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/anyhow/anyhow-1.0.28.crate",
        type = "tar.gz",
        strip_prefix = "anyhow-1.0.28",

        build_file = Label("//cargo/remote:anyhow-1.0.28.BUILD"),
    )

    _new_http_archive(
        name = "raze__atty__0_2_14",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/atty/atty-0.2.14.crate",
        type = "tar.gz",
        strip_prefix = "atty-0.2.14",

        build_file = Label("//cargo/remote:atty-0.2.14.BUILD"),
    )

    _new_http_archive(
        name = "raze__autocfg__1_0_0",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/autocfg/autocfg-1.0.0.crate",
        type = "tar.gz",
        strip_prefix = "autocfg-1.0.0",

        build_file = Label("//cargo/remote:autocfg-1.0.0.BUILD"),
    )

    _new_http_archive(
        name = "raze__bitflags__1_2_1",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/bitflags/bitflags-1.2.1.crate",
        type = "tar.gz",
        strip_prefix = "bitflags-1.2.1",

        build_file = Label("//cargo/remote:bitflags-1.2.1.BUILD"),
    )

    _new_http_archive(
        name = "raze__byteorder__1_3_4",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/byteorder/byteorder-1.3.4.crate",
        type = "tar.gz",
        strip_prefix = "byteorder-1.3.4",

        build_file = Label("//cargo/remote:byteorder-1.3.4.BUILD"),
    )

    _new_http_archive(
        name = "raze__bytes__0_5_4",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/bytes/bytes-0.5.4.crate",
        type = "tar.gz",
        strip_prefix = "bytes-0.5.4",

        build_file = Label("//cargo/remote:bytes-0.5.4.BUILD"),
    )

    _new_http_archive(
        name = "raze__cfg_if__0_1_10",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/cfg-if/cfg-if-0.1.10.crate",
        type = "tar.gz",
        strip_prefix = "cfg-if-0.1.10",

        build_file = Label("//cargo/remote:cfg-if-0.1.10.BUILD"),
    )

    _new_http_archive(
        name = "raze__chrono__0_4_11",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/chrono/chrono-0.4.11.crate",
        type = "tar.gz",
        strip_prefix = "chrono-0.4.11",

        build_file = Label("//cargo/remote:chrono-0.4.11.BUILD"),
    )

    _new_http_archive(
        name = "raze__colored__1_9_3",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/colored/colored-1.9.3.crate",
        type = "tar.gz",
        strip_prefix = "colored-1.9.3",

        build_file = Label("//cargo/remote:colored-1.9.3.BUILD"),
    )

    _new_http_archive(
        name = "raze__either__1_5_3",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/either/either-1.5.3.crate",
        type = "tar.gz",
        strip_prefix = "either-1.5.3",

        build_file = Label("//cargo/remote:either-1.5.3.BUILD"),
    )

    _new_http_archive(
        name = "raze__fnv__1_0_6",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/fnv/fnv-1.0.6.crate",
        type = "tar.gz",
        strip_prefix = "fnv-1.0.6",

        build_file = Label("//cargo/remote:fnv-1.0.6.BUILD"),
    )

    _new_http_archive(
        name = "raze__fuchsia_zircon__0_3_3",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/fuchsia-zircon/fuchsia-zircon-0.3.3.crate",
        type = "tar.gz",
        strip_prefix = "fuchsia-zircon-0.3.3",

        build_file = Label("//cargo/remote:fuchsia-zircon-0.3.3.BUILD"),
    )

    _new_http_archive(
        name = "raze__fuchsia_zircon_sys__0_3_3",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/fuchsia-zircon-sys/fuchsia-zircon-sys-0.3.3.crate",
        type = "tar.gz",
        strip_prefix = "fuchsia-zircon-sys-0.3.3",

        build_file = Label("//cargo/remote:fuchsia-zircon-sys-0.3.3.BUILD"),
    )

    _new_http_archive(
        name = "raze__futures_channel__0_3_4",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/futures-channel/futures-channel-0.3.4.crate",
        type = "tar.gz",
        strip_prefix = "futures-channel-0.3.4",

        build_file = Label("//cargo/remote:futures-channel-0.3.4.BUILD"),
    )

    _new_http_archive(
        name = "raze__futures_core__0_3_4",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/futures-core/futures-core-0.3.4.crate",
        type = "tar.gz",
        strip_prefix = "futures-core-0.3.4",

        build_file = Label("//cargo/remote:futures-core-0.3.4.BUILD"),
    )

    _new_http_archive(
        name = "raze__futures_sink__0_3_4",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/futures-sink/futures-sink-0.3.4.crate",
        type = "tar.gz",
        strip_prefix = "futures-sink-0.3.4",

        build_file = Label("//cargo/remote:futures-sink-0.3.4.BUILD"),
    )

    _new_http_archive(
        name = "raze__futures_task__0_3_4",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/futures-task/futures-task-0.3.4.crate",
        type = "tar.gz",
        strip_prefix = "futures-task-0.3.4",

        build_file = Label("//cargo/remote:futures-task-0.3.4.BUILD"),
    )

    _new_http_archive(
        name = "raze__futures_util__0_3_4",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/futures-util/futures-util-0.3.4.crate",
        type = "tar.gz",
        strip_prefix = "futures-util-0.3.4",

        build_file = Label("//cargo/remote:futures-util-0.3.4.BUILD"),
    )

    _new_http_archive(
        name = "raze__getrandom__0_1_14",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/getrandom/getrandom-0.1.14.crate",
        type = "tar.gz",
        strip_prefix = "getrandom-0.1.14",

        build_file = Label("//cargo/remote:getrandom-0.1.14.BUILD"),
    )

    _new_http_archive(
        name = "raze__h2__0_2_4",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/h2/h2-0.2.4.crate",
        type = "tar.gz",
        strip_prefix = "h2-0.2.4",

        build_file = Label("//cargo/remote:h2-0.2.4.BUILD"),
    )

    _new_http_archive(
        name = "raze__hermit_abi__0_1_11",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/hermit-abi/hermit-abi-0.1.11.crate",
        type = "tar.gz",
        strip_prefix = "hermit-abi-0.1.11",

        build_file = Label("//cargo/remote:hermit-abi-0.1.11.BUILD"),
    )

    _new_http_archive(
        name = "raze__http__0_2_1",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/http/http-0.2.1.crate",
        type = "tar.gz",
        strip_prefix = "http-0.2.1",

        build_file = Label("//cargo/remote:http-0.2.1.BUILD"),
    )

    _new_http_archive(
        name = "raze__http_body__0_3_1",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/http-body/http-body-0.3.1.crate",
        type = "tar.gz",
        strip_prefix = "http-body-0.3.1",

        build_file = Label("//cargo/remote:http-body-0.3.1.BUILD"),
    )

    _new_http_archive(
        name = "raze__httparse__1_3_4",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/httparse/httparse-1.3.4.crate",
        type = "tar.gz",
        strip_prefix = "httparse-1.3.4",

        build_file = Label("//cargo/remote:httparse-1.3.4.BUILD"),
    )

    _new_http_archive(
        name = "raze__hyper__0_13_5",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/hyper/hyper-0.13.5.crate",
        type = "tar.gz",
        strip_prefix = "hyper-0.13.5",

        build_file = Label("//cargo/remote:hyper-0.13.5.BUILD"),
    )

    _new_http_archive(
        name = "raze__indexmap__1_0_2",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/indexmap/indexmap-1.0.2.crate",
        type = "tar.gz",
        strip_prefix = "indexmap-1.0.2",

        build_file = Label("//cargo/remote:indexmap-1.0.2.BUILD"),
    )

    _new_http_archive(
        name = "raze__iovec__0_1_4",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/iovec/iovec-0.1.4.crate",
        type = "tar.gz",
        strip_prefix = "iovec-0.1.4",

        build_file = Label("//cargo/remote:iovec-0.1.4.BUILD"),
    )

    _new_http_archive(
        name = "raze__itertools__0_8_2",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/itertools/itertools-0.8.2.crate",
        type = "tar.gz",
        strip_prefix = "itertools-0.8.2",

        build_file = Label("//cargo/remote:itertools-0.8.2.BUILD"),
    )

    _new_http_archive(
        name = "raze__itertools__0_9_0",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/itertools/itertools-0.9.0.crate",
        type = "tar.gz",
        strip_prefix = "itertools-0.9.0",

        build_file = Label("//cargo/remote:itertools-0.9.0.BUILD"),
    )

    _new_http_archive(
        name = "raze__itoa__0_4_5",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/itoa/itoa-0.4.5.crate",
        type = "tar.gz",
        strip_prefix = "itoa-0.4.5",

        build_file = Label("//cargo/remote:itoa-0.4.5.BUILD"),
    )

    _new_http_archive(
        name = "raze__kernel32_sys__0_2_2",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/kernel32-sys/kernel32-sys-0.2.2.crate",
        type = "tar.gz",
        strip_prefix = "kernel32-sys-0.2.2",

        build_file = Label("//cargo/remote:kernel32-sys-0.2.2.BUILD"),
    )

    _new_http_archive(
        name = "raze__lazy_static__1_4_0",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/lazy_static/lazy_static-1.4.0.crate",
        type = "tar.gz",
        strip_prefix = "lazy_static-1.4.0",

        build_file = Label("//cargo/remote:lazy_static-1.4.0.BUILD"),
    )

    _new_http_archive(
        name = "raze__libc__0_2_69",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/libc/libc-0.2.69.crate",
        type = "tar.gz",
        strip_prefix = "libc-0.2.69",

        build_file = Label("//cargo/remote:libc-0.2.69.BUILD"),
    )

    _new_http_archive(
        name = "raze__libm__0_1_4",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/libm/libm-0.1.4.crate",
        type = "tar.gz",
        strip_prefix = "libm-0.1.4",

        build_file = Label("//cargo/remote:libm-0.1.4.BUILD"),
    )

    _new_http_archive(
        name = "raze__log__0_4_8",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/log/log-0.4.8.crate",
        type = "tar.gz",
        strip_prefix = "log-0.4.8",

        build_file = Label("//cargo/remote:log-0.4.8.BUILD"),
    )

    _new_http_archive(
        name = "raze__memchr__2_3_3",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/memchr/memchr-2.3.3.crate",
        type = "tar.gz",
        strip_prefix = "memchr-2.3.3",

        build_file = Label("//cargo/remote:memchr-2.3.3.BUILD"),
    )

    _new_http_archive(
        name = "raze__memory_units__0_3_0",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/memory_units/memory_units-0.3.0.crate",
        type = "tar.gz",
        strip_prefix = "memory_units-0.3.0",

        build_file = Label("//cargo/remote:memory_units-0.3.0.BUILD"),
    )

    _new_http_archive(
        name = "raze__mio__0_6_21",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/mio/mio-0.6.21.crate",
        type = "tar.gz",
        strip_prefix = "mio-0.6.21",

        build_file = Label("//cargo/remote:mio-0.6.21.BUILD"),
    )

    _new_http_archive(
        name = "raze__miow__0_2_1",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/miow/miow-0.2.1.crate",
        type = "tar.gz",
        strip_prefix = "miow-0.2.1",

        build_file = Label("//cargo/remote:miow-0.2.1.BUILD"),
    )

    _new_http_archive(
        name = "raze__net2__0_2_33",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/net2/net2-0.2.33.crate",
        type = "tar.gz",
        strip_prefix = "net2-0.2.33",

        build_file = Label("//cargo/remote:net2-0.2.33.BUILD"),
    )

    _new_http_archive(
        name = "raze__num_bigint__0_2_6",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/num-bigint/num-bigint-0.2.6.crate",
        type = "tar.gz",
        strip_prefix = "num-bigint-0.2.6",

        build_file = Label("//cargo/remote:num-bigint-0.2.6.BUILD"),
    )

    _new_http_archive(
        name = "raze__num_integer__0_1_42",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/num-integer/num-integer-0.1.42.crate",
        type = "tar.gz",
        strip_prefix = "num-integer-0.1.42",

        build_file = Label("//cargo/remote:num-integer-0.1.42.BUILD"),
    )

    _new_http_archive(
        name = "raze__num_rational__0_2_4",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/num-rational/num-rational-0.2.4.crate",
        type = "tar.gz",
        strip_prefix = "num-rational-0.2.4",

        build_file = Label("//cargo/remote:num-rational-0.2.4.BUILD"),
    )

    _new_http_archive(
        name = "raze__num_traits__0_2_11",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/num-traits/num-traits-0.2.11.crate",
        type = "tar.gz",
        strip_prefix = "num-traits-0.2.11",

        build_file = Label("//cargo/remote:num-traits-0.2.11.BUILD"),
    )

    _new_http_archive(
        name = "raze__parity_wasm__0_41_0",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/parity-wasm/parity-wasm-0.41.0.crate",
        type = "tar.gz",
        strip_prefix = "parity-wasm-0.41.0",

        build_file = Label("//cargo/remote:parity-wasm-0.41.0.BUILD"),
    )

    _new_http_archive(
        name = "raze__pin_project__0_4_9",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/pin-project/pin-project-0.4.9.crate",
        type = "tar.gz",
        strip_prefix = "pin-project-0.4.9",

        build_file = Label("//cargo/remote:pin-project-0.4.9.BUILD"),
    )

    _new_http_archive(
        name = "raze__pin_project_internal__0_4_9",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/pin-project-internal/pin-project-internal-0.4.9.crate",
        type = "tar.gz",
        strip_prefix = "pin-project-internal-0.4.9",

        build_file = Label("//cargo/remote:pin-project-internal-0.4.9.BUILD"),
    )

    _new_http_archive(
        name = "raze__pin_project_lite__0_1_4",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/pin-project-lite/pin-project-lite-0.1.4.crate",
        type = "tar.gz",
        strip_prefix = "pin-project-lite-0.1.4",

        build_file = Label("//cargo/remote:pin-project-lite-0.1.4.BUILD"),
    )

    _new_http_archive(
        name = "raze__pin_utils__0_1_0_alpha_4",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/pin-utils/pin-utils-0.1.0-alpha.4.crate",
        type = "tar.gz",
        strip_prefix = "pin-utils-0.1.0-alpha.4",

        build_file = Label("//cargo/remote:pin-utils-0.1.0-alpha.4.BUILD"),
    )

    _new_http_archive(
        name = "raze__ppv_lite86__0_2_6",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/ppv-lite86/ppv-lite86-0.2.6.crate",
        type = "tar.gz",
        strip_prefix = "ppv-lite86-0.2.6",

        build_file = Label("//cargo/remote:ppv-lite86-0.2.6.BUILD"),
    )

    _new_http_archive(
        name = "raze__proc_macro2__1_0_10",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/proc-macro2/proc-macro2-1.0.10.crate",
        type = "tar.gz",
        strip_prefix = "proc-macro2-1.0.10",

        build_file = Label("//cargo/remote:proc-macro2-1.0.10.BUILD"),
    )

    _new_http_archive(
        name = "raze__prometheus__0_8_0",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/prometheus/prometheus-0.8.0.crate",
        type = "tar.gz",
        strip_prefix = "prometheus-0.8.0",

        build_file = Label("//cargo/remote:prometheus-0.8.0.BUILD"),
    )

    _new_http_archive(
        name = "raze__prost__0_6_1",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/prost/prost-0.6.1.crate",
        type = "tar.gz",
        strip_prefix = "prost-0.6.1",

        build_file = Label("//cargo/remote:prost-0.6.1.BUILD"),
    )

    _new_http_archive(
        name = "raze__prost_derive__0_6_1",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/prost-derive/prost-derive-0.6.1.crate",
        type = "tar.gz",
        strip_prefix = "prost-derive-0.6.1",

        build_file = Label("//cargo/remote:prost-derive-0.6.1.BUILD"),
    )

    _new_http_archive(
        name = "raze__prost_types__0_6_1",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/prost-types/prost-types-0.6.1.crate",
        type = "tar.gz",
        strip_prefix = "prost-types-0.6.1",

        build_file = Label("//cargo/remote:prost-types-0.6.1.BUILD"),
    )

    _new_http_archive(
        name = "raze__quote__1_0_3",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/quote/quote-1.0.3.crate",
        type = "tar.gz",
        strip_prefix = "quote-1.0.3",

        build_file = Label("//cargo/remote:quote-1.0.3.BUILD"),
    )

    _new_http_archive(
        name = "raze__rand__0_7_3",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/rand/rand-0.7.3.crate",
        type = "tar.gz",
        strip_prefix = "rand-0.7.3",

        build_file = Label("//cargo/remote:rand-0.7.3.BUILD"),
    )

    _new_http_archive(
        name = "raze__rand_chacha__0_2_2",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/rand_chacha/rand_chacha-0.2.2.crate",
        type = "tar.gz",
        strip_prefix = "rand_chacha-0.2.2",

        build_file = Label("//cargo/remote:rand_chacha-0.2.2.BUILD"),
    )

    _new_http_archive(
        name = "raze__rand_core__0_5_1",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/rand_core/rand_core-0.5.1.crate",
        type = "tar.gz",
        strip_prefix = "rand_core-0.5.1",

        build_file = Label("//cargo/remote:rand_core-0.5.1.BUILD"),
    )

    _new_http_archive(
        name = "raze__rand_hc__0_2_0",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/rand_hc/rand_hc-0.2.0.crate",
        type = "tar.gz",
        strip_prefix = "rand_hc-0.2.0",

        build_file = Label("//cargo/remote:rand_hc-0.2.0.BUILD"),
    )

    _new_http_archive(
        name = "raze__redox_syscall__0_1_56",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/redox_syscall/redox_syscall-0.1.56.crate",
        type = "tar.gz",
        strip_prefix = "redox_syscall-0.1.56",

        build_file = Label("//cargo/remote:redox_syscall-0.1.56.BUILD"),
    )

    _new_http_archive(
        name = "raze__simple_logger__1_6_0",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/simple_logger/simple_logger-1.6.0.crate",
        type = "tar.gz",
        strip_prefix = "simple_logger-1.6.0",

        build_file = Label("//cargo/remote:simple_logger-1.6.0.BUILD"),
    )

    _new_http_archive(
        name = "raze__slab__0_4_2",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/slab/slab-0.4.2.crate",
        type = "tar.gz",
        strip_prefix = "slab-0.4.2",

        build_file = Label("//cargo/remote:slab-0.4.2.BUILD"),
    )

    _new_http_archive(
        name = "raze__spin__0_5_2",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/spin/spin-0.5.2.crate",
        type = "tar.gz",
        strip_prefix = "spin-0.5.2",

        build_file = Label("//cargo/remote:spin-0.5.2.BUILD"),
    )

    _new_http_archive(
        name = "raze__syn__1_0_17",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/syn/syn-1.0.17.crate",
        type = "tar.gz",
        strip_prefix = "syn-1.0.17",

        build_file = Label("//cargo/remote:syn-1.0.17.BUILD"),
    )

    _new_http_archive(
        name = "raze__thiserror__1_0_15",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/thiserror/thiserror-1.0.15.crate",
        type = "tar.gz",
        strip_prefix = "thiserror-1.0.15",

        build_file = Label("//cargo/remote:thiserror-1.0.15.BUILD"),
    )

    _new_http_archive(
        name = "raze__thiserror_impl__1_0_15",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/thiserror-impl/thiserror-impl-1.0.15.crate",
        type = "tar.gz",
        strip_prefix = "thiserror-impl-1.0.15",

        build_file = Label("//cargo/remote:thiserror-impl-1.0.15.BUILD"),
    )

    _new_http_archive(
        name = "raze__time__0_1_42",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/time/time-0.1.42.crate",
        type = "tar.gz",
        strip_prefix = "time-0.1.42",

        build_file = Label("//cargo/remote:time-0.1.42.BUILD"),
    )

    _new_http_archive(
        name = "raze__tokio__0_2_18",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/tokio/tokio-0.2.18.crate",
        type = "tar.gz",
        strip_prefix = "tokio-0.2.18",

        build_file = Label("//cargo/remote:tokio-0.2.18.BUILD"),
    )

    _new_http_archive(
        name = "raze__tokio_util__0_3_1",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/tokio-util/tokio-util-0.3.1.crate",
        type = "tar.gz",
        strip_prefix = "tokio-util-0.3.1",

        build_file = Label("//cargo/remote:tokio-util-0.3.1.BUILD"),
    )

    _new_http_archive(
        name = "raze__tower_service__0_3_0",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/tower-service/tower-service-0.3.0.crate",
        type = "tar.gz",
        strip_prefix = "tower-service-0.3.0",

        build_file = Label("//cargo/remote:tower-service-0.3.0.BUILD"),
    )

    _new_http_archive(
        name = "raze__try_lock__0_2_2",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/try-lock/try-lock-0.2.2.crate",
        type = "tar.gz",
        strip_prefix = "try-lock-0.2.2",

        build_file = Label("//cargo/remote:try-lock-0.2.2.BUILD"),
    )

    _new_http_archive(
        name = "raze__unicode_xid__0_2_0",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/unicode-xid/unicode-xid-0.2.0.crate",
        type = "tar.gz",
        strip_prefix = "unicode-xid-0.2.0",

        build_file = Label("//cargo/remote:unicode-xid-0.2.0.BUILD"),
    )

    _new_http_archive(
        name = "raze__want__0_3_0",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/want/want-0.3.0.crate",
        type = "tar.gz",
        strip_prefix = "want-0.3.0",

        build_file = Label("//cargo/remote:want-0.3.0.BUILD"),
    )

    _new_http_archive(
        name = "raze__wasi__0_9_0_wasi_snapshot_preview1",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/wasi/wasi-0.9.0+wasi-snapshot-preview1.crate",
        type = "tar.gz",
        strip_prefix = "wasi-0.9.0+wasi-snapshot-preview1",

        build_file = Label("//cargo/remote:wasi-0.9.0+wasi-snapshot-preview1.BUILD"),
    )

    _new_http_archive(
        name = "raze__wasmi__0_6_2",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/wasmi/wasmi-0.6.2.crate",
        type = "tar.gz",
        strip_prefix = "wasmi-0.6.2",

        build_file = Label("//cargo/remote:wasmi-0.6.2.BUILD"),
    )

    _new_http_archive(
        name = "raze__wasmi_validation__0_3_0",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/wasmi-validation/wasmi-validation-0.3.0.crate",
        type = "tar.gz",
        strip_prefix = "wasmi-validation-0.3.0",

        build_file = Label("//cargo/remote:wasmi-validation-0.3.0.BUILD"),
    )

    _new_http_archive(
        name = "raze__winapi__0_2_8",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/winapi/winapi-0.2.8.crate",
        type = "tar.gz",
        strip_prefix = "winapi-0.2.8",

        build_file = Label("//cargo/remote:winapi-0.2.8.BUILD"),
    )

    _new_http_archive(
        name = "raze__winapi__0_3_8",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/winapi/winapi-0.3.8.crate",
        type = "tar.gz",
        strip_prefix = "winapi-0.3.8",

        build_file = Label("//cargo/remote:winapi-0.3.8.BUILD"),
    )

    _new_http_archive(
        name = "raze__winapi_build__0_1_1",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/winapi-build/winapi-build-0.1.1.crate",
        type = "tar.gz",
        strip_prefix = "winapi-build-0.1.1",

        build_file = Label("//cargo/remote:winapi-build-0.1.1.BUILD"),
    )

    _new_http_archive(
        name = "raze__winapi_i686_pc_windows_gnu__0_4_0",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/winapi-i686-pc-windows-gnu/winapi-i686-pc-windows-gnu-0.4.0.crate",
        type = "tar.gz",
        strip_prefix = "winapi-i686-pc-windows-gnu-0.4.0",

        build_file = Label("//cargo/remote:winapi-i686-pc-windows-gnu-0.4.0.BUILD"),
    )

    _new_http_archive(
        name = "raze__winapi_x86_64_pc_windows_gnu__0_4_0",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/winapi-x86_64-pc-windows-gnu/winapi-x86_64-pc-windows-gnu-0.4.0.crate",
        type = "tar.gz",
        strip_prefix = "winapi-x86_64-pc-windows-gnu-0.4.0",

        build_file = Label("//cargo/remote:winapi-x86_64-pc-windows-gnu-0.4.0.BUILD"),
    )

    _new_http_archive(
        name = "raze__ws2_32_sys__0_2_1",
        url = "https://crates-io.s3-us-west-1.amazonaws.com/crates/ws2_32-sys/ws2_32-sys-0.2.1.crate",
        type = "tar.gz",
        strip_prefix = "ws2_32-sys-0.2.1",

        build_file = Label("//cargo/remote:ws2_32-sys-0.2.1.BUILD"),
    )

