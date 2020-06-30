#
# Copyright 2018 The Project Oak Authors
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

workspace(name = "oak")

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")
load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")

http_archive(
    name = "bazel_skylib",
    sha256 = "f1c8360c01fcf276778d3519394805dc2a71a64274a3a0908bc9edff7b5aebc8",
    url = "https://github.com/bazelbuild/bazel-skylib/releases/download/1.0.1/bazel-skylib-1.0.1.tar.gz",
)

http_archive(
    name = "rules_cc",
    sha256 = "ff1710c6f2a880784abe6aa9a6fcb6c4cbfc2cf3e5d81ef5d92dddc8ef537864",
    strip_prefix = "rules_cc-0489ba308b2e1fe458dea5a3e6efebd25087a339",
    urls = [
        # Head commit on 2020-01-14.
        "https://github.com/bazelbuild/rules_cc/archive/0489ba308b2e1fe458dea5a3e6efebd25087a339.tar.gz",
    ],
)

http_archive(
    name = "com_google_absl",
    sha256 = "eb44e45b9b53b506658861f734ca743346ec792732b063a5b43c96751ccd90c7",
    strip_prefix = "abseil-cpp-7853a7586c492ce8905c9e49f8679dada6354f2c",
    urls = [
        # Head commit on 2020-03-16.
        "https://github.com/abseil/abseil-cpp/archive/7853a7586c492ce8905c9e49f8679dada6354f2c.zip",
    ],
)

# Java rules
http_archive(
    name = "rules_java",
    sha256 = "7f4772b0ee2b46a042870c844e9c208e8a0960a953a079236a4bbd785e471275",
    strip_prefix = "rules_java-9eb38ebffbaf4414fa3d2292b28e604a256dd5a5",
    urls = [
        # Head commit on 2020-02-18.
        "https://github.com/bazelbuild/rules_java/archive/9eb38ebffbaf4414fa3d2292b28e604a256dd5a5.zip",
    ],
)

# BoringSSL
http_archive(
    name = "boringssl",
    sha256 = "37fabee8aa25d4a7f4eb05071b2c1929991c272cc2cb1cb33305163faea3c668",
    strip_prefix = "boringssl-6a47fc1adc71998756d275050351346e4fb4e2d5",
    # Commit from 2019-12-13
    urls = [
        "https://github.com/google/boringssl/archive/6a47fc1adc71998756d275050351346e4fb4e2d5.tar.gz",
    ],
)

# Patch gRPC ares BUILD file.
# TODO: Remove when gRPC will fix Ares Android build
# https://github.com/grpc/grpc/pull/21463
http_archive(
    name = "com_github_grpc_grpc",
    patches = [
        # This patch adds `ares_android.h` dependency in the Ares BUILD file.
        # https://github.com/grpc/grpc/issues/21437
        "//third_party/google/rpc:Add-ares-android.patch",
    ],
    sha256 = "c2ab8a42a0d673c1acb596d276055adcc074c1116e427f118415da3e79e52969",
    strip_prefix = "grpc-1.27.3",
    urls = ["https://github.com/grpc/grpc/archive/v1.27.3.tar.gz"],
)

# Google Test
git_repository(
    name = "gtest",
    commit = "2fe3bd994b3189899d93f1d5a881e725e046fdc2",
    remote = "https://github.com/google/googletest",
)

# Google Protocol Buffers.
http_archive(
    name = "com_google_protobuf",
    sha256 = "e8c7601439dbd4489fe5069c33d374804990a56c2f710e00227ee5d8fd650e67",
    strip_prefix = "protobuf-3.11.2",
    urls = [
        "https://github.com/protocolbuffers/protobuf/archive/v3.11.2.tar.gz",
    ],
)

load("@com_google_protobuf//:protobuf_deps.bzl", "protobuf_deps")

protobuf_deps()

# Google APIs for Cloud Spanner protos.
# TODO: Switch from fork after https://github.com/googleapis/googleapis/pull/553 is merged.
http_archive(
    name = "com_google_googleapis",
    sha256 = "3a426981242af9c05dbc3cdfc72f6627516232bbccaebaab1711397606184973",
    strip_prefix = "googleapis-66d43496b46c26915d7d37302cddbd81481302d7",
    urls = [
        "https://github.com/michael-kernel-sanders/googleapis/archive/66d43496b46c26915d7d37302cddbd81481302d7.zip",
    ],
)

# Java gRPC support for Android examples.
http_archive(
    name = "io_grpc_grpc_java",
    sha256 = "446ad7a2e85bbd05406dbf95232c7c49ed90de83b3b60cb2048b0c4c9f254d29",
    strip_prefix = "grpc-java-1.29.0",
    urls = [
        "https://github.com/grpc/grpc-java/archive/v1.29.0.zip",
    ],
)

load("@io_grpc_grpc_java//:repositories.bzl", "grpc_java_repositories")

grpc_java_repositories()

# TODO: Create a deps function for the googleapis repo.
http_archive(
    name = "com_google_api_codegen",
    sha256 = "ba19948ebc4ea39358ba07fc0253f8927d7a2c9ba3462e8f34faad7ad5ac4142",
    strip_prefix = "gapic-generator-8e930b79e846b9d4876462be9dc4c1dbc04e2903",
    urls = ["https://github.com/googleapis/gapic-generator/archive/8e930b79e846b9d4876462be9dc4c1dbc04e2903.zip"],
)

http_archive(
    name = "org_tensorflow",
    sha256 = "4844e49a4d6ed9bceef608ce7f65f41b75e6362b2721c4e0d34a053d58753f42",
    strip_prefix = "tensorflow-11bed638b14898cdde967f6b108e45732aa4798a",
    urls = [
        # Head commit on 2020-01-20.
        "https://github.com/tensorflow/tensorflow/archive/11bed638b14898cdde967f6b108e45732aa4798a.tar.gz",
    ],
)

# TensorFlow dependency.
http_archive(
    name = "io_bazel_rules_closure",
    sha256 = "5b00383d08dd71f28503736db0500b6fb4dda47489ff5fc6bed42557c07c6ba9",
    strip_prefix = "rules_closure-308b05b2419edb5c8ee0471b67a40403df940149",
    urls = [
        # Head commit on 2019-06-13.
        "https://github.com/bazelbuild/rules_closure/archive/308b05b2419edb5c8ee0471b67a40403df940149.tar.gz",
    ],
)

# WebAssembly Binary Toolkit
#
# The config.h.patch is generated by following the wabt build instructions to
# generate a new config.h file, and then converting that into a patch file. E.g.
# in the wabt repo directory:
#
# ~~~
# $ mkdir build
# $ cd build
# $ cmake ..
# $ cmake --build .
# $ diff -Naur /dev/null config.h > config.h.patch
# ~~~
http_archive(
    name = "wabt",
    build_file = "@//third_party/wabt:wabt.BUILD",
    patches = [
        "//third_party/wabt:config.h.patch",
    ],
    sha256 = "5333949ed4ae63808afa0d1f7d627cd7485ebeec339590571e5f2cb21e304f79",
    strip_prefix = "wabt-1.0.12",
    urls = ["https://github.com/WebAssembly/wabt/archive/1.0.12.tar.gz"],
)

# Tool used for creating a compilation database.
http_archive(
    name = "io_kythe",
    sha256 = "85dac12cdeea46f9e369ff109934aa98967bed1cd7c4c4afdc11577c3f99d31a",
    strip_prefix = "kythe-4814f9f3fcc05c49fbe11f62f1e58a428048da27",
    urls = [
        # Head commit on 2019-12-03.
        "https://github.com/kythe/kythe/archive/4814f9f3fcc05c49fbe11f62f1e58a428048da27.tar.gz",
    ],
)

# Kythe tool dependency.
# Loading only a subset of Kythe dependencies necessary for
# compilation database generation.
# https://github.com/kythe/kythe/blob/4814f9f3fcc05c49fbe11f62f1e58a428048da27/external.bzl#L110-L123
http_archive(
    name = "com_github_google_glog",
    build_file_content = "\n".join([
        "load(\"//:bazel/glog.bzl\", \"glog_library\")",
        "glog_library(with_gflags=0)",
    ]),
    sha256 = "9b4867ab66c33c41e2672b5de7e3133d38411cdb75eeb0d2b72c88bb10375c71",
    strip_prefix = "glog-ba8a9f6952d04d1403b97df24e6836227751454e",
    url = "https://github.com/google/glog/archive/ba8a9f6952d04d1403b97df24e6836227751454e.zip",
)

# Kythe tool dependency.
# https://github.com/kythe/kythe/blob/4814f9f3fcc05c49fbe11f62f1e58a428048da27/external.bzl#L75-L85
http_archive(
    name = "com_github_tencent_rapidjson",
    build_file = "@io_kythe//third_party:rapidjson.BUILD",
    sha256 = "8e00c38829d6785a2dfb951bb87c6974fa07dfe488aa5b25deec4b8bc0f6a3ab",
    strip_prefix = "rapidjson-1.1.0",
    url = "https://github.com/Tencent/rapidjson/archive/v1.1.0.zip",
)

# Bazel rules for Android applications.
http_archive(
    name = "rules_android",
    sha256 = "cd06d15dd8bb59926e4d65f9003bfc20f9da4b2519985c27e190cddc8b7a7806",
    strip_prefix = "rules_android-0.1.1",
    urls = ["https://github.com/bazelbuild/rules_android/archive/v0.1.1.zip"],
)

load("@rules_android//android:rules.bzl", "android_ndk_repository", "android_sdk_repository")

android_sdk_repository(
    name = "androidsdk",
    api_level = 28,
    build_tools_version = "28.0.3",
)

android_ndk_repository(
    name = "androidndk",
    api_level = 28,
)

load("@com_github_grpc_grpc//bazel:grpc_deps.bzl", "grpc_deps")

grpc_deps()

load("@com_github_grpc_grpc//bazel:grpc_extra_deps.bzl", "grpc_extra_deps")

grpc_extra_deps()

http_archive(
    name = "io_bazel_rules_go",
    sha256 = "142dd33e38b563605f0d20e89d9ef9eda0fc3cb539a14be1bdb1350de2eda659",
    urls = [
        "https://mirror.bazel.build/github.com/bazelbuild/rules_go/releases/download/v0.22.2/rules_go-v0.22.2.tar.gz",
        "https://github.com/bazelbuild/rules_go/releases/download/v0.22.2/rules_go-v0.22.2.tar.gz",
    ],
)

load("@io_bazel_rules_go//go:deps.bzl", "go_register_toolchains", "go_rules_dependencies")

go_rules_dependencies()

go_register_toolchains()

# Download Gazelle
http_archive(
    name = "bazel_gazelle",
    sha256 = "d8c45ee70ec39a57e7a05e5027c32b1576cc7f16d9dd37135b0eddde45cf1b10",
    urls = [
        "https://storage.googleapis.com/bazel-mirror/github.com/bazelbuild/bazel-gazelle/releases/download/v0.20.0/bazel-gazelle-v0.20.0.tar.gz",
        "https://github.com/bazelbuild/bazel-gazelle/releases/download/v0.20.0/bazel-gazelle-v0.20.0.tar.gz",
    ],
)

# Load and call Gazelle dependencies
load("@bazel_gazelle//:deps.bzl", "gazelle_dependencies", "go_repository")

gazelle_dependencies()

# Repositories used by Go code.
go_repository(
    name = "com_github_golang_glog",
    importpath = "github.com/golang/glog",
    sum = "h1:VKtxabqXZkF25pY9ekfRL6a582T4P37/31XEstQ5p58=",
    version = "v0.0.0-20160126235308-23def4e6c14b",
)

go_repository(
    name = "org_golang_google_grpc",
    importpath = "google.golang.org/grpc",
    sum = "h1:wdKvqQk7IttEw92GoRyKG2IDrUIpgpj6H6m81yfeMW0=",
    version = "v1.25.1",
)

go_repository(
    name = "com_github_golang_protobuf",
    importpath = "github.com/golang/protobuf",
    sum = "h1:6lQm79b+lXiMfvg/cZm0SGofjICqVBUtrP5yJMmIC1U=",
    version = "v1.3.2",
)

go_repository(
    name = "org_golang_x_net",
    importpath = "golang.org/x/net",
    sum = "h1:oWX7TPOiFAMXLq8o0ikBYfCJVlRHBcsciT5bXOrH628=",
    version = "v0.0.0-20190311183353-d8887717615a",
)

go_repository(
    name = "org_golang_x_text",
    importpath = "golang.org/x/text",
    sum = "h1:g61tztE5qeGQ89tm6NTjjM9VPIm088od1l6aSorWRWg=",
    version = "v0.3.0",
)

load("@io_kythe//:setup.bzl", "kythe_rule_repositories")

kythe_rule_repositories()

# Kythe requires `go_rules_compat` to be loaded.
# https://github.com/kythe/kythe/blob/9941fe8eabba4612daea78ce69c5cc205e9b0791/WORKSPACE#L28-L39
# https://github.com/kythe/kythe/issues/4237
# Visibility warnings are disabled, since they cause check_formatting to fail.
# buildifier: disable=bzl-visibility
load("@io_bazel_rules_go//go/private:compat/compat_repo.bzl", "go_rules_compat")

go_rules_compat(
    name = "io_bazel_rules_go_compat",
)

# clang + llvm 8.0
http_archive(
    name = "clang",
    build_file = "//toolchain:all_files.BUILD",
    sha256 = "0f5c314f375ebd5c35b8c1d5e5b161d9efaeff0523bac287f8b4e5b751272f51",
    strip_prefix = "clang+llvm-8.0.0-x86_64-linux-gnu-ubuntu-18.04",
    url = "http://releases.llvm.org/8.0.0/clang+llvm-8.0.0-x86_64-linux-gnu-ubuntu-18.04.tar.xz",
)

# Gcc compiler for Arm
# We need the compiler in order to get the sysroot for aarch64_linux to crosscompile + all the
# needed libraries to link agaisnt.
# NB: we are not usign gcc to build, clang is still the default compiler.
http_archive(
    name = "gcc_arm",
    build_file = "//toolchain:all_files.BUILD",
    sha256 = "8ce3e7688a47d8cd2d8e8323f147104ae1c8139520eca50ccf8a7fa933002731",
    strip_prefix = "gcc-arm-8.3-2019.03-x86_64-aarch64-linux-gnu",
    url = "https://developer.arm.com/-/media/Files/downloads/gnu-a/8.3-2019.03/binrel/gcc-arm-8.3-2019.03-x86_64-aarch64-linux-gnu.tar.xz",
)

load("//toolchain:emcc_toolchain_config.bzl", "emsdk_configure")

# Should be configured after loading `clang`.
emsdk_configure(name = "emsdk")

load("@io_bazel_rules_closure//closure:defs.bzl", "closure_repositories")

closure_repositories()

# Do not use `tf_workspace()` - it interferes with c-ares in gRPC loaded and patched
# and causes missing `ares.h` error.
# https://github.com/tensorflow/tensorflow/blob/25a06bc503c7d07ffc5480ac107e3c8681937971/tensorflow/workspace.bzl#L970-L975
load("@org_tensorflow//tensorflow:workspace.bzl", "tf_repositories")

tf_repositories()

# Bazel rules for packaging and deployment by Grakn Labs
http_archive(
    name = "graknlabs_bazel_distribution",
    sha256 = "cbb8357cc5b78a141ab7871558916c991f3ba80778d91fd4e2aa6b7894f52749",
    strip_prefix = "bazel-distribution-01973c5e50eadf7a64273d72d0158d58012f977c",
    url = "https://github.com/graknlabs/bazel-distribution/archive/01973c5e50eadf7a64273d72d0158d58012f977c.zip",
)

load("@graknlabs_bazel_distribution//common:dependencies.bzl", "bazelbuild_rules_pkg")

bazelbuild_rules_pkg()

load("@graknlabs_bazel_distribution//packer:dependencies.bzl", "deploy_packer_dependencies")

deploy_packer_dependencies()
