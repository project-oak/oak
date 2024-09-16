#
# Copyright 2023 The Project Oak Authors
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

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

cc_library(
    name = "hpke-jni-lib",
    srcs = [
        "context_jni.cc",
        "hpke_jni.cc",
        "jni_helper.cc",
        "keypair_jni.cc",
    ],
    hdrs = [
        "com_google_oak_crypto_hpke_Hpke.h",
        "com_google_oak_crypto_hpke_KeyPair.h",
        "com_google_oak_crypto_hpke_RecipientContext.h",
        "com_google_oak_crypto_hpke_SenderContext.h",
        "jni_helper.h",
    ],
    deps = [
        ":jni",
        "//cc/crypto/hpke:recipient_context",
        "//cc/crypto/hpke:sender_context",
        "//cc/crypto/hpke:utils",
        "@com_google_absl//absl/status:statusor",
    ],
    alwayslink = 1,
)

# Hacky workaround to expose <jni.h> headers in cc_library rules. The JNI
# headers are magically exposed to genrules, so we export the headers of
# interest from those genrules. See
# https://github.com/tensorflow/tensorflow/blob/5dfbeab6c01a5919324a94c0092d34e6be218c3d/tensorflow/java/src/main/native/BUILD#L51
genrule(
    name = "copy_jni_h",
    srcs = ["@bazel_tools//tools/jdk:jni_header"],
    outs = ["jni.h"],
    cmd = "cp -f $< $@",
)

genrule(
    name = "copy_jni_md_h",
    srcs = select({
        "@bazel_tools//src/conditions:darwin": ["@bazel_tools//tools/jdk:jni_md_header-darwin"],
        "//conditions:default": ["@bazel_tools//tools/jdk:jni_md_header-linux"],
    }),
    outs = ["jni_md.h"],
    cmd = "cp -f $< $@",
)

cc_library(
    name = "jni",
    hdrs = [
        ":jni.h",
        ":jni_md.h",
    ],
    # The includes line is necessary to expose these as system headers. Be
    # careful not to overpopulate this directory.
    includes = ["."],
)

cc_binary(
    name = "libhpke-jni.so",
    linkshared = 1,
    linkstatic = 1,
    deps = [":hpke-jni-lib"],
)
