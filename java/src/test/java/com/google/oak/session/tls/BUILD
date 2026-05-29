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

load("@rules_kotlin//kotlin:jvm.bzl", "kt_jvm_test")

package(
    licenses = ["notice"],
)

kt_jvm_test(
    name = "OakSessionTlsTest",
    srcs = ["OakSessionTlsTest.kt"],
    data = ["//oak_session/tls/testing:test_keys"],
    # Break JDK module encapsulation to allow Conscrypt and Bouncy Castle to perform deep
    # reflection on internal X.509 and DER-parsing utilities in java.base.
    #
    # For modular JDK JVM arguments specification, see JEP 261: https://openjdk.org/jeps/261
    # For strict JDK internal strong encapsulation, see JEP 403: https://openjdk.org/jeps/403
    jvm_flags = [
        "--add-opens=java.base/sun.security.x509=ALL-UNNAMED",
        "--add-opens=java.base/sun.security.util=ALL-UNNAMED",
    ],
    target_compatible_with = ["@platforms//os:linux"],
    test_class = "com.google.oak.session.tls.OakSessionTlsTest",
    deps = [
        "//java/src/main/java/com/google/oak/session/tls:cert_util",
        "//java/src/main/java/com/google/oak/session/tls:oak_session_tls",
        "//java/src/main/java/com/google/oak/util:file_util",
        "@maven//:junit_junit",
        "@maven//:org_bouncycastle_bcpkix_jdk18on",
        "@maven//:org_bouncycastle_bcprov_jdk18on",
        "@maven//:org_conscrypt_conscrypt_openjdk_uber",
        "@maven//:org_jetbrains_kotlinx_kotlinx_coroutines_core",
        "@rules_kotlin//kotlin/compiler:kotlin-test",
    ],
)
