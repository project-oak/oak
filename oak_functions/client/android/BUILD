#
# Copyright 2021 The Project Oak Authors
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

load("@rules_android//android:rules.bzl", "android_binary", "android_library")

package(
    licenses = ["notice"],
)

android_library(
    name = "client_activity",
    srcs = ["com/google/oak/functions/android/client/MainActivity.java"],
    custom_package = "com.google.oak.functions.android.client",
    manifest = "AndroidManifest.xml",
    # exports_manifest = 1,
    resource_files = glob(["com/google/oak/functions/android/client/res/**"]),
    deps = [
        "//oak_functions/client/java:client_android",
        "//oak_functions/proto:invocation_java_proto",
        "@com_google_guava_guava",
        "@com_google_protobuf//:protobuf_java",
        "@com_google_protobuf//:protobuf_java_util",
        "@conscrypt//:conscrypt",
        # "@conscrypt-android",
        ":conscrypt-android-local",
    ],
)

android_binary(
    name = "client_app",
    custom_package = "com.google.oak.functions.android.client",
    manifest = "AndroidManifest.xml",
    # manifest_values = {
    #     "manifest_merger": "android",
    # },
    multidex = "native",
    deps = [
        ":client_activity",
    ],
)

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_file")

http_file(
    name = "conscrypt-android-aar",
    sha256 = "42d18979caf53f5ef68548c76d4c98b41adb910a32ad9448133f9c5b20bd65a3",
    urls = [
        "https://search.maven.org/remotecontent?filepath=org/conscrypt/conscrypt-android/2.5.2/conscrypt-android-2.5.2.aar",
    ]
)

aar_import(
    name = "conscrypt-android-local",
    # licenses = ["notice"],
    # jar_sha256 = "42d18979caf53f5ef68548c76d4c98b41adb910a32ad9448133f9c5b20bd65a3",
    # aar = "search.maven.org/remotecontent?filepath=org/conscrypt/conscrypt-android/2.5.2/conscrypt-android-2.5.2.aar",
    # aar = "https://search.maven.org/remotecontent?filepath=org/conscrypt/conscrypt-android/2.5.2/conscrypt-android-2.5.2.aar",
    aar = ":conscrypt-android-aar"
)
