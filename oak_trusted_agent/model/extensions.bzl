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

"""Fetches Ollama model weights as image layers laid out under /models.

The Ollama registry is an OCI distribution registry. Pinning the manifest
digest pins every blob, since the manifest lists each blob's digest, so a
model needs only its name, tag and manifest digest.
"""

_REGISTRY = "registry.ollama.ai"
_MODELS_DIR = "/models"

_PKG_TAR = """
pkg_tar(
    name = {name},
    srcs = [{src}],
    mode = "0444",
    package_dir = {package_dir},
)
"""

def _check_sha256(hex_digest, context):
    # rctx.download skips verification when sha256 is empty, so reject
    # anything that is not a full digest.
    if len(hex_digest) != 64 or hex_digest.strip("0123456789abcdef"):
        fail("invalid sha256 in {}: {}".format(context, repr(hex_digest)))
    return hex_digest

def _pkg_tar(name, src, package_dir):
    return _PKG_TAR.format(
        name = json.encode(name),
        src = json.encode(src),
        package_dir = json.encode(package_dir),
    )

def _ollama_model_impl(rctx):
    manifest = "manifests/{}/{}/{}".format(_REGISTRY, rctx.attr.model, rctx.attr.tag)
    rctx.download(
        url = "https://{}/v2/{}/manifests/{}".format(_REGISTRY, rctx.attr.model, rctx.attr.tag),
        output = manifest,
        sha256 = _check_sha256(rctx.attr.sha256, rctx.attr.name),
    )
    contents = json.decode(rctx.read(manifest))

    # Ollama stores blobs by digest, so a digest listed twice is one file.
    digests = {contents["config"]["digest"]: None}
    for layer in contents["layers"]:
        digests[layer["digest"]] = None

    build = ['load("@rules_pkg//pkg:tar.bzl", "pkg_tar")']
    build.append(_pkg_tar(
        name = "manifest",
        src = manifest,
        package_dir = "{}/manifests/{}/{}".format(_MODELS_DIR, _REGISTRY, rctx.attr.model),
    ))

    # One layer per blob, so large blobs build and push in parallel.
    layers = [":manifest"]
    for i, digest in enumerate(digests):
        if not digest.startswith("sha256:"):
            fail("unsupported digest in {}: {}".format(manifest, digest))
        hex_digest = _check_sha256(digest.removeprefix("sha256:"), manifest)
        blob = "blobs/sha256-" + hex_digest
        rctx.download(
            url = "https://{}/v2/{}/blobs/{}".format(_REGISTRY, rctx.attr.model, digest),
            output = blob,
            sha256 = hex_digest,
        )
        build.append(_pkg_tar(
            name = "blob_{}".format(i),
            src = blob,
            package_dir = _MODELS_DIR + "/blobs",
        ))
        layers.append(":blob_{}".format(i))

    build.append("""
filegroup(
    name = "layers",
    srcs = {},
    visibility = ["//visibility:public"],
)
""".format(json.encode(layers)))
    rctx.file("BUILD.bazel", "\n".join(build))

_ollama_model = repository_rule(
    implementation = _ollama_model_impl,
    attrs = {
        "model": attr.string(mandatory = True, doc = "Registry name, e.g. library/gemma4."),
        "tag": attr.string(mandatory = True, doc = "Model tag, e.g. e2b-it-qat."),
        "sha256": attr.string(mandatory = True, doc = "SHA-256 of the manifest."),
    },
)

def _ollama_impl(mctx):
    for mod in mctx.modules:
        for model in mod.tags.model:
            _ollama_model(
                name = model.name,
                model = model.model,
                tag = model.tag,
                sha256 = model.sha256,
            )

    # Every input is pinned by hash, so there is nothing to record in the lockfile.
    return mctx.extension_metadata(reproducible = True)

ollama = module_extension(
    implementation = _ollama_impl,
    tag_classes = {
        "model": tag_class(attrs = {
            "name": attr.string(mandatory = True),
            "model": attr.string(mandatory = True),
            "tag": attr.string(mandatory = True),
            "sha256": attr.string(mandatory = True),
        }),
    },
)
