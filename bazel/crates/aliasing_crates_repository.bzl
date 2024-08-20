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
"""Define a repo that aliases other crates_repository repos."""

def _aliasing_crates_repository_impl(repository_ctx):
    repositories = [json.decode(r) for r in repository_ctx.attr.repositories]

    # Construct a set containing all packages.
    packages = {}
    for repo in repositories:
        packages.update({package: True for package in repo["packages"]})

    # Create a BUILD file with an `alias` rule for each package.
    contents = "package(default_visibility = [\"//visibility:public\"])\n"
    for package in sorted(packages.keys()):
        contents += ("\n" +
                     "alias(\n" +
                     "    name = \"{}\",\n".format(package) +
                     "    actual = select({\n")
        for repo in repositories:
            # We include an entry even if the crates index doesn't contain the
            # package because because the resulting error is clearer than what
            # might happen if a //conditions:default package is used instead.
            target = repo["overrides"].get(package, "@{}//:{}".format(repo["name"], package))
            for condition in repo["conditions"]:
                contents += "        \"{}\": \"{}\",\n".format(condition, target)
        contents += ("    }),\n" +
                     ")\n")

    repository_ctx.file("BUILD", contents, executable = False)

aliasing_crates_repository = repository_rule(
    implementation = _aliasing_crates_repository_impl,
    doc = "Creates a repository that selects between other crates_repository repos.",
    attrs = {
        "repositories": attr.string_list(
            doc = "A list of repositories to alias; see aliased_crates_repository().",
        ),
    },
)

def aliased_crates_repository(name, conditions, packages, overrides = {}):
    """A constructor for an aliased crates_repository.

    Args:
        name (str): The name of crates_repository.
        conditions (list): List of select-compatible conditions indicating when
            the repository should be used.
        packages (list): List of packages (crates) present in the
            crates_repository.
        overrides (dict): Map from crate name to bazel target to use instead of
            the default ("@<name>//:<package>").

    Returns:
        str: A json encoded string of all inputs.
    """

    # Convert fields that may contain Labels to strings before serialization.
    return json.encode({
        "name": name,
        "conditions": [str(c) for c in conditions],
        "packages": packages,
        "overrides": {k: str(v) for k, v in overrides.items()},
    })
