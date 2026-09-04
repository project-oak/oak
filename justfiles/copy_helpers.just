# These are the core rules for copying the supported artifact types into the output directory.
# We use these to keep track of outputs that we want to track through bazel
# configuration changes, share with CI hosts, or publish transparently.
#
# They ensure that the target is built; this should not add too much time, since already-built
# targets will quickly complete the "build" command.

# This target expects a rule that outputs one binary, and copies it to artifacts/binaries with the given name.
[private]
copy-binary target dest platform="":
    bazel build {{target}} --config=release {{ if platform != "" { "--platforms=" + platform } else { "" } }}
    mkdir --parents artifacts/binaries
    cp --force --preserve=timestamps --no-preserve=mode \
        $(bazel cquery --config=release {{ if platform != "" { "--platforms=" + platform } else { "" } }} {{target}} --output files) \
        artifacts/binaries/{{dest}}

# This file copies all outputs of the given target to the artifacts/subjects subdirectory.
[private]
copy-subjects target dest platform="":
    mkdir --parents artifacts/subjects/{{dest}}
    bazel build {{target}} --config=release {{ if platform != "" { "--platforms=" + platform } else { "" } }}
    cp --force --preserve=timestamps --no-preserve=mode \
        $(bazel cquery --config=release {{ if platform != "" { "--platforms=" + platform } else { "" } }} {{target}} --output files) \
        artifacts/subjects/{{dest}}

# This rule copies all file outputs of the given target to the artifacts/binaries.
[private]
copy-binaries target dest platform="":
    #!/bin/sh
    bazel build {{target}} --config=release {{ if platform != "" { "--platforms=" + platform } else { "" } }}
    mkdir --parents artifacts/binaries/{{dest}}
    for output in $(bazel cquery --config=release {{ if platform != "" { "--platforms=" + platform } else { "" } }} {{target}} --output files)
    do
        if [ -f "$output" ]
        then
            cp --force --preserve=timestamps --no-preserve=mode "$output" artifacts/binaries/{{dest}}
        fi
    done

[private]
copy-all target dest platform="":
    mkdir --parents artifacts/{{dest}}
    bazel build {{target}} --config=release {{ if platform != "" { "--platforms=" + platform } else { "" } }}
    cp --recursive --force --preserve=timestamps --no-preserve=mode \
        $(bazel cquery --config=release {{ if platform != "" { "--platforms=" + platform } else { "" } }} {{target}} --output files) \
        artifacts/{{dest}}
