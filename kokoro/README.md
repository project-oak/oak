# Kokoro CI scripts

These are scripts referenced by Kokoro CI jobs.

Jobs: go/oak-kokoro-jobs

Build Configs: go/oak-kokoro-builds

Scripts in the top-level directory should correspond directly to one of the
named jobs, with the same name.

In cases we are transitioning the structure or naming of something, symlinks may
be present, connecting an old script name still referenced in the job configs to
a new script name that we intend to eventually transition everything to.

Any additional helper scripts should be under the `helpers` directory.
