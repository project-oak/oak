set working-directory := '..'

# Recipes for dealing with Rust crates

[private]
default:
    @just --list crates

# Repin all crates.
repin: repin-oak repin-codelab repin-private-memory
# ... only in Oak.
repin-oak: (repin-cmd "true")
# ... only in Codelab.
[working-directory: "codelab"]
repin-codelab: (repin-cmd "true" "codelab")
# ... only in Private Memory.
[working-directory: "oak_private_memory"]
repin-private-memory: (repin-cmd "true" "oak_private_memory")

# Update all crates to latest version allowed by semver spec, in all Bazel projects.
update: update-oak update-codelab update-private-memory
# ... only in Oak.
update-oak: (repin-cmd "full")
# ... only in Codelab.
update-codelab: (repin-cmd "full" "codelab")
# ... only in Private Memory.
update-private-memory: (repin-cmd "full" "oak_private_memory")

[doc("Update a specific crate in Oak, using Rust version syntax.
For example:
    just bazel-update-crate curve25519-dalek@4.1.3
")]
update-crate crate: (repin-cmd crate)

[private]
[no-cd]
repin-cmd arg dir=".":
    @# Running most bazel commands will trigger the update when it's needed.
    @# bazel sync actually causes the whole thing to take a fair bit longer.
    cd {{dir}} && pwd && CARGO_BAZEL_REPIN=1 bazel info bazel-bin
