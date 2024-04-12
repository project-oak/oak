# This won't stick around long, just using it while working on this.

readonly SCRIPTS_DIR="$(dirname "$0")"

cd "$SCRIPTS_DIR"

tar --list --file ./target/image-old.tar.xz > target/original_files
# The bazel-built tar has `./` in front of the files.
tar --list --file ./target/image.tar.xz | sed --expression 's/\.\///g' > target/bazel_files
diff --unified target/original_files target/bazel_files
