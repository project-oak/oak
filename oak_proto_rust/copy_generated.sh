set -o xtrace

echo "Copy generated files"

BUILD_SCRIPT_GENERATED_FILES=../../build.out_dir
IMPORTABLE_GENERATED_FILE_DEST=../../../../../../oak_proto_rust/generated

if [ ! -d $BUILD_SCRIPT_GENERATED_FILES ]
then
  set +o xtrace
  echo "The expected bazel workspace directory wasn't found."
  echo "Make sure you run this script via bazel:"
  echo "bazel run oak_proto_rust:copy_generated"
  exit 1
fi

ls -la $BUILD_SCRIPT_GENERATED_FILES

cp "$BUILD_SCRIPT_GENERATED_FILES"/*.rs $IMPORTABLE_GENERATED_FILE_DEST

ls $IMPORTABLE_GENERATED_FILE_DEST

chmod --recursive u+w "$IMPORTABLE_GENERATED_FILE_DEST"
