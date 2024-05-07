set -o xtrace

echo "Verify generated files"

echo "FILES:"
ls -la
echo ""

BUILD_SCRIPT_GENERATED_FILES=../../build.out_dir
IMPORTABLE_GENERATED_FILE_DEST=../../../../../../oak_proto_rust/generated

echo "BSD:"
ls $BUILD_SCRIPT_GENERATED_FILES

if [ ! -d $BUILD_SCRIPT_GENERATED_FILES ]
then
  set +o xtrace
  echo "The expected bazel workspace directory wasn't found."
  echo "Make sure you run this script via bazel:"
  echo "bazel run oak_proto_rust:verify_generated"
  exit 1
fi


for generated in "$BUILD_SCRIPT_GENERATED_FILES"/*
do
  filename=$(basename -- "$generated")
  GENERATED_FILE_HASH=$(sha512sum < "$generated")
  EXISTING_FILE_HASH=$(sha512sum < "$IMPORTABLE_GENERATED_FILE_DEST/$filename")

  if [ "$GENERATED_FILE_HASH" != "$EXISTING_FILE_HASH" ]
  then
    set +o xtrace
    echo ""
    echo "The generated files haven't been moved to an importable location."
    echo "Please run:"
    echo ""
    echo "bazel run oak_proto_rust:copy_generated"
    echo ""
    exit 1
  fi
done

echo "Generated files are up-to-date"
