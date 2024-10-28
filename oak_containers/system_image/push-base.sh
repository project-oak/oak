set -o xtrace
set -o errexit
set -o nounset
set -o pipefail

readonly SCRIPTS_DIR="$(dirname "$0")"

printf "If you haven't done a push before, you'll need to set up gcloud auth:\n"
printf "Install gcloud if needed: https://cloud.google.com/sdk/docs/downloads-interactive\n"
printf "And then:\n\n"
printf "  gcloud auth login\n"
printf "  gcloud config set project oak-ci\n"
printf "  gcloud auth configure-docker\n"
printf "  gcloud auth configure-docker europe-west2-docker.pkg.dev\n"

readonly TARGET_DIR=oak_containers/system_image/target
if [ "$1" == "vanilla" ]
then
    $SCRIPTS_DIR/build-base.sh vanilla
    readonly source=base-image.tar
    readonly static_dir="base-image"
elif [ "$1" == "nvidia" ]
then
    $SCRIPTS_DIR/build-base.sh nvidia
    readonly source=nvidia-base-image.tar
    readonly static_dir="nvidia-base-image"
elif [ "$1" == "sysroot" ]
then
    $SCRIPTS_DIR/build-base.sh sysroot
    readonly source=sysroot.tar
    readonly static_dir="sysroot"
else
  set +o xtrace
  echo ""
  echo "Push one of the containers base images.
  echo "Provide either vanilla or nvidia or sysroot as an argument
  echo ""
fi

xz --force "$TARGET_DIR/$source"
sha256sum=$(sha256sum "$TARGET_DIR/$source.xz" | cut -d " " -f 1)
gsutil cp "$TARGET_DIR/$source.xz"  "gs://oak-bins/$static_dir/$sha256sum.tar.xz"
