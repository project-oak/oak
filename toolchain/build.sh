
BINUTILS_VERSION=2.40

TARGET=x86_64-unknown-oak

# Clean up any previous build directory.
if [ -d build ]; then
  rm -rf build
fi
mkdir -p build

mkdir -p toolchain
DIR=`pwd`/toolchain
cd build

# Step 1: binutils
echo "Building binutils..."
curl -O -L https://ftpmirror.gnu.org/gnu/binutils/binutils-$BINUTILS_VERSION.tar.bz2 > build.log
tar xf binutils-$BINUTILS_VERSION.tar.bz2
(
  cd binutils-$BINUTILS_VERSION
  patch -p1 < ../../binutils-2.40-oak.patch > ../build.log
)
mkdir -p build-binutils
(
  cd build-binutils
  echo "  running configure"
  ../binutils-$BINUTILS_VERSION/configure \
    --target=$TARGET \
    --prefix=$DIR > ../build.log 2>&1 && \
  echo "  running make" && \
  make > ../build.log 2>&1 && \
  echo "  running make install" && \
  make install > ../build.log 2>&1
  if [ $? -ne 0 ]; then
    echo "Failed to build binutils! See build.log for more details."
    exit 1
  fi
)

rm -rf build
echo "Toolchain built in $DIR."
