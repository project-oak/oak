
BINUTILS_VERSION=2.40
GCC_VERSION=12.2.0
NEWLIB_VERSION=4.3.0.20230120

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

# Step 2: GCC. Just the compiler parts; we'll come back for the C++ standard library later.
echo "Building GCC..."
curl -O -L https://ftpmirror.gnu.org/gnu/gcc/gcc-$GCC_VERSION/gcc-$GCC_VERSION.tar.gz > build.log
tar xf gcc-$GCC_VERSION.tar.gz
(
  cd gcc-$GCC_VERSION
  patch -p1 < ../../gcc-12.2.0-oak.patch > ../build.log
)
mkdir -p build-gcc
(
  cd build-gcc
  echo "  running configure"
  ../gcc-$GCC_VERSION/configure \
    --target=$TARGET \
    --prefix=$DIR \
    --with-sysroot=$DIR \
    --enable-languages=c,c++ \
    --enable-host-shared \
    --with-gnu-as \
    --with-gnu-ld \
    --disable-multilib \
    --disable-threads \
    --disable-initifini-array \
    --with-newlib >> ../build.log 2>&1 && \
  echo "  running make" && \
  make all-gcc all-target-libgcc >> ../build.log 2>&1 && \
  echo "  running make install" && \
  make install-gcc install-target-libgcc >> ../build.log 2>&1
  if [ $? -ne 0 ]; then
    echo "Failed to build GCC! See build.log for more details."
    exit 1
  fi
)

# Step 3: Newlib, aka libc, libm and libgloss
echo "Building newlib..."
curl -O -L ftp://sourceware.org/pub/newlib/newlib-$NEWLIB_VERSION.tar.gz > build.log
tar xf newlib-$NEWLIB_VERSION.tar.gz
(
  cd newlib-$NEWLIB_VERSION
  patch -p1 < ../../newlib-4.3.0-oak.patch >> ../build.log
  cp ../../newlib/* libgloss/oak
)
mkdir -p build-newlib
(
  cd build-newlib
  echo "  running configure"
  PATH="$PATH:$DIR/bin" ../newlib-$NEWLIB_VERSION/configure \
    --target=$TARGET \
    --prefix=$DIR \
    --disable-multilib >> ../build.log 2>&1 && \
  echo "  running make" && \
  PATH="$PATH:$DIR/bin" make >> ../build.log 2>&1 && \
  echo "  running make install" && \
  PATH="$PATH:$DIR/bin" make install >> ../build.log 2>&1
  if [ $? -ne 0 ]; then
    echo "Failed to build newlib! See build.log for more details."
    exit 1
  fi
)

# Step 4: now that we have a C library, build the C++ library
echo "Building libstdc++..."
# we should have the GCC build directory from Step 2
(
  cd build-gcc
  echo "  running make" && \
  make all-target-libstdc++-v3 >> ../build.log 2>&1 && \
  echo "  running make install" && \
  make install-target-libstdc++-v3 >> ../build.log 2>&1
  if [ $? -ne 0 ]; then
    echo "Failed to build libstdc++! See build.log for more details."
    exit 1
  fi
)

rm -rf build
echo "Toolchain built in $DIR."
