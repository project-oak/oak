# IREE Enclave Application

IREE application binary that can be run under Restricted Kernel.

## Building

Building IREE Enclave Application requires compiled binary files that are not
currently checked-in the main Github repository. These files include:

1. Compiled IREE library file `libiree_core.a`
   - This library is compiled internally
2. Compiled `newlib` library dependencies (`libc.a` and `libgloss.a`)
   - These libraries could be extracted from archive built with
     `oak/toolchain/build.sh`

All of the library dependencies should be put in the `cc/iree/` directory.
