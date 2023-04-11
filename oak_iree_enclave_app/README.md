# IREE Enclave Application

IREE application binary that can be run under Restricted Kernel.

### Building

Building IREE Enclave Application requires compiled binary files that are not
currently checked-in the main Github repository. These files include:

1. Compiled IREE library file `libiree.a` (compiled internally)
2. Compiled `newlib` library dependencies (`` and ``)
