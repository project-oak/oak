# C++ FFI Test Application

This enclave application demonstrates calling C++ code from Rust inside an Oak
Restricted Kernel enclave. It serves as a test and integration example for the
[LLVM libc++ port](../../../../third_party/llvm_libc/README.md), exercising C++
standard library features (`std::vector`, `std::sort`, `std::string`,
`std::unique_ptr`) that in turn rely on the Oak LLVM libc port.
