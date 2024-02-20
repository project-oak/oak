# AMD SEV-SNP Guest Library

This library implements Rust wrappers for new CPU instructions introduced for
AMD SEV-ES and SEV-SNP. It also adds structs that represent data structures used
by AMD SEV-ES and SEV-SNP.

For more information see:

- [https://developer.amd.com/sev/](https://developer.amd.com/sev/)
- [AMD64 Architecture Programmer’s Manual, Volume 2: System Programming](https://www.amd.com/system/files/TechDocs/24593.pdf) -
  Sections 15.34 - 15.36
- [SEV-ES Guest-Hypervisor Communication Block Standardization](https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf)
- [SEV Secure Nested Paging Firmware ABI Specification](https://www.amd.com/system/files/TechDocs/56860.pdf)
- Whitepaper:
  [AMD SEV-SNP: Strengthening VM Isolation with Integrity Protection and More](https://www.amd.com/system/files/TechDocs/SEV-SNP-strengthening-vm-isolation-with-integrity-protection-and-more.pdf)
