searchState.loadedDescShard("snp_measurement", 0, "Returns the argument unchanged.\nCalls <code>U::from(self)</code>.\nThe SEV-SNP CPUID page.\nWhether the page is part of an initial migration image …\nReserved value.\nThe page is not an IMI page.\nThe page is a normal page.\nThe size of the PageInfo struct.\nImplementation of the Page Info structure used for …\nThe type of page being measured.\nThe SEV-SNP secrets page.\nA page that is encrypted but not measured.\nThe page contains a VM state save area (VMSA) for a vCPU.\nA page filled with zeros.\nWhether the page is part of an initial migration image. …\nThe length of this struct in bytes.\nReserved. Must be 0.\nThe permissions for VMPL1. For now we treat this as …\nThe permissions for VMPL2. For now we treat this as …\nThe permissions for VMPL3. For now we treat this as …\nThe SHA-384 digest of the contents to be measured for …\nThe current measurement up to this point.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nTry to create Self from the raw representation\nTry to create Self from the raw representation\nThe guest-physical address of the page being measured.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nThe type of page being measured.\nSets the <code>contents</code> field based to the SHA-384 digest of the …\nCalculates the SHA-384 digest of the struct’s memory and …\nUpdates the current measurement digest from a byte slice …\nUpdates the current measurement digest for a …\nUpdates the current measurement digest from a VMSA page.\nThe address of the first byte after the end of the …\nThe reverse offset from the end of the firmware blob to …\nThe size of the header of an entry in the GUID table.\nThe footer GUID identifying the end of the GUID table.\nThe header of a guid table entry.\nThe maximum size of the shadow firmware for legacy boot.\nThe address of the first byte after the end of the legacy …\nThe GUID identifying the SEV ES reset block GUID table …\nThe GUID identifying the SEV metadata GUID table entry.\nThe size of the SEV metadata section entry.\nThe size of the SEV metadata section header.\nThe version of SEV metadata sections we expect to …\nThe expected first 4 bytes of the SEV metadata section …\nThe instruction pointer and code segment base that will be …\nThe header of the SEV metadata section.\nInformation about the pages specified in the firmware SEV …\nThe page types used in the firmware SEV metadata section …\nThe contents of the Stage 0 firmware ROM image and its …\nThe bytes of the State 0 firmware ROM image.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nTry to create Self from the raw representation\nGets the main contents of the GUID table, excluding the …\nGets the SEV-ES reset block from the firmware image.\nGets the SEV-SNP specific pages defined in the firmware …\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nThe offset into the firmware ROM image from where the …\nGets the bytes of the legacy boot shadow of the ROM image.\nThe start address of the legacy boot shadow of the …\nLoads the Stage 0 firmware ROM image from the supplied …\nParses the GUID table from the firmware image as a map.\nGets the bytes of the entire ROM image.\nThe start address of the firmware ROM in guest memory.\nThe CPU family of the vCPU we expect to be running on.\nThe CPU model of the vCPU we expect to be running on.\nThe stepping of the vCPU we expect to be running on.\nThe guest-physical address of the VMSA page.\nGets the initial VMSA for additional vCPUs that are not …\nGets the initial VMSA for the vCPU that is used to boot …")