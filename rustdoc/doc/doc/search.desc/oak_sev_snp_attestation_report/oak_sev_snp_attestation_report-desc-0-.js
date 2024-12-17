searchState.loadedDescShard("oak_sev_snp_attestation_report", 0, "AMD SEV-SNP data structures for attestation reports.\nA signed attestation report.\nThe data contained in an attestation report.\nWhether the author key digest is included in the report.\nIndicates ciphertext hiding is enabled for the DRAM.\nDebugging the guest is allowed.\nIndicates that the plaform is using error correcting codes …\nECDSA using curve P-384 with SHA-384.\nAn ECDSA signature.\nThe required policy for a guest to run.\nInvalid.\nThe guest can be associated with a migration agent.\nThe author key digest is not present.\nInformation on the platform configuration.\nFlags indicating allowed policy options.\nIndicates that the RAPL feature is disabled.\nThe number of bytes of custom data that can be included in …\nReserved, must always be 1.\nThe guest can only be activated on a single socket.\nSimulatneous multi-threading (SMT) is allowed.\nIndicates that simulatneous multi-threading (SMT) is …\nThe signing algorithm used for the report signature.\nKey used to sign the attestation report.\nIndicates that transparent secure memory encryption (TSME) …\nThe version of all the components in the Trusted Computing …\nThe author key digest is present.\nThe minimum ABI major version required to launch the guest.\nThe minimum ABI minor version required to launch the guest.\nGet a flags value with all known bits set.\nGet a flags value with all known bits set.\nThe SHA-384 digest of the author public key used to …\nThe bitwise and (<code>&amp;</code>) of the bits in two flags values.\nThe bitwise and (<code>&amp;</code>) of the bits in two flags values.\nThe bitwise and (<code>&amp;</code>) of the bits in two flags values.\nThe bitwise and (<code>&amp;</code>) of the bits in two flags values.\nThe bitwise or (<code>|</code>) of the bits in two flags values.\nThe bitwise or (<code>|</code>) of the bits in two flags values.\nThe bitwise or (<code>|</code>) of the bits in two flags values.\nThe bitwise or (<code>|</code>) of the bits in two flags values.\nGet the underlying bits value.\nGet the underlying bits value.\nThe bitwise exclusive-or (<code>^</code>) of the bits in two flags …\nThe bitwise exclusive-or (<code>^</code>) of the bits in two flags …\nThe bitwise exclusive-or (<code>^</code>) of the bits in two flags …\nThe bitwise exclusive-or (<code>^</code>) of the bits in two flags …\nThe current security version number (SVN) of the secure …\nIdentifier unique to the chip, unless the ID has been …\nThe build number of the committed secure firmware ABI …\nThe major number of the committed secure firmware ABI …\nThe minor number of the committed secure firmware ABI …\nThe committed TCB version.\nThe bitwise negation (<code>!</code>) of the bits in a flags value, …\nThe bitwise negation (<code>!</code>) of the bits in a flags value, …\nWhether all set bits in a source flags value are also set …\nWhether all set bits in a source flags value are also set …\nFamily ID (combined Extended Family ID and Family ID).\nModel (combined Extended Model and Model fields).\nStepping.\nThe build number of the current secure firmware ABI …\nThe major number of the current secure firmware ABI …\nThe minor number of the current secure firmware ABI …\nThe current version of each of the components in the …\nThe data contained in the report.\nThe intersection of a source flags value with the …\nThe intersection of a source flags value with the …\nGet a flags value with all bits unset.\nGet a flags value with all bits unset.\nThe bitwise or (<code>|</code>) of the bits in each flags value.\nThe bitwise or (<code>|</code>) of the bits in each flags value.\nThe family ID provided at launch.\nThe allowed settings for the guest.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nConvert from a bits value.\nConvert from a bits value.\nConvert from a bits value exactly.\nConvert from a bits value exactly.\nConvert from a bits value, unsetting any unknown bits.\nConvert from a bits value, unsetting any unknown bits.\nThe bitwise or (<code>|</code>) of the bits in each flags value.\nThe bitwise or (<code>|</code>) of the bits in each flags value.\nGet a flags value with the bits of a flag with the given …\nGet a flags value with the bits of a flag with the given …\nCreates a new AttestationReport with all zeros and the …\nTry to create Self from the raw representation\nTry to create Self from the raw representation\nTry to create Self from the raw representation\nGets the author key enabled field as an <code>AuthorKey</code> enum if …\nGets the flags field as a <code>PolicyFlags</code> representation if …\nGets the value of MaskChipKey.\nGets the platform info field as a <code>PlatformInfo</code> …\nGets the signing algorithm field as a <code>SigningAlgorithm</code> …\nThe guest security version number.\nCustom data provided by the hypervisor at launch.\nThe SHA-384 digest of the ID public key used to sign the …\nThe image ID provided at launch.\nThe bitwise or (<code>|</code>) of the bits in two flags values.\nThe bitwise or (<code>|</code>) of the bits in two flags values.\nThe bitwise and (<code>&amp;</code>) of the bits in two flags values.\nThe bitwise and (<code>&amp;</code>) of the bits in two flags values.\nWhether any set bits in a source flags value are also set …\nWhether any set bits in a source flags value are also set …\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nWhether all known bits in this flags value are set.\nWhether all known bits in this flags value are set.\nWhether all bits in this flags value are unset.\nWhether all bits in this flags value are unset.\nYield a set of contained flags values.\nYield a set of contained flags values.\nYield a set of contained named flags values.\nYield a set of contained named flags values.\nThe value of the current TCB version when the guest was …\nThe measurement of the VM memory calculated at launch.\nThe lowest current patch level of all the CPU cores.\nThe bitwise negation (<code>!</code>) of the bits in a flags value, …\nThe bitwise negation (<code>!</code>) of the bits in a flags value, …\nInformation about the platform.\nThe policy required by the guest VM to be launched.\nThe R component of this signature. The value is …\nThe intersection of a source flags value with the …\nThe intersection of a source flags value with the …\nGuest-provided data. The custom data provided in the …\nThe report ID of this guest.\nThe report ID of this guest’s migration agent.\nThe reported TCB version that was used to generate the …\nThe S component of this signature. The value is …\nCall <code>insert</code> when <code>value</code> is <code>true</code> or <code>remove</code> when <code>value</code> is …\nCall <code>insert</code> when <code>value</code> is <code>true</code> or <code>remove</code> when <code>value</code> is …\nThe signature over the data.\nThe algorithm used to sign the report.\nThe current SVN of the SNP firmware.\nThe intersection of a source flags value with the …\nThe intersection of a source flags value with the …\nThe intersection of a source flags value with the …\nThe intersection of a source flags value with the …\nThe bitwise exclusive-or (<code>^</code>) of the bits in two flags …\nThe bitwise exclusive-or (<code>^</code>) of the bits in two flags …\nThe current SVN of the PSP operating system.\nThe bitwise exclusive-or (<code>^</code>) of the bits in two flags …\nThe bitwise exclusive-or (<code>^</code>) of the bits in two flags …\nThe bitwise or (<code>|</code>) of the bits in two flags values.\nThe bitwise or (<code>|</code>) of the bits in two flags values.\nChecks that the report data is valid and the signature has …\nChecks that fields with specific expected values or ranges …\nChecks that the flags are valid and the reserved bytes are …\nChecks that the reserved bytes are all zero.\nChecks that the reserved bytes are all zero.\nThe version of the attestation report format.\nThe VMPL value that was passed in the request.")