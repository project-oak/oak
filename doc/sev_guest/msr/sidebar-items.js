window.SIDEBAR_ITEMS = {"constant":[["NO_PREFERRED_GHCB_LOCATION","Value indicating that the hypervisor does not have a preferred location for the GHCB."],["SUPPORTED_PROTOCOL_VERION","The version of the GHCB MSR protocol supported by this library. This represents the version specific to AMD SEV-SNP."]],"enum":[["CpuidRegister","The register of interest from the result of executing CPUID."],["PageAssignment","Whether a memory page is private to the guest, or shared with the hypervisor."],["RegisterGhcbGpaError",""],["SevStatusError",""],["TerminationReason","The reason for requesting termination from the hypervisor."]],"fn":[["change_snp_page_state","Requests a change of state for a page to be either private to the guest VM, or shared with the hypervisor."],["get_cpuid","Gets the value of the specified register that was returned when executing CPUID for the specified leaf. Sub-leafs are not supported."],["get_hypervisor_feature_support","Requests a bitmap specifying the features supported by the hypervisor."],["get_preferred_ghcb_location","Requests the hypervisor’s preferred location for the GHCB page."],["get_sev_info","Gets information about the supported GHCB MSR protocol verions and the location of the encryption bit."],["get_sev_status","Gets the status of SEV features for the current guest."],["register_ghcb_location","Registers the location of the GHCB page for the current vCPU with the hypervisor."],["request_termination","Requests termination from the hypervisor."],["set_ghcb_address_and_exit","Sets the address of the GHCB page before exiting to the hypervisor."]],"struct":[["CpuidRequest","A request to execute CPUID for a specific leaf and return one of the result registers."],["CpuidResponse","A response from executing CPUID for a specific leaf. Only one register is returned at a time."],["GhcbGpa","Contains the guest-physical address of the GHCB page. The address must have been registered with the hypervisor before using it."],["HypervisorFeatureSupportRequest","A request for the hypervisor’s supported features."],["HypervisorFeatureSupportResponse","Flags indicating which features are supported by the hypervisor."],["PreferredGhcbGpaRequest","A request for the hypervisor’s preferred location for the GHCB page."],["PreferredGhcbGpaResponse","The response containing the preferred location of the GHCB."],["RegisterGhcbGpaRequest","Request to register a guest-physical address for the GHCB with the hypervisor."],["RegisterGhcbGpaResponse","The response containing the result of the GHCB registration."],["SevInfoRequest","A request for information about the supported GHCB MSR protocol version and the encryption bit."],["SevInfoResponse","Response from the hypervisor about the encryption bit and supported GHCB protocol versions. The encryption bit value is validated by the hardware before the guest is resumed."],["SevStatus","Flags indicating which SEV features are active."],["SnpPageStateChangeRequest","Request to change a memory page from shared to private or private to shared."],["SnpPageStateChangeResponse","The response containing the result of the SNP Page State Change operation."],["TerminationRequest","Request for the hypervisor to terminate the guest."]]};