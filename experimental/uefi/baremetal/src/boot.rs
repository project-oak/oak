// Common data needed for all boot paths
pub trait Info {
    // Name of for this boot protocol
    fn name(&self) -> &str;
    // Starting address of the Root System Descriptor Pointer
    fn rsdp_addr(&self) -> u64;
    // The kernel command line (not including null terminator)
    fn cmdline(&self) -> &[u8];
    // Methods to access the E820 Memory map
    fn num_entries(&self) -> u8;
    fn entry(&self, idx: u8) -> E820Entry;
}

#[derive(Clone, Copy, Debug)]
#[repr(C, packed)]
pub struct E820Entry {
    pub addr: u64,
    pub size: u64,
    pub entry_type: u32,
}

impl E820Entry {
    pub const RAM_TYPE: u32 = 1;
}
