use core::mem::size_of;

bitflags::bitflags! {
    // An extension of x86_64::structures::gdt::DescriptorFlags
    struct Descriptor: u64 {
        const LIMIT_0_15 =   0xFFFF;
        const BASE_0_23 = 0xFF_FFFF << 16;
        const ACCESSED =          1 << 40;
        const WRITABLE =          1 << 41;  // Only for Data-Segments
        const READABLE =          1 << 41;  // Only for Code-Segments
        const EXPANSION =         1 << 42;  // Only for Data-Segments
        const CONFORMING =        1 << 42;  // Only for Code-Segments
        const EXECUTABLE =        1 << 43;
        const USER_SEGMENT =      1 << 44;
        const DPL_RING_3 =        3 << 45;
        const PRESENT =           1 << 47;
        const LIMIT_16_19 =     0xF << 48;
        const SOFTWARE =          1 << 52;
        const BIT64 =             1 << 53;
        const BIT32 =             1 << 54;
        const GRANULARITY =       1 << 55;
        const BASE_24_31 =     0xFF << 56;

        // All segments are nonconforming, non-system, ring-0 only, and present.
        // We set ACCESSED in advance to avoid writing to the descriptor.
        const COMMON = Self::ACCESSED.bits | Self::USER_SEGMENT.bits | Self::PRESENT.bits;
        // BIT32 must be 0, all other bits (not yet mentioned) are ignored.
        const CODE64 = Self::COMMON.bits | Self::READABLE.bits | Self::EXECUTABLE.bits | Self::BIT64.bits;
        const DATA64 = Self::COMMON.bits | Self::WRITABLE.bits | Self::BIT64.bits;
    }
}

// An alternative to x86_64::structures::DescriptorTablePointer that avoids
// "pointer-to-integer cast" (which rust does not support in statics).
#[repr(C, packed)]
struct Pointer {
    limit: u16,
    base: &'static Descriptor,
}

impl Pointer {
    const fn new(gdt: &'static [Descriptor]) -> Self {
        let size = gdt.len() * size_of::<Descriptor>();
        Self {
            limit: size as u16 - 1,
            base: &gdt[0],
        }
    }
}

// Our 64-bit GDT lives in RAM, so it can be accessed like any other global.
#[no_mangle]
static GDT64_PTR: Pointer = Pointer::new(&GDT64);
static GDT64: [Descriptor; 3] = [Descriptor::empty(), Descriptor::CODE64, Descriptor::DATA64];
