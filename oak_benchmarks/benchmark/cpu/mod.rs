//
// Copyright 2026 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

//! CPU-bound benchmarks.

use core::fmt;

use bitflags::bitflags;

pub mod hashing;

/// Common interface for CPU-bound benchmarks.
///
/// CPU benchmarks use the `run::<T>()` method on specific implementations,
/// where `T` is a [`BenchmarkTimer`](crate::timer::BenchmarkTimer) chosen by
/// the host application.
pub trait CpuBenchmark {
    /// Maximum data size this benchmark supports.
    fn max_data_size(&self) -> usize;
}

bitflags! {
    /// A set of instruction-set extensions relevant to the crypto benchmarks.
    ///
    /// The set is not "every extension the CPU has". It is exactly those that a
    /// cryptographic crate in this suite dispatches on, because a difference in
    /// any of them means the two platforms ran different code and the comparison
    /// is between instruction sets rather than between kernels.
    ///
    /// The bit positions travel in the wire format, so they are assigned
    /// explicitly and may not be reordered or reused, and the whole set has to
    /// stay inside one byte. See [`CpuFeatures::to_wire`] for how two of these
    /// sets are packed together.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct FeatureSet: u32 {
        /// SHA-NI (`sha256rnds2` and friends).
        const SHA_NI = 1 << 0;
        /// AES-NI (`aesenc` and friends).
        const AES_NI = 1 << 1;
        /// Carry-less multiply, used for the GCM authenticator.
        const PCLMULQDQ = 1 << 2;
        /// AVX2, used by the portable SHA-2 and Keccak backends.
        const AVX2 = 1 << 3;
        /// AVX-512 IFMA (`vpmadd52luq` / `vpmadd52huq`).
        ///
        /// `curve25519-dalek` runtime-dispatches its field arithmetic onto this
        /// when the CPU offers it, which makes Ed25519 substantially faster than
        /// the AVX2 path. It is tracked here because that dispatch is invisible
        /// otherwise: it happens inside the crate, is not implied by any of the
        /// flags above, and produced a 1.65x apparent difference between the two
        /// platforms that had nothing to do with either kernel.
        const AVX512IFMA = 1 << 4;
        /// AVX-512VL, the 128/256-bit encodings of the AVX-512 instructions.
        ///
        /// `curve25519-dalek`'s IFMA backend needs this as well as
        /// [`Self::AVX512IFMA`], so both are reported.
        const AVX512VL = 1 << 5;
    }
}

/// The wire layout gives each feature set eight bits; see
/// [`CpuFeatures::to_wire`].
const _: () = assert!(FeatureSet::all().bits() <= 0xFF);

impl FeatureSet {
    /// The AVX-512 flags, whose register state the Restricted Kernel does not
    /// enable.
    const AVX512: Self = Self::AVX512IFMA.union(Self::AVX512VL);

    /// The set of features statically enabled for this build.
    pub const fn compiled() -> Self {
        let mut set = Self::empty();
        if cfg!(target_feature = "sha") {
            set = set.union(Self::SHA_NI);
        }
        if cfg!(target_feature = "aes") {
            set = set.union(Self::AES_NI);
        }
        if cfg!(target_feature = "pclmulqdq") {
            set = set.union(Self::PCLMULQDQ);
        }
        if cfg!(target_feature = "avx2") {
            set = set.union(Self::AVX2);
        }
        if cfg!(target_feature = "avx512ifma") {
            set = set.union(Self::AVX512IFMA);
        }
        if cfg!(target_feature = "avx512vl") {
            set = set.union(Self::AVX512VL);
        }
        set
    }

    /// The set of features the CPU reports via `CPUID`, gated on the OS
    /// having enabled the state they need.
    ///
    /// See Table 3-8 in
    /// <https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html>
    /// for the bit positions.
    ///
    /// A feature is only usable if the OS enabled its register state in
    /// `XCR0`, which reading would need `unsafe`. The one case where that
    /// differs is handled directly: the Restricted Kernel enables only `X87`,
    /// `SSE` and `AVX` (see `oak_restricted_kernel/src/avx.rs`), so the
    /// AVX-512 bits are masked out in the enclave.
    pub fn available() -> Self {
        // `__cpuid` is a safe intrinsic on x86-64: `CPUID` is unprivileged and
        // unconditionally available, so no target-feature guard is needed.
        // Leaf 1 always exists; leaf 7 only if the maximum basic leaf
        // (returned in EAX by leaf 0) is at least 7, which is checked below.
        use core::arch::x86_64::__cpuid;

        let mut set = Self::empty();

        let leaf1 = __cpuid(1);
        set.set(Self::AES_NI, leaf1.ecx & (1 << 25) != 0);
        set.set(Self::PCLMULQDQ, leaf1.ecx & (1 << 1) != 0);

        let max_leaf = __cpuid(0).eax;
        if max_leaf >= 7 {
            let leaf7 = __cpuid(7);
            set.set(Self::SHA_NI, leaf7.ebx & (1 << 29) != 0);
            set.set(Self::AVX2, leaf7.ebx & (1 << 5) != 0);
            set.set(Self::AVX512IFMA, leaf7.ebx & (1 << 21) != 0);
            set.set(Self::AVX512VL, leaf7.ebx & (1 << 31) != 0);
        }

        if cfg!(target_os = "none") {
            set.remove(Self::AVX512);
        }

        set
    }
}

/// Which instruction-set extensions this binary can actually use.
///
/// `sha2` and `aes` pick a backend through `cpufeatures`, which detects with
/// `CPUID` at runtime. `CPUID` works fine on bare metal, but `cpufeatures`
/// `cfg`s its detection out for `target_os = "none"` and reports every feature
/// absent unless it was statically enabled; see
/// <https://docs.rs/cpufeatures/0.2.17/src/cpufeatures/x86.rs.html>. So the
/// enclave gets compile-time features only while the baseline detects at
/// runtime. Reporting either half alone is misleading, so we report both and
/// [`CpuFeatures::effective`] combines them.
///
/// This cannot see divergence in code that does not dispatch: a crate like
/// `p256` emits whatever the compile-time features permit, so two builds given
/// different `-C target-cpu` can differ while reporting the same bits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CpuFeatures {
    /// Features statically enabled for this build.
    pub compiled: FeatureSet,
    /// Features the CPU reports through `CPUID`, minus any whose register
    /// state the running kernel has not enabled. See [`FeatureSet::available`];
    /// on the enclave this clears the AVX-512 bits.
    pub available: FeatureSet,
    /// Whether the crypto crates can dispatch on `available` at runtime.
    ///
    /// False on bare metal, where `cpufeatures` compiles its detection out.
    pub runtime_dispatch: bool,
}

impl CpuFeatures {
    /// Determine the features for this build and this CPU.
    pub fn detect() -> Self {
        Self {
            compiled: FeatureSet::compiled(),
            available: FeatureSet::available(),
            // Same `cfg` as the AVX-512 masking in `available`, but for an
            // unrelated reason: there, the Restricted Kernel does not enable
            // AVX-512 state; here, `cpufeatures` compiles its detection out.
            runtime_dispatch: !cfg!(target_os = "none"),
        }
    }

    /// The features actually reachable by the crypto backends.
    ///
    /// This is the value to compare across platforms: if two runs report the
    /// same effective set, they used the same implementations.
    pub fn effective(&self) -> FeatureSet {
        if self.runtime_dispatch { self.compiled.union(self.available) } else { self.compiled }
    }

    /// Pack the flags into a bitfield for transport over the wire.
    ///
    /// Layout: bits 0-7 compile-time, bits 8-15 `CPUID`, bit 16 runtime
    /// dispatch. Each set is masked to its byte: `FeatureSet::from_bits_retain`
    /// admits bits outside the declared flags, and one of those would otherwise
    /// land in a neighbouring field.
    pub const fn to_wire(self) -> u32 {
        let mask = FeatureSet::all().bits();
        (self.compiled.bits() & mask)
            | ((self.available.bits() & mask) << 8)
            | ((self.runtime_dispatch as u32) << 16)
    }

    /// Unpack a bitfield produced by [`Self::to_wire`].
    ///
    /// Infallible, unlike the `from_bits` that `bitflags` generates for
    /// [`FeatureSet`]: bits outside the known flags are dropped rather than
    /// rejected, so a result recorded by a newer binary still decodes.
    pub const fn from_wire(bits: u32) -> Self {
        Self {
            compiled: FeatureSet::from_bits_truncate(bits),
            available: FeatureSet::from_bits_truncate(bits >> 8),
            runtime_dispatch: bits & (1 << 16) != 0,
        }
    }
}

/// Write a feature set, or `none` if it is empty.
///
/// `bitflags` writes an empty string for an empty set, and a blank field in a
/// report cannot be told apart from a missing one. Everything else is left to
/// the crate, so a newly added flag cannot go unprinted.
fn write_set(f: &mut fmt::Formatter<'_>, set: FeatureSet) -> fmt::Result {
    if set.is_empty() {
        return f.write_str("none");
    }
    bitflags::parser::to_writer(&set, f)
}

/// `{}` prints the effective feature set, which is the value to compare
/// between two runs. `{:#}` adds the compile-time and `CPUID` sets it was
/// derived from, for logs and methodology notes.
impl fmt::Display for CpuFeatures {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !f.alternate() {
            return write_set(f, self.effective());
        }
        f.write_str("effective=")?;
        write_set(f, self.effective())?;
        f.write_str(" (compiled=")?;
        write_set(f, self.compiled)?;
        f.write_str(", cpuid=")?;
        write_set(f, self.available)?;
        write!(f, ", runtime_dispatch={})", self.runtime_dispatch)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The names travel into reports, so pin them rather than let a rename of
    /// the flag constants change what a recorded run says.
    #[test]
    fn display_lists_the_flag_names() {
        let show = |bits| CpuFeatures::from_wire(bits).to_string();
        assert_eq!(show(0), "none");
        assert_eq!(show(0b1111), "SHA_NI | AES_NI | PCLMULQDQ | AVX2");
        assert_eq!(show(0b1000), "AVX2");
        assert_eq!(show(0b11_0000), "AVX512IFMA | AVX512VL");

        // The alternate form is what the human-readable report prints.
        assert_eq!(
            format!("{:#}", CpuFeatures::from_wire(0b11 | (1 << 16))),
            "effective=SHA_NI | AES_NI (compiled=SHA_NI | AES_NI, cpuid=none, runtime_dispatch=true)"
        );
    }

    /// Without dispatch the `CPUID` half is unreachable and must not appear.
    #[test]
    fn display_hides_undispatchable_features() {
        assert_eq!(CpuFeatures::from_wire(0b11_1111 << 8).to_string(), "none");
    }

    #[test]
    fn bits_round_trip() {
        for compiled in 0..64u32 {
            for available in 0..64u32 {
                for dispatch in [false, true] {
                    let f = CpuFeatures {
                        compiled: FeatureSet::from_bits_truncate(compiled),
                        available: FeatureSet::from_bits_truncate(available),
                        runtime_dispatch: dispatch,
                    };
                    assert_eq!(CpuFeatures::from_wire(f.to_wire()), f);
                }
            }
        }
    }

    #[test]
    fn detect_matches_round_trip() {
        let f = CpuFeatures::detect();
        assert_eq!(CpuFeatures::from_wire(f.to_wire()), f);
    }

    /// The wire layout is duplicated by anything that decodes a recorded
    /// result, so pin it to literals rather than to itself. `bits_round_trip`
    /// would pass with any consistent choice of shifts.
    #[test]
    fn the_wire_layout_is_what_it_says_it_is() {
        let all = FeatureSet::all();
        let none = FeatureSet::empty();

        let compiled = CpuFeatures { compiled: all, available: none, runtime_dispatch: false };
        assert_eq!(compiled.to_wire(), 0b11_1111);

        let available = CpuFeatures { compiled: none, available: all, runtime_dispatch: false };
        assert_eq!(available.to_wire(), 0b11_1111 << 8);

        let dispatch = CpuFeatures { compiled: none, available: none, runtime_dispatch: true };
        assert_eq!(dispatch.to_wire(), 1 << 16);
    }

    /// The host this project targets has several of these extensions. If
    /// `CPUID` reporting were broken, the fairness check built on it would be
    /// worthless, so assert it returns something.
    #[test]
    fn cpuid_reports_something() {
        let available = FeatureSet::available();
        assert!(
            available.intersects(FeatureSet::SHA_NI | FeatureSet::AES_NI | FeatureSet::AVX2),
            "CPUID reported no relevant extensions at all, which is implausible on x86-64"
        );
    }

    #[test]
    fn effective_uses_runtime_features_only_when_dispatch_is_possible() {
        let all = FeatureSet::all();
        let none = FeatureSet::empty();

        let with_dispatch = CpuFeatures { compiled: none, available: all, runtime_dispatch: true };
        assert_eq!(with_dispatch.effective(), all);

        let without_dispatch =
            CpuFeatures { compiled: none, available: all, runtime_dispatch: false };
        assert_eq!(without_dispatch.effective(), none);
    }

    /// On Linux, `std` builds have runtime dispatch; on the enclave they do
    /// not. Guards against the `cfg` being inverted.
    #[test]
    fn runtime_dispatch_is_available_in_this_test_build() {
        assert!(CpuFeatures::detect().runtime_dispatch);
    }

    /// Two flags sharing a bit would be indistinguishable on the wire, so
    /// results recorded before and after a new flag could not be told apart.
    ///
    /// `bitflags` does not check this: it accepts two constants with the same
    /// value without complaint. The listing is spelled out so that a flag added
    /// without a bit of its own fails the comparison against `all`.
    #[test]
    fn every_flag_occupies_a_distinct_bit() {
        let flags = [
            FeatureSet::SHA_NI,
            FeatureSet::AES_NI,
            FeatureSet::PCLMULQDQ,
            FeatureSet::AVX2,
            FeatureSet::AVX512IFMA,
            FeatureSet::AVX512VL,
        ];
        let union = flags.iter().copied().fold(FeatureSet::empty(), FeatureSet::union);

        assert_eq!(union.bits().count_ones() as usize, flags.len());
        assert_eq!(union, FeatureSet::all());

        // The AVX-512 bits were added last, so pin where they landed.
        assert_eq!(FeatureSet::AVX512IFMA.bits(), 1 << 4);
        assert_eq!(FeatureSet::AVX512VL.bits(), 1 << 5);
    }

    /// A `FeatureSet` can carry bits outside the declared flags, because
    /// `bitflags` 2 keeps them in `from_bits_retain` and in the bit operators.
    /// Such a bit must not escape its byte and land in a neighbouring field.
    #[test]
    fn undeclared_bits_do_not_escape_their_field() {
        let noise = FeatureSet::from_bits_retain(!0);
        let none = FeatureSet::empty();

        let compiled = CpuFeatures { compiled: noise, available: none, runtime_dispatch: false };
        assert_eq!(compiled.to_wire(), 0b11_1111);

        let available = CpuFeatures { compiled: none, available: noise, runtime_dispatch: false };
        assert_eq!(available.to_wire(), 0b11_1111 << 8);
    }
}
