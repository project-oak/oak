// Copyright 2016 - 2018 Ulrik Sverdrup "bluss"
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use crate::kernel::GemmKernel;
use crate::kernel::GemmSelect;
use crate::kernel::{U4, U8};
use crate::archparam;


#[cfg(target_arch="x86")]
use core::arch::x86::*;
#[cfg(target_arch="x86_64")]
use core::arch::x86_64::*;
#[cfg(any(target_arch="x86", target_arch="x86_64"))]
use crate::x86::{FusedMulAdd, AvxMulAdd, SMultiplyAdd};

#[cfg(any(target_arch="x86", target_arch="x86_64"))]
struct KernelAvx;
#[cfg(any(target_arch="x86", target_arch="x86_64"))]
struct KernelFma;
#[cfg(any(target_arch="x86", target_arch="x86_64"))]
struct KernelSse2;
struct KernelFallback;

type T = f32;

/// Detect which implementation to use and select it using the selector's
/// .select(Kernel) method.
///
/// This function is called one or more times during a whole program's
/// execution, it may be called for each gemm kernel invocation or fewer times.
#[inline]
pub(crate) fn detect<G>(selector: G) where G: GemmSelect<T> {
    // dispatch to specific compiled versions
    #[cfg(any(target_arch="x86", target_arch="x86_64"))]
    {
        if is_x86_feature_detected_!("fma") {
            return selector.select(KernelFma);
        } else if is_x86_feature_detected_!("avx") {
            return selector.select(KernelAvx);
        } else if is_x86_feature_detected_!("sse2") {
            return selector.select(KernelSse2);
        }
    }
    return selector.select(KernelFallback);
}

#[cfg(any(target_arch="x86", target_arch="x86_64"))]
macro_rules! loop_m { ($i:ident, $e:expr) => { loop8!($i, $e) }; }
#[cfg(test)]
macro_rules! loop_n { ($j:ident, $e:expr) => { loop8!($j, $e) }; }

#[cfg(any(target_arch="x86", target_arch="x86_64"))]
impl GemmKernel for KernelAvx {
    type Elem = T;

    type MRTy = U8;
    type NRTy = U8;

    #[inline(always)]
    fn align_to() -> usize { 32 }

    #[inline(always)]
    fn always_masked() -> bool { false }

    #[inline(always)]
    fn nc() -> usize { archparam::S_NC }
    #[inline(always)]
    fn kc() -> usize { archparam::S_KC }
    #[inline(always)]
    fn mc() -> usize { archparam::S_MC }

    #[inline(always)]
    unsafe fn kernel(
        k: usize,
        alpha: T,
        a: *const T,
        b: *const T,
        beta: T,
        c: *mut T, rsc: isize, csc: isize) {
        kernel_target_avx(k, alpha, a, b, beta, c, rsc, csc)
    }
}

#[cfg(any(target_arch="x86", target_arch="x86_64"))]
impl GemmKernel for KernelFma {
    type Elem = T;

    type MRTy = <KernelAvx as GemmKernel>::MRTy;
    type NRTy = <KernelAvx as GemmKernel>::NRTy;

    #[inline(always)]
    fn align_to() -> usize { KernelAvx::align_to() }

    #[inline(always)]
    fn always_masked() -> bool { KernelAvx::always_masked() }

    #[inline(always)]
    fn nc() -> usize { archparam::S_NC }
    #[inline(always)]
    fn kc() -> usize { archparam::S_KC }
    #[inline(always)]
    fn mc() -> usize { archparam::S_MC }

    #[inline(always)]
    unsafe fn kernel(
        k: usize,
        alpha: T,
        a: *const T,
        b: *const T,
        beta: T,
        c: *mut T, rsc: isize, csc: isize) {
        kernel_target_fma(k, alpha, a, b, beta, c, rsc, csc)
    }
}

#[cfg(any(target_arch="x86", target_arch="x86_64"))]
impl GemmKernel for KernelSse2 {
    type Elem = T;

    type MRTy = <KernelFallback as GemmKernel>::MRTy;
    type NRTy = <KernelFallback as GemmKernel>::NRTy;

    #[inline(always)]
    fn align_to() -> usize { 16 }

    #[inline(always)]
    fn always_masked() -> bool { KernelFallback::always_masked() }

    #[inline(always)]
    fn nc() -> usize { archparam::S_NC }
    #[inline(always)]
    fn kc() -> usize { archparam::S_KC }
    #[inline(always)]
    fn mc() -> usize { archparam::S_MC }

    #[inline(always)]
    unsafe fn kernel(
        k: usize,
        alpha: T,
        a: *const T,
        b: *const T,
        beta: T,
        c: *mut T, rsc: isize, csc: isize) {
        kernel_target_sse2(k, alpha, a, b, beta, c, rsc, csc)
    }
}

impl GemmKernel for KernelFallback {
    type Elem = T;

    type MRTy = U8;
    type NRTy = U4;

    #[inline(always)]
    fn align_to() -> usize { 0 }

    #[inline(always)]
    fn always_masked() -> bool { true }

    #[inline(always)]
    fn nc() -> usize { archparam::S_NC }
    #[inline(always)]
    fn kc() -> usize { archparam::S_KC }
    #[inline(always)]
    fn mc() -> usize { archparam::S_MC }

    #[inline(always)]
    unsafe fn kernel(
        k: usize,
        alpha: T,
        a: *const T,
        b: *const T,
        beta: T,
        c: *mut T, rsc: isize, csc: isize) {
        kernel_fallback_impl(k, alpha, a, b, beta, c, rsc, csc)
    }
}

// no inline for unmasked kernels
#[cfg(any(target_arch="x86", target_arch="x86_64"))]
#[target_feature(enable="fma")]
unsafe fn kernel_target_fma(k: usize, alpha: T, a: *const T, b: *const T,
                            beta: T, c: *mut T, rsc: isize, csc: isize)
{
    kernel_x86_avx::<FusedMulAdd>(k, alpha, a, b, beta, c, rsc, csc)
}

// no inline for unmasked kernels
#[cfg(any(target_arch="x86", target_arch="x86_64"))]
#[target_feature(enable="avx")]
unsafe fn kernel_target_avx(k: usize, alpha: T, a: *const T, b: *const T,
                            beta: T, c: *mut T, rsc: isize, csc: isize)
{
    kernel_x86_avx::<AvxMulAdd>(k, alpha, a, b, beta, c, rsc, csc)
}

#[inline]
#[cfg(any(target_arch="x86", target_arch="x86_64"))]
#[target_feature(enable="sse2")]
unsafe fn kernel_target_sse2(k: usize, alpha: T, a: *const T, b: *const T,
                             beta: T, c: *mut T, rsc: isize, csc: isize)
{
    kernel_fallback_impl(k, alpha, a, b, beta, c, rsc, csc)
}

#[inline(always)]
#[cfg(any(target_arch="x86", target_arch="x86_64"))]
unsafe fn kernel_x86_avx<MA>(k: usize, alpha: T, a: *const T, b: *const T,
                             beta: T, c: *mut T, rsc: isize, csc: isize)
    where MA: SMultiplyAdd,
{
    const MR: usize = KernelAvx::MR;
    const NR: usize = KernelAvx::NR;

    debug_assert_ne!(k, 0);

    let mut ab = [_mm256_setzero_ps(); MR];

    // this kernel can operate in either transposition (C = A B or C^T = B^T A^T)
    let prefer_row_major_c = rsc != 1;

    let (mut a, mut b) = if prefer_row_major_c { (a, b) } else { (b, a) };
    let (rsc, csc) = if prefer_row_major_c { (rsc, csc) } else { (csc, rsc) };

    macro_rules! shuffle_mask {
        ($z:expr, $y:expr, $x:expr, $w:expr) => {
            ($z << 6) | ($y << 4) | ($x << 2) | $w
        }
    }
    macro_rules! permute_mask {
        ($z:expr, $y:expr, $x:expr, $w:expr) => {
            ($z << 6) | ($y << 4) | ($x << 2) | $w
        }
    }

    macro_rules! permute2f128_mask {
        ($y:expr, $x:expr) => {
            (($y << 4) | $x)
        }
    }

    // Start data load before each iteration
    let mut av = _mm256_load_ps(a);
    let mut bv = _mm256_load_ps(b);

    // Compute A B
    unroll_by_with_last!(4 => k, is_last, {
        // We compute abij = ai bj
        //
        // Load b as one contiguous vector
        // Load a as striped vectors
        //
        // Shuffle the abij elements in order after the loop.
        //
        // Note this scheme copied and transposed from the BLIS 8x8 sgemm
        // microkernel.
        //
        // Our a indices are striped and our b indices are linear. In
        // the variable names below, we always have doubled indices so
        // for example a0246 corresponds to a vector of a0 a0 a2 a2 a4 a4 a6 a6.
        //
        // ab0246: ab2064: ab4602: ab6420:
        // ( ab00  ( ab20  ( ab40  ( ab60
        //   ab01    ab21    ab41    ab61
        //   ab22    ab02    ab62    ab42
        //   ab23    ab03    ab63    ab43
        //   ab44    ab64    ab04    ab24
        //   ab45    ab65    ab05    ab25
        //   ab66    ab46    ab26    ab06
        //   ab67 )  ab47 )  ab27 )  ab07 )
        //
        // ab1357: ab3175: ab5713: ab7531:
        // ( ab10  ( ab30  ( ab50  ( ab70
        //   ab11    ab31    ab51    ab71
        //   ab32    ab12    ab72    ab52
        //   ab33    ab13    ab73    ab53
        //   ab54    ab74    ab14    ab34
        //   ab55    ab75    ab15    ab35
        //   ab76    ab56    ab36    ab16
        //   ab77 )  ab57 )  ab37 )  ab17 )

        const PERM32_2301: i32 = permute_mask!(1, 0, 3, 2);
        const PERM128_30: i32 = permute2f128_mask!(0, 3);

        // _mm256_moveldup_ps(av):
        // vmovsldup ymm2, ymmword ptr [rax]
        //
        // Load and duplicate each even word:
        // ymm2 ← [a0 a0 a2 a2 a4 a4 a6 a6]
        //
        // _mm256_movehdup_ps(av):
        // vmovshdup ymm2, ymmword ptr [rax]
        //
        // Load and duplicate each odd word:
        // ymm2 ← [a1 a1 a3 a3 a5 a5 a7 a7]
        //

        let a0246 = _mm256_moveldup_ps(av); // Load: a0 a0 a2 a2 a4 a4 a6 a6
        let a2064 = _mm256_permute_ps(a0246, PERM32_2301);

        let a1357 = _mm256_movehdup_ps(av); // Load: a1 a1 a3 a3 a5 a5 a7 a7
        let a3175 = _mm256_permute_ps(a1357, PERM32_2301);

        let a4602 = _mm256_permute2f128_ps(a0246, a0246, PERM128_30);
        let a6420 = _mm256_permute2f128_ps(a2064, a2064, PERM128_30);

        let a5713 = _mm256_permute2f128_ps(a1357, a1357, PERM128_30);
        let a7531 = _mm256_permute2f128_ps(a3175, a3175, PERM128_30);

        ab[0] = MA::multiply_add(a0246, bv, ab[0]);
        ab[1] = MA::multiply_add(a2064, bv, ab[1]);
        ab[2] = MA::multiply_add(a4602, bv, ab[2]);
        ab[3] = MA::multiply_add(a6420, bv, ab[3]);

        ab[4] = MA::multiply_add(a1357, bv, ab[4]);
        ab[5] = MA::multiply_add(a3175, bv, ab[5]);
        ab[6] = MA::multiply_add(a5713, bv, ab[6]);
        ab[7] = MA::multiply_add(a7531, bv, ab[7]);

        if !is_last {
            a = a.add(MR);
            b = b.add(NR);

            bv = _mm256_load_ps(b);
            av = _mm256_load_ps(a);
        }
    });

    let alphav = _mm256_set1_ps(alpha);

    // Permute to put the abij elements in order
    //
    // shufps 0xe4: 22006644 00224466 -> 22226666
    //
    // vperm2 0x30: 00004444 44440000 -> 00000000
    // vperm2 0x12: 00004444 44440000 -> 44444444
    //
    
    let ab0246 = ab[0];
    let ab2064 = ab[1];
    let ab4602 = ab[2];
    let ab6420 = ab[3];

    let ab1357 = ab[4];
    let ab3175 = ab[5];
    let ab5713 = ab[6];
    let ab7531 = ab[7];

    const SHUF_0123: i32 = shuffle_mask!(3, 2, 1, 0);
    debug_assert_eq!(SHUF_0123, 0xE4);

    const PERM128_03: i32 = permute2f128_mask!(3, 0);
    const PERM128_21: i32 = permute2f128_mask!(1, 2);

    // No elements are "shuffled" in truth, they all stay at their index
    // but we combine vectors to de-stripe them.
    //
    // For example, the first shuffle below uses 0 1 2 3 which
    // corresponds to the X0 X1 Y2 Y3 sequence etc:
    //
    //                                             variable
    // X ab00 ab01 ab22 ab23 ab44 ab45 ab66 ab67   ab0246
    // Y ab20 ab21 ab02 ab03 ab64 ab65 ab46 ab47   ab2064
    // 
    //   X0   X1   Y2   Y3   X4   X5   Y6   Y7
    // = ab00 ab01 ab02 ab03 ab44 ab45 ab46 ab47   ab0044

    let ab0044 = _mm256_shuffle_ps(ab0246, ab2064, SHUF_0123);
    let ab2266 = _mm256_shuffle_ps(ab2064, ab0246, SHUF_0123);

    let ab4400 = _mm256_shuffle_ps(ab4602, ab6420, SHUF_0123);
    let ab6622 = _mm256_shuffle_ps(ab6420, ab4602, SHUF_0123);

    let ab1155 = _mm256_shuffle_ps(ab1357, ab3175, SHUF_0123);
    let ab3377 = _mm256_shuffle_ps(ab3175, ab1357, SHUF_0123);

    let ab5511 = _mm256_shuffle_ps(ab5713, ab7531, SHUF_0123);
    let ab7733 = _mm256_shuffle_ps(ab7531, ab5713, SHUF_0123);

    let ab0000 = _mm256_permute2f128_ps(ab0044, ab4400, PERM128_03);
    let ab4444 = _mm256_permute2f128_ps(ab0044, ab4400, PERM128_21);

    let ab2222 = _mm256_permute2f128_ps(ab2266, ab6622, PERM128_03);
    let ab6666 = _mm256_permute2f128_ps(ab2266, ab6622, PERM128_21);

    let ab1111 = _mm256_permute2f128_ps(ab1155, ab5511, PERM128_03);
    let ab5555 = _mm256_permute2f128_ps(ab1155, ab5511, PERM128_21);

    let ab3333 = _mm256_permute2f128_ps(ab3377, ab7733, PERM128_03);
    let ab7777 = _mm256_permute2f128_ps(ab3377, ab7733, PERM128_21);

    ab[0] = ab0000;
    ab[1] = ab1111;
    ab[2] = ab2222;
    ab[3] = ab3333;
    ab[4] = ab4444;
    ab[5] = ab5555;
    ab[6] = ab6666;
    ab[7] = ab7777;

    // Compute α (A B)
    // Compute here if we don't have fma, else pick up α further down
    if !MA::IS_FUSED {
        loop_m!(i, ab[i] = _mm256_mul_ps(alphav, ab[i]));
    }

    macro_rules! c {
        ($i:expr, $j:expr) => (c.offset(rsc * $i as isize + csc * $j as isize));
    }

    // C ← α A B + β C
    let mut cv = [_mm256_setzero_ps(); MR];
    if beta != 0. {
        let betav = _mm256_set1_ps(beta);
        // Read C
        if csc == 1 {
            loop_m!(i, cv[i] = _mm256_loadu_ps(c![i, 0]));
        } else {
            loop_m!(i, cv[i] = _mm256_setr_ps(*c![i, 0], *c![i, 1], *c![i, 2], *c![i, 3],
                                              *c![i, 4], *c![i, 5], *c![i, 6], *c![i, 7]));
        }
        // Compute β C
        loop_m!(i, cv[i] = _mm256_mul_ps(cv[i], betav));
    }

    // Compute (α A B) + (β C)
    if !MA::IS_FUSED {
        loop_m!(i, cv[i] = _mm256_add_ps(cv[i], ab[i]));
    } else {
        loop_m!(i, cv[i] = MA::multiply_add(alphav, ab[i], cv[i]));
    }

    // Store C back to memory
    if csc == 1 {
        loop_m!(i, _mm256_storeu_ps(c![i, 0], cv[i]));
    } else {
        // Permute to bring each element in the vector to the front and store
        loop_m!(i, {
            let cvlo = _mm256_extractf128_ps(cv[i], 0);
            let cvhi = _mm256_extractf128_ps(cv[i], 1);

            _mm_store_ss(c![i, 0], cvlo);
            let cperm = _mm_permute_ps(cvlo, permute_mask!(0, 3, 2, 1));
            _mm_store_ss(c![i, 1], cperm);
            let cperm = _mm_permute_ps(cperm, permute_mask!(0, 3, 2, 1));
            _mm_store_ss(c![i, 2], cperm);
            let cperm = _mm_permute_ps(cperm, permute_mask!(0, 3, 2, 1));
            _mm_store_ss(c![i, 3], cperm);

            _mm_store_ss(c![i, 4], cvhi);
            let cperm = _mm_permute_ps(cvhi, permute_mask!(0, 3, 2, 1));
            _mm_store_ss(c![i, 5], cperm);
            let cperm = _mm_permute_ps(cperm, permute_mask!(0, 3, 2, 1));
            _mm_store_ss(c![i, 6], cperm);
            let cperm = _mm_permute_ps(cperm, permute_mask!(0, 3, 2, 1));
            _mm_store_ss(c![i, 7], cperm);
        });
    }
}

#[inline]
unsafe fn kernel_fallback_impl(k: usize, alpha: T, a: *const T, b: *const T,
                               beta: T, c: *mut T, rsc: isize, csc: isize)
{
    const MR: usize = KernelFallback::MR;
    const NR: usize = KernelFallback::NR;
    let mut ab: [[T; NR]; MR] = [[0.; NR]; MR];
    let mut a = a;
    let mut b = b;
    debug_assert_eq!(beta, 0., "Beta must be 0 or is not masked");

    // Compute A B into ab[i][j]
    unroll_by!(4 => k, {
        loop8!(i, loop4!(j, ab[i][j] += at(a, i) * at(b, j)));

        a = a.offset(MR as isize);
        b = b.offset(NR as isize);
    });

    macro_rules! c {
        ($i:expr, $j:expr) => (c.offset(rsc * $i as isize + csc * $j as isize));
    }

    // set C = α A B
    loop4!(j, loop8!(i, *c![i, j] = alpha * ab[i][j]));
}

#[inline(always)]
unsafe fn at(ptr: *const T, i: usize) -> T {
    *ptr.offset(i as isize)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::vec;
    use crate::aligned_alloc::Alloc;

    fn aligned_alloc<K>(elt: K::Elem, n: usize) -> Alloc<K::Elem>
        where K: GemmKernel,
              K::Elem: Copy,
    {
        unsafe {
            Alloc::new(n, K::align_to()).init_with(elt)
        }
    }

    use super::T;

    fn test_a_kernel<K: GemmKernel<Elem=T>>(_name: &str) {
        const K: usize = 4;
        let mr = K::MR;
        let nr = K::NR;
        let mut a = aligned_alloc::<K>(1., mr * K);
        let mut b = aligned_alloc::<K>(0., nr * K);
        for (i, x) in a.iter_mut().enumerate() {
            *x = i as _;
        }

        for i in 0..K {
            b[i + i * nr] = 1.;
        }
        let mut c = vec![0.; mr * nr];
        unsafe {
            K::kernel(K, 1., &a[0], &b[0], 0., &mut c[0], 1, mr as isize);
            // col major C
        }
        assert_eq!(&a[..], &c[..a.len()]);
    }

    #[test]
    fn test_kernel_fallback_impl() {
        test_a_kernel::<KernelFallback>("kernel");
    }

    #[cfg(any(target_arch="x86", target_arch="x86_64"))]
    #[test]
    fn test_loop_m_n() {
        let mut m = [[0; KernelAvx::NR]; KernelAvx::MR];
        loop_m!(i, loop_n!(j, m[i][j] += 1));
        for arr in &m[..] {
            for elt in &arr[..] {
                assert_eq!(*elt, 1);
            }
        }
    }

    #[cfg(any(target_arch="x86", target_arch="x86_64"))]
    mod test_arch_kernels {
        use super::test_a_kernel;
        use super::super::*;
        #[cfg(features = "std")]
        use std::println;
        macro_rules! test_arch_kernels_x86 {
            ($($feature_name:tt, $name:ident, $kernel_ty:ty),*) => {
                $(
                #[test]
                fn $name() {
                    if is_x86_feature_detected_!($feature_name) {
                        test_a_kernel::<$kernel_ty>(stringify!($name));
                    } else {
                        #[cfg(features = "std")]
                        println!("Skipping, host does not have feature: {:?}", $feature_name);
                    }
                }
                )*
            }
        }

        test_arch_kernels_x86! {
            "fma", fma, KernelFma,
            "avx", avx, KernelAvx,
            "sse2", sse2, KernelSse2
        }

        #[test]
        fn ensure_target_features_tested() {
            // If enabled, this test ensures that the requested feature actually
            // was enabled on this configuration, so that it was tested.
            let should_ensure_feature = !option_env!("MMTEST_ENSUREFEATURE")
                                                    .unwrap_or("").is_empty();
            if !should_ensure_feature {
                // skip
                return;
            }
            let feature_name = option_env!("MMTEST_FEATURE")
                                          .expect("No MMTEST_FEATURE configured!");
            let detected = match feature_name {
                "avx" => is_x86_feature_detected_!("avx"),
                "fma" => is_x86_feature_detected_!("fma"),
                "sse2" => is_x86_feature_detected_!("sse2"),
                _ => false,
            };
            assert!(detected, "Feature {:?} was not detected, so it could not be tested",
                    feature_name);
        }
    }
}
