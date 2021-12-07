// Copyright 2016 - 2018 Ulrik Sverdrup "bluss"
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use core::ops::{AddAssign, MulAssign};

/// General matrix multiply kernel
pub trait GemmKernel {
    type Elem: Element;

    /// Kernel rows
    const MR: usize = Self::MRTy::VALUE;
    /// Kernel cols
    const NR: usize = Self::NRTy::VALUE;
    /// Kernel rows as const num type
    type MRTy: ConstNum;
    /// Kernel cols as const num type
    type NRTy: ConstNum;

    /// align inputs to this
    fn align_to() -> usize;

    /// Whether to always use the masked wrapper around the kernel.
    fn always_masked() -> bool;

    fn nc() -> usize;
    fn kc() -> usize;
    fn mc() -> usize;

    /// Matrix multiplication kernel
    ///
    /// This does the matrix multiplication:
    ///
    /// C ← α A B + β C
    ///
    /// + `k`: length of data in a, b
    /// + a, b are packed
    /// + c has general strides
    /// + rsc: row stride of c
    /// + csc: col stride of c
    /// + `alpha`: scaling factor for A B product
    /// + `beta`: scaling factor for c.
    ///   Note: if `beta` is `0.`, the kernel should not (and must not)
    ///   read from c, its value is to be treated as if it was zero.
    ///
    /// When masked, the kernel is always called with β=0 but α is passed
    /// as usual. (This is only useful information if you return `true` from
    /// `always_masked`.)
    unsafe fn kernel(
        k: usize,
        alpha: Self::Elem,
        a: *const Self::Elem,
        b: *const Self::Elem,
        beta: Self::Elem,
        c: *mut Self::Elem, rsc: isize, csc: isize);
}

pub trait Element : Copy + AddAssign + MulAssign + Send + Sync {
    fn zero() -> Self;
    fn one() -> Self;
    fn is_zero(&self) -> bool;
}

impl Element for f32 {
    fn zero() -> Self { 0. }
    fn one() -> Self { 1. }
    fn is_zero(&self) -> bool { *self == 0. }
}

impl Element for f64 {
    fn zero() -> Self { 0. }
    fn one() -> Self { 1. }
    fn is_zero(&self) -> bool { *self == 0. }
}

/// Kernel selector
pub(crate) trait GemmSelect<T> {
    /// Call `select` with the selected kernel for this configuration
    fn select<K>(self, kernel: K)
        where K: GemmKernel<Elem=T>,
              T: Element;
}


pub trait ConstNum {
    const VALUE: usize;
}

pub struct U4;
pub struct U8;

impl ConstNum for U4 { const VALUE: usize = 4; }
impl ConstNum for U8 { const VALUE: usize = 8; }
