/* --------------------------------------------------------------  */
/* (C)Copyright 2001,2008,                                         */
/* International Business Machines Corporation,                    */
/* Sony Computer Entertainment, Incorporated,                      */
/* Toshiba Corporation,                                            */
/*                                                                 */
/* All Rights Reserved.                                            */
/*                                                                 */
/* Redistribution and use in source and binary forms, with or      */
/* without modification, are permitted provided that the           */
/* following conditions are met:                                   */
/*                                                                 */
/* - Redistributions of source code must retain the above copyright*/
/*   notice, this list of conditions and the following disclaimer. */
/*                                                                 */
/* - Redistributions in binary form must reproduce the above       */
/*   copyright notice, this list of conditions and the following   */
/*   disclaimer in the documentation and/or other materials        */
/*   provided with the distribution.                               */
/*                                                                 */
/* - Neither the name of IBM Corporation nor the names of its      */
/*   contributors may be used to endorse or promote products       */
/*   derived from this software without specific prior written     */
/*   permission.                                                   */
/*                                                                 */
/* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND          */
/* CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,     */
/* INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF        */
/* MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE        */
/* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR            */
/* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,    */
/* SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT    */
/* NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;    */
/* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)        */
/* HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN       */
/* CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR    */
/* OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,  */
/* EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.              */
/* --------------------------------------------------------------  */
/* PROLOG END TAG zYx                                              */
#ifdef __SPU__
#ifndef _EXPD2_H_
#define _EXPD2_H_	1

#include <spu_intrinsics.h>
#include "floord2.h"

#define LOG2E 1.4426950408889634073599     // 1/log(2) 

/*
 * FUNCTION
 *	vector double _expd2(vector double x)
 *
 * DESCRIPTION
 *	_expd2 computes e raised to the input x for
 *	each of the element of the double word vector.
 *
 * Calculation is performed by reducing the input argument
 * to within a managable range, and then computing the power
 * series to the 11th degree.
 *
 * Range reduction is performed using the property:
 *
 *	exp(x) = 2^n * exp(r)
 *
 * Values for "n" and "r" are determined such that:
 *
 *       x = n * ln(2) + r, |r| <= ln(2)/2
 *
 *       n = floor(  (x/ln(2)) + 1/2  )
 *       r = x - (n * ln(2))
 *
 * To enhance the precision for "r", computation is performed
 * using a two part representation of ln(2). 
 *
 * Once the input is reduced, the power series is computed:
 *
 *                    __12_
 *                    \
 *       exp(x) = 1 +  \   (x^i)/i!
 *                     /
 *                    /____
 *                     i=2
 *
 * The resulting value is scaled by 2^n and returned.
 *
 */	      

static __inline vector double _expd2(vector double x)
{
  //  log(2) in extended machine representable precision
  vec_double2 ln2_hi = spu_splats(6.9314575195312500E-1);  // 3FE62E4000000000
  vec_double2 ln2_lo = spu_splats(1.4286068203094172E-6);  // 3EB7F7D1CF79ABCA

  //  coefficients for the power series
  // vec_double2 f01 = spu_splats(1.00000000000000000000E0);  // 1/(1!)
  vec_double2 f02 = spu_splats(5.00000000000000000000E-1); // 1/(2!)
  vec_double2 f03 = spu_splats(1.66666666666666666667E-1); // 1/(3!)
  vec_double2 f04 = spu_splats(4.16666666666666666667E-2); // 1/(4!)
  vec_double2 f05 = spu_splats(8.33333333333333333333E-3); // 1/(5!)
  vec_double2 f06 = spu_splats(1.38888888888888888889E-3); // 1/(6!)
  vec_double2 f07 = spu_splats(1.98412698412698412698E-4); // 1/(7!)
  vec_double2 f08 = spu_splats(2.48015873015873015873E-5); // 1/(8!)
  vec_double2 f09 = spu_splats(2.75573192239858906526E-6); // 1/(9!)
  vec_double2 f10 = spu_splats(2.75573192239858906526E-7); // 1/(10!)
  vec_double2 f11 = spu_splats(2.50521083854417187751E-8); // 1/(11!)
  vec_double2 f12 = spu_splats(2.08767569878680989792E-9); // 1/(12!)

  //  rx = floor(1/2 + x/log(2))  
  vec_double2 rx = _floord2(spu_madd(x,spu_splats(LOG2E),spu_splats(0.5)));

  // extract the exponent of reduction
  vec_int4 exp = spu_convts(spu_roundtf(rx),0);

  // reduce the input to within [ -ln(2)/2 ... ln(2)/2 ]
  vec_double2 r;
  r = spu_nmsub(rx,ln2_hi,x);
  r = spu_nmsub(rx,ln2_lo,r);

  vec_double2 result;
  vec_double2 r2 = spu_mul(r,r);

  //  Use Horner's method on the power series
  /*  result = ((((c12*x + c11)*x + c10)*x + c9)*x + c8)*x + c7)*x + c6)*x^6 +
              ((((((c5*x + c4)*x + c3)*x + c2)*x + c1)*x + c0
  */

#ifdef __SPU_EDP__
  vec_double2 p1, p2, r4, r6;

  p1 = spu_madd(f12, r, f11);
  p2 = spu_madd(f05, r, f04);
  r4 = spu_mul(r2, r2);
  p1 = spu_madd(p1, r, f10);
  p2 = spu_madd(p2, r, f03);
  p1 = spu_madd(p1, r, f09);
  p2 = spu_madd(p2, r, f02);
  p1 = spu_madd(p1, r, f08);
  r6 = spu_mul(r2, r4);
  p1 = spu_madd(p1, r, f07);
  p2 = spu_madd(p2, r2, r);
  p1 = spu_madd(p1, r, f06);

  result = spu_madd(r6, p1, p2);
  result = spu_add(result, spu_splats(1.0));

#else

  result = spu_madd(r,f12,f11);
  result = spu_madd(result,r,f10);
  result = spu_madd(result,r,f09);
  result = spu_madd(result,r,f08);
  result = spu_madd(result,r,f07);
  result = spu_madd(result,r,f06);
  result = spu_madd(result,r,f05);
  result = spu_madd(result,r,f04);
  result = spu_madd(result,r,f03);
  result = spu_madd(result,r,f02);
  result = spu_madd(result,r2,r);
  result = spu_add(result,spu_splats(1.0));

#endif  /* __SPU_EDP__ */


  //  Scale the result - basically a call to ldexpd2()
  vec_int4 e1, e2;
  vec_int4 min = spu_splats(-2044);
  vec_int4 max = spu_splats(2046);
  vec_uint4 cmp_min, cmp_max;
  vec_uint4 shift = (vec_uint4) { 20, 32, 20, 32 };
  vec_double2 f1, f2;

  /* Clamp the specified exponent to the range -2044 to 2046.
   */
  cmp_min = spu_cmpgt(exp, min);
  cmp_max = spu_cmpgt(exp, max);
  exp = spu_sel(min, exp, cmp_min);
  exp = spu_sel(exp, max, cmp_max);

  /* Generate the factors f1 = 2^e1 and f2 = 2^e2
   */
  e1 = spu_rlmaska(exp, -1);
  e2 = spu_sub(exp, e1);

  f1 = (vec_double2)spu_sl(spu_add(e1, 1023), shift);
  f2 = (vec_double2)spu_sl(spu_add(e2, 1023), shift);

  /* Compute the product x * 2^e1 * 2^e2
   */
  result = spu_mul(spu_mul(result, f1), f2);

  return result;
}

#endif /* _EXPD2_H_ */
#endif /* __SPU__ */
