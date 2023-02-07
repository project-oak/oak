/* --------------------------------------------------------------  */
/* (C)Copyright 2006,2008,                                         */
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
#ifndef _SCALBNF4_H_
#define _SCALBNF4_H_	1

#include <spu_intrinsics.h>

/*
 * FUNCTION
 *	vector float _scalbnf4(vector float x, vector signed int exp)
 *
 * DESCRIPTION
 *      The _scalbnf4 function returns a vector containing each element of x 
 *      multiplied by 2^n computed efficiently.  This function is computed 
 *      without the assistance of any floating point operations and as such 
 *      does not set any floating point exceptions.
 *
 *      Special Cases:
 *	  - if the exponent is 0, then x is either 0 or a subnormal, and the
 *          result will be returned as 0.
 *        - if the result if underflows, it will be returned as 0.
 *        - if the result overflows, it will be returned as FLT_MAX.
 *
 */
static __inline vector float _scalbnf4(vector float x, vector signed int exp)
{
  vec_int4 x_exp;
  vec_uint4 zero;
  vec_uint4 overflow;
  vec_uint4 exp_mask = (vec_uint4)spu_splats(0x7F800000);
  vec_float4 out;

  /* Extract exponent from x. If the exponent is 0, then
   * x is either 0 or a denorm and x*2^exp is a zero.
   */
  x_exp = spu_and(spu_rlmask((vec_int4)x, -23), 0xFF);
  zero = spu_cmpeq(x_exp, 0);

  /* Compute the expected exponent and determine if the 
   * result is within range.
   */
  x_exp = spu_add(exp, x_exp);

  /* Check for zero or overflow of result.
   * Note: set high bit of flags = 0, since we have to
   * return -0 when x = -0
   */
  zero     = spu_rlmask(spu_orc(zero, spu_cmpgt(x_exp, 0)), -1);
  overflow = spu_rlmask(spu_cmpgt(x_exp, 255), -1);

  /* Merge the expect exponent with x's mantissa. Zero the
   * result if underflow and force to max if overflow.
   */
  out = spu_sel(x, (vec_float4)spu_rl(x_exp, 23), exp_mask);
  out = spu_andc(out, (vec_float4)zero);
  out = spu_or(out, (vec_float4)overflow);

  return out;
}

#endif /* _SCALBNF4_H_ */
#endif /* __SPU__ */
