/*
  (C) Copyright 2001,2006,
  International Business Machines Corporation,
  Sony Computer Entertainment, Incorporated,
  Toshiba Corporation,

  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright notice,
  this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.
    * Neither the names of the copyright holders nor the names of their
  contributors may be used to endorse or promote products derived from this
  software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
  IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
  PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
  OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
  EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
  PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
  PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
  LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
  SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/
#ifndef _REMQUOF_H_
#define _REMQUOF_H_	1

#include <spu_intrinsics.h>
#include "headers/vec_literal.h"


static __inline float _remquof(float x, float y, int *quo)
{
  int n;
  vec_int4 quotient;
  vec_int4 four = { 4, 4, 4, 4 };
  vec_uint4 vx, vy, z, y2, y4;
  vec_uint4 abs_x, abs_y, abs_2x, abs_8y;
  vec_uint4 exp_x, exp_y;
  vec_uint4 zero_x, zero_y;
  vec_uint4 logb_x, logb_y;
  vec_uint4 mant_x, mant_y;
  vec_uint4 not_ge, overflow, quo_pos;
  vec_uint4 result, result0, resultx, cnt, sign, bias;
  vec_uint4 sign_mask = VEC_SPLAT_U32(0x80000000);
  vec_uint4 implied_1 = VEC_SPLAT_U32(0x00800000);
  vec_uint4 mant_mask = VEC_SPLAT_U32(0x007FFFFF);

  vx = (vec_uint4)spu_promote(x, 0);
  vy = (vec_uint4)spu_promote(y, 0);

  abs_x = spu_andc(vx, sign_mask);
  abs_y = spu_andc(vy, sign_mask);

  abs_8y = spu_add(abs_y, VEC_SPLAT_U32(0x01800000)); /* abs_2y = 8 * abs_y */

  sign = spu_and(vx, sign_mask);

  quo_pos = spu_cmpgt((vec_int4)spu_and(spu_xor(vx, vy), sign_mask), -1);

  /* Compute abs_x = fmodf(abs_x, 8*abs_y). If y is greater than 0.125*SMAX
   * (SMAX is the maximum representable float), then return abs_x.
   */
  {
    /* Determine ilogb of abs_x and abs_8y and
     * extract the mantissas (mant_x, mant_y)
     */
    exp_x  = spu_rlmask(abs_x, -23);
    exp_y  = spu_rlmask(abs_8y, -23);

    resultx = spu_or(spu_cmpgt(abs_8y, abs_x), spu_cmpgt(abs_y, VEC_SPLAT_U32(0x7E7FFFFF)));

    zero_x = spu_cmpeq(exp_x, 0);
    zero_y = spu_cmpeq(exp_y, 0);

    logb_x = spu_add(exp_x, -127);
    logb_y = spu_add(exp_y, -127);

    mant_x = spu_andc(spu_sel(implied_1, abs_x, mant_mask), zero_x);
    mant_y = spu_andc(spu_sel(implied_1, abs_8y, mant_mask), zero_y);

    /* Compute fixed point fmod of mant_x and mant_y. Set the flag,
     * result0, to all ones if we detect that the final result is
     * ever 0.
     */
    result0 = spu_or(zero_x, zero_y);

    n = spu_extract(spu_sub(logb_x, logb_y), 0);


    while (n-- > 0) {
      z = spu_sub(mant_x, mant_y);

      result0 = spu_or(spu_cmpeq(z, 0), result0);

      mant_x = spu_sel(spu_add(mant_x, mant_x), spu_add(z, z),
                       spu_cmpgt((vec_int4)z, -1));
    }

    z = spu_sub(mant_x, mant_y);
    mant_x = spu_sel(mant_x, z, spu_cmpgt((vec_int4)z, -1));

    result0 = spu_or(spu_cmpeq(mant_x, 0), result0);

    /* Convert the result back to floating point and restore
     * the sign. If we flagged the result to be zero (result0),
     * zero it. If we flagged the result to equal its input x,
     * (resultx) then return x.
     */
    cnt = spu_add(spu_cntlz(mant_x), -8);

    mant_x = spu_rl(spu_andc(mant_x, implied_1), (vec_int4)cnt);

    exp_y = spu_sub(exp_y, cnt);
    result0 = spu_orc(result0, spu_cmpgt((vec_int4)exp_y, 0)); /* zero denorm results */
    exp_y = spu_rl(exp_y, 23);

    result = spu_sel(exp_y, mant_x, mant_mask);
    abs_x = spu_sel(spu_andc(result, spu_rlmask(result0, -1)), abs_x, resultx);
  }

  /* if (x >= 4*y)
   *   x -= 4*y
   *   quotient = 4
   * else
   *   quotient = 0
   */
  y4 = spu_andc(spu_add(abs_y, VEC_SPLAT_U32(0x01000000)), zero_y);

  overflow = spu_cmpgt(abs_y, VEC_SPLAT_U32(0x7EFFFFFF));
  not_ge = spu_or(spu_cmpgt(y4, abs_x), overflow);

  abs_x = spu_sel((vec_uint4)spu_sub((vec_float4)abs_x, (vec_float4)y4), abs_x, not_ge);
  quotient = spu_andc (four, (vec_int4)not_ge);

  /* if (x >= 2*y
   *   x -= 2*y
   *   quotient += 2
   */
  y2 = spu_andc(spu_add(abs_y, implied_1), zero_y);
  not_ge = spu_cmpgt(y2, abs_x);

  abs_x = spu_sel((vec_uint4)spu_sub((vec_float4)abs_x, (vec_float4)y2), abs_x, not_ge);
  quotient = spu_sel(spu_add(quotient, 2), quotient, not_ge);

  /* if (2*x > y)
   *     x -= y
   *     if (2*x >= y) x -= y
   */
  abs_2x = spu_add(abs_x, implied_1);
  bias = spu_cmpgt(abs_2x, abs_y);
  abs_x = spu_sel(abs_x, (vec_uint4)spu_sub((vec_float4)abs_x, (vec_float4)abs_y), bias);
  quotient = spu_sub(quotient, (vec_int4)bias);

  bias = spu_andc(bias, spu_rlmaska((vec_uint4)spu_msub((vec_float4)abs_x, VEC_SPLAT_F32(2.0f), (vec_float4)abs_y), -31));
  abs_x = spu_sel(abs_x, (vec_uint4)spu_sub((vec_float4)abs_x, (vec_float4)abs_y), bias);
  quotient = spu_sub(quotient, (vec_int4)bias);

  /* Generate a correct final sign
   */
  result = spu_xor(abs_x, sign);

  quotient = spu_and(quotient, 7);
  quotient = spu_sel(spu_sub(0, quotient), quotient, quo_pos);

  *quo = spu_extract(quotient, 0);

  return (spu_extract((vec_float4)result, 0));
}
#endif /* _REMQUOF_H_ */
