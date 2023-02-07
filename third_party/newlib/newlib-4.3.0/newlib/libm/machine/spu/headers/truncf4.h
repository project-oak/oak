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
#ifndef _TRUNCF4_H_
#define _TRUNCF4_H_	1
    
#include <spu_intrinsics.h>
    
/*
 * FUNCTION
 *      vector float _truncf4(vector float x)
 *
 * DESCRIPTION
 *      The _truncf4 function truncates the elements of the input vector
 *      downwards (towards zero) to the nearest integer.
 *
 */
static __inline vector float _truncf4(vector float x) 
{
  vec_int4 exp;
  vec_uint4 or_mask, and_mask, mask;
  vec_float4 out;
    
  // Construct a mask to remove the fraction bits. The mask
  // depends on the exponent of the floating point
  // input value.
  exp = spu_sub(127, spu_and(spu_rlmask((vec_int4) x, -23), 0xFF));

  // Be sure to always preserve the sign bit
  or_mask = spu_rlmask(spu_cmpgt(exp, 0),-1);

  and_mask = spu_rlmask(spu_splats((unsigned int)0x7FFFFF), exp);
  mask = spu_or(spu_and(and_mask, spu_cmpgt(exp, -31)), or_mask);
    
  // Apply the mask and return the result.
    
  out = spu_andc(x, (vec_float4) (mask));
  return (out);
}
#endif /* _TRUNCF4_H_ */
#endif /* __SPU__ */
