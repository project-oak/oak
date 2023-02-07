/* --------------------------------------------------------------  */
/* (C)Copyright 2007,2008,                                         */
/* International Business Machines Corporation                     */
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
#ifndef _ASINHF4_H_
#define _ASINHF4_H_	1

#include <spu_intrinsics.h>

#include "logf4.h"
#include "sqrtf4.h"

/*
 * FUNCTION
 *  vector float _asinhf4(vector float x)
 *
 * DESCRIPTION
 *  The asinhf4 function returns a vector containing the hyperbolic
 *  arcsines of the corresponding elements of the input vector.
 *
 *  We are using the formula:
 *    asinh = ln(|x| + sqrt(x^2 + 1))
 *  and the anti-symmetry of asinh.
 *
 *  For x near zero, we use the Taylor series:
 *
 *                infinity
 *                 ------
 *                  -   '  P  (0)
 *                   -      k-1    k
 *    asinh x =       -    -----  x
 *                   -       k
 *                  -   ,
 *                 ------
 *                 k = 1
 *
 *  Special Cases:
 *   - asinh(+0)        returns +0
 *   - asinh(-0)        returns -0
 *   - Normally,  asinh(+/- infinity) returns +/- infinity,
 *	   but on the SPU, single-precision infinity is not supported,
 *	   so it is treated as a normal number here.
 *
 */

/*
 * Maclaurin Series Coefficients 
 * for x near 0.
 */
#define ASINH_MAC01     1.0000000000000000000000000000000000000000000000000000000000000000000000E0
#define ASINH_MAC03     -1.6666666666666666666666666666666666666666666666666666666666666666666667E-1
#define ASINH_MAC05     7.5000000000000000000000000000000000000000000000000000000000000000000000E-2
#define ASINH_MAC07     -4.4642857142857142857142857142857142857142857142857142857142857142857143E-2
#define ASINH_MAC09     3.0381944444444444444444444444444444444444444444444444444444444444444444E-2
#define ASINH_MAC11     -2.2372159090909090909090909090909090909090909090909090909090909090909091E-2
#define ASINH_MAC13     1.7352764423076923076923076923076923076923076923076923076923076923076923E-2
#define ASINH_MAC15     -1.3964843750000000000000000000000000000000000000000000000000000000000000E-2
#define ASINH_MAC17     1.1551800896139705882352941176470588235294117647058823529411764705882353E-2
#define ASINH_MAC19     -9.7616095291940789473684210526315789473684210526315789473684210526315789E-3
#define ASINH_MAC21     8.3903358096168154761904761904761904761904761904761904761904761904761905E-3
#define ASINH_MAC23     -7.3125258735988451086956521739130434782608695652173913043478260869565217E-3
#define ASINH_MAC25     6.4472103118896484375000000000000000000000000000000000000000000000000000E-3
#define ASINH_MAC27     -5.7400376708419234664351851851851851851851851851851851851851851851851852E-3
#define ASINH_MAC29     5.1533096823199041958512931034482758620689655172413793103448275862068966E-3
#define ASINH_MAC31     -4.6601434869150961599042338709677419354838709677419354838709677419354839E-3
#if 0
#define ASINH_MAC33     4.2409070936793630773370916193181818181818181818181818181818181818181818E-3
#define ASINH_MAC35     -3.8809645588376692363194056919642857142857142857142857142857142857142857E-3
#define ASINH_MAC37     3.5692053938259345454138678473395270270270270270270270270270270270270270E-3
#define ASINH_MAC39     -3.2970595034734847453924325796274038461538461538461538461538461538461538E-3
#define ASINH_MAC41     3.0578216492580306693548109473251714939024390243902439024390243902439024E-3
#define ASINH_MAC43     -2.8461784011089421678767647854117460029069767441860465116279069767441860E-3
#endif


static __inline vector float _asinhf4(vector float x)
{
    vec_float4 sign_mask = spu_splats(-0.0f);
    vec_float4 onef      = spu_splats(1.0f);
    vec_uint4  oneu      = spu_splats(1u);
    vec_uint4  twou      = spu_splats(2u);
    vec_uint4  threeu    = spu_splats(3u);
    vec_float4 ln2       = spu_splats(6.931471805599453094172321E-1f);
    vec_float4 largef    = spu_splats(9.21e18f);
    vec_float4 result, fresult, mresult;
    vec_float4 xabs, xsqu;
    /* Where we switch from maclaurin to formula */
    vec_float4  switch_approx = spu_splats(0.74f);
    vec_float4  trunc_part2   = spu_splats(20.0f);
    vec_uint4   truncadd;
    vec_uint4   islarge;
    vec_uint4   use_form;

    xabs = spu_andc(x, sign_mask);
    xsqu = spu_mul(x, x);
    islarge = spu_cmpgt(xabs, largef);

    /*
     * Formula:
     *   asinh = ln(|x| + sqrt(x^2 + 1))
     */

    vec_float4 logarg = spu_add(xabs, _sqrtf4(spu_madd(xabs, xabs, onef)));
    logarg = spu_sel(logarg, xabs, islarge);
    fresult = _logf4(logarg);
    fresult = spu_sel(fresult, spu_add(fresult, ln2), islarge);

    /*
     * Maclaurin Series
     */
    mresult = spu_madd(xsqu, spu_splats((float)ASINH_MAC31), spu_splats((float)ASINH_MAC29));
    mresult = spu_madd(xsqu, mresult, spu_splats((float)ASINH_MAC27));
    mresult = spu_madd(xsqu, mresult, spu_splats((float)ASINH_MAC25));
    mresult = spu_madd(xsqu, mresult, spu_splats((float)ASINH_MAC23));
    mresult = spu_madd(xsqu, mresult, spu_splats((float)ASINH_MAC21));
    mresult = spu_madd(xsqu, mresult, spu_splats((float)ASINH_MAC19));
    mresult = spu_madd(xsqu, mresult, spu_splats((float)ASINH_MAC17));
    mresult = spu_madd(xsqu, mresult, spu_splats((float)ASINH_MAC15));
    mresult = spu_madd(xsqu, mresult, spu_splats((float)ASINH_MAC13));
    mresult = spu_madd(xsqu, mresult, spu_splats((float)ASINH_MAC11));
    mresult = spu_madd(xsqu, mresult, spu_splats((float)ASINH_MAC09));
    mresult = spu_madd(xsqu, mresult, spu_splats((float)ASINH_MAC07));
    mresult = spu_madd(xsqu, mresult, spu_splats((float)ASINH_MAC05));
    mresult = spu_madd(xsqu, mresult, spu_splats((float)ASINH_MAC03));
    mresult = spu_madd(xsqu, mresult, spu_splats((float)ASINH_MAC01));
    mresult = spu_mul(xabs, mresult);

    /*
     * Choose between series and formula
     */
    use_form  = spu_cmpgt(xabs, switch_approx);
    result = spu_sel(mresult, fresult, use_form);

    /*
     * Truncation correction on spu
     */
    truncadd = spu_sel(oneu, threeu, use_form);
    truncadd = spu_sel(truncadd, twou, spu_cmpgt(xabs, trunc_part2));
    result = (vec_float4)spu_add((vec_uint4)result, truncadd);

    /* Preserve sign - asinh is anti-symmetric */
    result = spu_sel(result, x, (vec_uint4)sign_mask);

    return result;
}

#endif /* _ASINHF4_H_ */
#endif /* __SPU__ */
