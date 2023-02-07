/* ef_cosh.c -- float version of e_cosh.c.
 * Conversion to float by Ian Lance Taylor, Cygnus Support, ian@cygnus.com.
 */

/*
 * ====================================================
 * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
 *
 * Developed at SunPro, a Sun Microsystems, Inc. business.
 * Permission to use, copy, modify, and distribute this
 * software is freely granted, provided that this notice 
 * is preserved.
 * ====================================================
 */

#include "fdlibm.h"
#include "math_config.h"

#ifdef __v810__
#define const
#endif

#ifdef __STDC__
static const float one = 1.0, half=0.5;
#else
static float one = 1.0, half=0.5;
#endif

#ifdef __STDC__
	float __ieee754_coshf(float x)
#else
	float __ieee754_coshf(x)
	float x;
#endif
{	
	float t,w;
	__int32_t ix;

	GET_FLOAT_WORD(ix,x);
	ix &= 0x7fffffff;

    /* x is INF or NaN */
	if(!FLT_UWORD_IS_FINITE(ix)) return x*x;	

    /* |x| in [0,0.5*ln2], return 1+expm1(|x|)^2/(2*exp(|x|)) */
	if(ix<0x3eb17218) {
	    t = expm1f(fabsf(x));
	    w = one+t;
	    if (ix<0x24000000) return w;	/* cosh(tiny) = 1 */
	    return one+(t*t)/(w+w);
	}

    /* |x| in [0.5*ln2,22], return (exp(|x|)+1/exp(|x|)/2; */
	if (ix < 0x41b00000) {
		t = __ieee754_expf(fabsf(x));
		return half*t+half/t;
	}

    /* |x| in [22, log(maxdouble)] return half*exp(|x|) */
	if (ix <= FLT_UWORD_LOG_MAX)
	  return half*__ieee754_expf(fabsf(x));

    /* |x| in [log(maxdouble), overflowthresold] */
	if (ix <= FLT_UWORD_LOG_2MAX) {
	    w = __ieee754_expf(half*fabsf(x));
	    t = half*w;
	    return t*w;
	}

    /* |x| > overflowthresold, cosh(x) overflow */
	return __math_oflowf(0);
}
