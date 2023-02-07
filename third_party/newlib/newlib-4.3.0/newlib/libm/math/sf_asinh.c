/* sf_asinh.c -- float version of s_asinh.c.
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

#ifdef __STDC__
static const float 
#else
static float 
#endif
one =  1.0000000000e+00, /* 0x3F800000 */
ln2 =  6.9314718246e-01, /* 0x3f317218 */
huge=  1.0000000000e+30; 

#ifdef __STDC__
	float asinhf(float x)
#else
	float asinhf(x)
	float x;
#endif
{	
	float t,w;
	__int32_t hx,ix;
	GET_FLOAT_WORD(hx,x);
	ix = hx&0x7fffffff;
	if(!FLT_UWORD_IS_FINITE(ix)) return x+x;	/* x is inf or NaN */
	if(ix< 0x31800000) {	/* |x|<2**-28 */
	    if(huge+x>one) return x;	/* return x inexact except 0 */
	} 
	if(ix>0x4d800000) {	/* |x| > 2**28 */
	    w = __ieee754_logf(fabsf(x))+ln2;
	} else if (ix>0x40000000) {	/* 2**28 > |x| > 2.0 */
	    t = fabsf(x);
	    w = __ieee754_logf((float)2.0*t+one/(__ieee754_sqrtf(x*x+one)+t));
	} else {		/* 2.0 > |x| > 2**-28 */
	    t = x*x;
	    w =log1pf(fabsf(x)+t/(one+__ieee754_sqrtf(one+t)));
	}
	if(hx>0) return w; else return -w;
}

#ifdef _DOUBLE_IS_32BITS

#ifdef __STDC__
	double asinh(double x)
#else
	double asinh(x)
	double x;
#endif
{
	return (double) asinhf((float) x);
}

#endif /* defined(_DOUBLE_IS_32BITS) */
