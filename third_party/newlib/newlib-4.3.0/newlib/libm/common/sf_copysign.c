/* sf_copysign.c -- float version of s_copysign.c.
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

/*
 * copysignf(float x, float y)
 * copysignf(x,y) returns a value with the magnitude of x and
 * with the sign bit of y.
 */

#include "fdlibm.h"

#ifdef __STDC__
	float copysignf(float x, float y)
#else
	float copysignf(x,y)
	float x,y;
#endif
{
	__uint32_t ix,iy;
	GET_FLOAT_WORD(ix,x);
	GET_FLOAT_WORD(iy,y);
	SET_FLOAT_WORD(x,(ix&0x7fffffff)|(iy&0x80000000));
        return x;
}

#ifdef _DOUBLE_IS_32BITS

#ifdef __STDC__
	double copysign(double x, double y)
#else
	double copysign(x,y)
	double x,y;
#endif
{
	return (double) copysignf((float) x, (float) y);
}

#endif /* defined(_DOUBLE_IS_32BITS) */
