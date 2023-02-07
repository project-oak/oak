/* wf_sinh.c -- float version of w_sinh.c.
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
 * wrapper sinhf(x)
 */

#include "fdlibm.h"
#include <errno.h>

#ifdef __STDC__
	float sinhf(float x)		/* wrapper sinhf */
#else
	float sinhf(x)			/* wrapper sinhf */
	float x;
#endif
{
#ifdef _IEEE_LIBM
	return __ieee754_sinhf(x);
#else
	float z; 
	z = __ieee754_sinhf(x);
	if(_LIB_VERSION == _IEEE_) return z;
	if(!finitef(z)&&finitef(x)) {
	    /* sinhf(finite) overflow */
	    errno = ERANGE;
	    return ( (x>0.0f) ? HUGE_VALF : -HUGE_VALF);
	} else
	    return z;
#endif
}

#ifdef _DOUBLE_IS_32BITS

#ifdef __STDC__
	double sinh(double x)
#else
	double sinh(x)
	double x;
#endif
{
	return (double) sinhf((float) x);
}

#endif /* defined(_DOUBLE_IS_32BITS) */
