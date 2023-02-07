/* wf_jn.c -- float version of w_jn.c.
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
#include <errno.h>


#ifdef __STDC__
	float jnf(int n, float x)	/* wrapper jnf */
#else
	float jnf(n,x)			/* wrapper jnf */
	float x; int n;
#endif
{
#ifdef _IEEE_LIBM
	return jnf(n,x);
#else
	float z;
	z = jnf(n,x);
	if(_LIB_VERSION == _IEEE_ || isnanf(x) ) return z;
	if(fabsf(x)>(float)X_TLOSS) {
	    /* jnf(|x|>X_TLOSS) */
	    errno = ERANGE;
	    return 0.0f;
	} else
	    return z;
#endif
}

#ifdef __STDC__
	float ynf(int n, float x)	/* wrapper ynf */
#else
	float ynf(n,x)			/* wrapper ynf */
	float x; int n;
#endif
{
#ifdef _IEEE_LIBM
	return ynf(n,x);
#else
	float z;
	z = ynf(n,x);
	if(_LIB_VERSION == _IEEE_ || isnanf(x) ) return z;
        if(x <= 0.0f){
	    /* ynf(n,0) = -inf or ynf(x<0) = NaN */
#ifndef HUGE_VAL 
#define HUGE_VAL inf
	    double inf = 0.0;

	    SET_HIGH_WORD(inf,0x7ff00000);	/* set inf to infinite */
#endif
	    errno = EDOM;
	    return (float)-HUGE_VAL;
        }
	if(x>(float)X_TLOSS) {
	    /* ynf(x>X_TLOSS) */
	    errno = ERANGE;
	    return 0.0f;
	} else
	    return z;
#endif
}

#ifdef _DOUBLE_IS_32BITS

#ifdef __STDC__
	double jn(int n, double x)
#else
	double jn(n,x)
	double x; int n;
#endif
{
	return (double) jnf(n, (float) x);
}

#ifdef __STDC__
	double yn(int n, double x)
#else
	double yn(n,x)
	double x; int n;
#endif
{
	return (double) ynf(n, (float) x);
}

#endif /* defined(_DOUBLE_IS_32BITS) */
