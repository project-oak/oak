
/* @(#)w_atan2.c 5.1 93/09/24 */
/*
 * ====================================================
 * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
 *
 * Developed at SunPro, a Sun Microsystems, Inc. business.
 * Permission to use, copy, modify, and distribute this
 * software is freely granted, provided that this notice 
 * is preserved.
 * ====================================================
 *
 */

/*
FUNCTION
        <<atan2>>, <<atan2f>>---arc tangent of y/x

INDEX
   atan2
INDEX
   atan2f

SYNOPSIS
        #include <math.h>
        double atan2(double <[y]>,double <[x]>);
        float atan2f(float <[y]>,float <[x]>);

DESCRIPTION

<<atan2>> computes the inverse tangent (arc tangent) of <[y]>/<[x]>. 
<<atan2>> produces the correct result even for angles near 
@ifnottex
pi/2 or -pi/2 
@end ifnottex
@tex
$\pi/2$ or $-\pi/2$
@end tex
(that is, when <[x]> is near 0). 

<<atan2f>> is identical to <<atan2>>, save that it takes and returns
<<float>>. 

RETURNS
<<atan2>> and <<atan2f>> return a value in radians, in the range of 
@ifnottex
-pi to pi.
@end ifnottex
@tex
$-\pi$ to $\pi$.
@end tex

PORTABILITY
<<atan2>> is ANSI C.  <<atan2f>> is an extension.


*/

/* 
 * wrapper atan2(y,x)
 */

#include "fdlibm.h"
#include <errno.h>

#ifndef _DOUBLE_IS_32BITS

#ifdef __STDC__
	double atan2(double y, double x)	/* wrapper atan2 */
#else
	double atan2(y,x)			/* wrapper atan2 */
	double y,x;
#endif
{
	return __ieee754_atan2(y,x);
}

#endif /* defined(_DOUBLE_IS_32BITS) */
