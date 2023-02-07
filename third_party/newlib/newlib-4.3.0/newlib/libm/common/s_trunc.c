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
FUNCTION
<<trunc>>, <<truncf>>---round to integer, towards zero
INDEX
	trunc
INDEX
	truncf

SYNOPSIS
	#include <math.h>
	double trunc(double <[x]>);
	float truncf(float <[x]>);

DESCRIPTION
	The <<trunc>> functions round their argument to the integer value, in
	floating format, nearest to but no larger in magnitude than the
	argument, regardless of the current rounding direction.  (While the
	"inexact" floating-point exception behavior is unspecified by the C
	standard, the <<trunc>> functions are written so that "inexact" is not
	raised if the result does not equal the argument, which behavior is as
	recommended by IEEE 754 for its related functions.)

RETURNS
<[x]> truncated to an integral value.

PORTABILITY
ANSI C, POSIX

*/

#include "fdlibm.h"

#ifndef _DOUBLE_IS_32BITS

#ifdef __STDC__
	double trunc(double x)
#else
	double trunc(x)
	double x;
#endif
{
  int signbit;
  /* Most significant word, least significant word. */
  int msw;
  unsigned int lsw;
  int exponent_less_1023;

  EXTRACT_WORDS(msw, lsw, x);

  /* Extract sign bit. */
  signbit = msw & 0x80000000;

  /* Extract exponent field. */
  exponent_less_1023 = ((msw & 0x7ff00000) >> 20) - 1023;

  if (exponent_less_1023 < 20)
    {
      /* All significant digits are in msw. */
      if (exponent_less_1023 < 0)
        {
          /* -1 < x < 1, so result is +0 or -0. */
          INSERT_WORDS(x, signbit, 0);
        }
      else
        {
          /* All relevant fraction bits are in msw, so lsw of the result is 0. */
          INSERT_WORDS(x, signbit | (msw & ~(0x000fffff >> exponent_less_1023)), 0);
        }
    }
  else if (exponent_less_1023 > 51)
    {
      if (exponent_less_1023 == 1024)
        {
          /* x is infinite, or not a number, so trigger an exception. */
          return x + x;
        }
      /* All bits in the fraction fields of the msw and lsw are needed in the result. */
    }
  else
    {
      /* All fraction bits in msw are relevant.  Truncate irrelevant
         bits from lsw. */
      INSERT_WORDS(x, msw, lsw & ~(0xffffffffu >> (exponent_less_1023 - 20)));
    }
  return x;
}

#endif /* _DOUBLE_IS_32BITS */
