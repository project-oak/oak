/* lroundf adapted to be llroundf for Newlib, 2009 by Craig Howland.  */
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

long long int
llroundf(float x)
{
  __int32_t exponent_less_127;
  __uint32_t w;
  long long int result;
  __int32_t sign;

  GET_FLOAT_WORD (w, x);
  exponent_less_127 = ((w & 0x7f800000) >> 23) - 127;
  sign = (w & 0x80000000) != 0 ? -1 : 1;
  w &= 0x7fffff;
  w |= 0x800000;

  if (exponent_less_127 < (int)((8 * sizeof (long long int)) - 1))
    {
      if (exponent_less_127 < 0)
        return exponent_less_127 < -1 ? 0 : sign;
      else if (exponent_less_127 >= 23)
        result = (long long int) w << (exponent_less_127 - 23);
      else
        {
          w += 0x400000 >> exponent_less_127;
          result = w >> (23 - exponent_less_127);
        }
    }
  else
      return (long long int) x;

  return sign * result;
}

#ifdef _DOUBLE_IS_32BITS

long long int
llround(double x)
{
	return llroundf((float) x);
}

#endif /* defined(_DOUBLE_IS_32BITS) */
