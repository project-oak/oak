/*
FUNCTION
        <<strtosfix16>>, <<strtosfix32>>, <<strtosfix64>>---string to signed fixed point

INDEX
	strtosfix16
INDEX
	strtosfix32
INDEX
	strtosfix64
INDEX
	_strtosfix16_r
INDEX
	_strtosfix32_r
INDEX
	_strtosfix64_r

SYNOPSIS
	#include <stdlib.h>
        __int16 strtosfix16 (const char *<[s]>, char **<[ptr]>);

        __int32 strtosfix32 (const char *<[s]>, char **<[ptr]>);

        __int64 strtosfix64 (const char *<[s]>, char **<[ptr]>);

        __int16 _strtosfix16_r (void *<[reent]>, 
                       const char *<[s]>, char **<[ptr]>);

        __int32 _strtosfix32_r (void *<[reent]>, 
                       const char *<[s]>, char **<[ptr]>);

        __int64 _strtosfix64_r (void *<[reent]>, 
                       const char *<[s]>, char **<[ptr]>);

DESCRIPTION
        The function <<strtosfix16>> converts the string <<*<[s]>>> to
	a fixed-point sign + 15-bits fraction representation.  The function 
	follows the same rules as <<strtod>>.

	The substring converted is the longest initial
	subsequence of <[s]>, beginning with the first
	non-whitespace character, that has the format:
	.[+|-]<[digits]>[.][<[digits]>][(e|E)[+|-]<[digits]>] 
	The substring contains no characters if <[s]> is empty, consists
	entirely of whitespace, or if the first non-whitespace
	character is something other than <<+>>, <<->>, <<.>>, or a
	digit. If the substring is empty, no conversion is done, and
	the value of <[s]> is stored in <<*<[ptr]>>>.  Otherwise,
	the substring is converted, and a pointer to the final string
	(which will contain at least the terminating null character of
	<[s]>) is stored in <<*<[ptr]>>>.  If you want no
	assignment to <<*<[ptr]>>>, pass a null pointer as <[ptr]>.

	<<strtosfix32>> is identical to <<strtosfix16>> except that it 
	converts to fixed-point sign + 31-bits fraction representation.
	<<strtosfix64>> is also similar, except that it converts
	to fixed-point sign + 63-bit fraction format.

	The alternate functions <<_strtosfix16_r>>, <<_strtosfix32_r>>,
	and <<_strtosfix64_r>> are reentrant versions.
	The extra argument <[reent]> is a pointer to a reentrancy structure.

RETURNS
	The functions return the converted substring value, if any.  If
	no conversion can be performed, then 0 is returned.  If the converted
	value is a NaN, 0 is returned and errno is set to <<EDOM>>.
	If the converted value exceeds the maximum positive fixed-point value, 
	the output value is saturated to the maximum value and <<ERANGE>> is stored in 
	errno.  If the converted value is less than the minimum fixed-point negative
	value, then the output is saturated to the minimum value  and <<ERANGE>> is stored
	in errno.  Otherwise, the converted value is returned in the
	specified fixed-point format.

PORTABILITY
        <<strtosfix16>>, <<strtosfix32>>, and <<strtosfix64>> are non-standard.

        The OS subroutines of <<strtod>> are required.
*/

#ifdef __SPE__ 

#include <_ansi.h>
#include <limits.h>
#include <errno.h>
#include <stdlib.h>
#include <reent.h>
#include "vfieeefp.h"

/*
 * Convert a string to a fixed-point (sign + 15-bits) value.
 *
 * Ignores `locale' stuff.
 */
__int16_t
_strtosfix16_r (struct _reent *rptr,
	const char *nptr,
	char **endptr)
{
  union double_union dbl;
  unsigned long tmp, tmp2;
  int exp, negexp, sign;
  __int16_t result;

  dbl.d = _strtod_r (rptr, nptr, endptr);

  /* treat NAN as domain error, +/- infinity as saturation */
  if (!finite(dbl.d))
    {
      if (isnan (dbl.d))
	{
	  _REENT_ERRNO(rptr) = EDOM;
	  return 0;
	}
      _REENT_ERRNO(rptr) = ERANGE;
      if (word0(dbl) & Sign_bit)
	return SHRT_MIN;
      return SHRT_MAX;
    }

  /* check for normal saturation */
  if (dbl.d >= 1.0)
    {
      _REENT_ERRNO(rptr) = ERANGE;
      return SHRT_MAX;
    }
  else if (dbl.d < -1.0)
    {
      _REENT_ERRNO(rptr) = ERANGE;
      return SHRT_MIN;
    }

  /* otherwise we have normal number in range */

  /* strip off sign and exponent */
  sign = word0(dbl) & Sign_bit;
  exp = ((word0(dbl) & Exp_mask) >> Exp_shift) - Bias;
  negexp = -exp;
  if (negexp > 15)
    return 0;
  /* add in implicit normalized bit */
  tmp = word0(dbl) | Exp_msk1;
  /* remove exponent and sign */
  tmp <<= Ebits;
  if (negexp != 0)
    {
      /* perform rounding */
      tmp2 = tmp + (1 << (negexp - 1));
      result = (short)(tmp2 >> (negexp + 16));
      /* check if rounding caused carry bit which must be added into result */
      if (tmp2 < tmp)
	result |= (1 << (16 - negexp));
      /* check if positive saturation has occurred because of rounding */
      if (!sign && result < 0)
	{
	  _REENT_ERRNO(rptr) = ERANGE;
	  return SHRT_MAX;
	}
    }
  else
    {
      /* we have -1.0, no rounding necessary */
      return SHRT_MIN;
    }

  return  sign ? -result : result;
}

#ifndef _REENT_ONLY

__int16_t
strtosfix16 (const char *s,
	char **ptr)
{
  return _strtosfix16_r (_REENT, s, ptr);
}

#endif

#endif /* __SPE__ */
