//  Copyright 2022 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/*
 * Template source file for strtol/ll/ul/ull functions. Requires
 * appropriate definition of macros below.
 */

/* Specs for strouX() functions are weird: "if there was a leading
 * minus sign, the negation of the result of the con‐ version
 * represented as an unsigned value". This means that we accept to
 * convert strings like "-1234"... */

#ifndef _STRTOX_FNAME
#error "missing function name"
#endif

#ifndef _STRTOX_SIGNED_TNAME
#error "missing signed type name"
#endif

#ifndef _STRTOX_VARIANT_UNSIGNED
#error "missing indication of type signedness (0 for unsigned)"
#endif

#ifndef _STRTOX_INTMAX
#error "missing max value for type"
#endif

#if !_STRTOX_VARIANT_UNSIGNED && !defined(_STRTOX_INTMIN)
#error "missing min value for signed type"
#endif

#define _STRTOX_UNSIGNED_TNAME unsigned _STRTOX_SIGNED_TNAME

#if _STRTOX_VARIANT_UNSIGNED
unsigned
#endif
    _STRTOX_SIGNED_TNAME
        _STRTOX_FNAME(const char *nptr, char **endptr, int base) {
  _STRTOX_UNSIGNED_TNAME absval = 0;
  _STRTOX_UNSIGNED_TNAME max_unshifted_absval;
  char dtop, ltop, utop;
  char *s = (char *)nptr;
  const char *endc = nptr;
  int positive = 1;
  int overflow = 0;
  unsigned max_last_digit;

  if (!((base == 0) || ((base >= 2) && (base <= 36)))) return 0;

  /* spaces allowed before */
  while (*s && isspace(*s)) s++;

  /* both + and - allowed before value, even for strouX (!) */
  if (*s == '+')
    s++;
  else if (*s == '-') {
    positive = 0;
    s++;
  }

  /* Handle automatic base == 0, also allow 0x... in hex mode */
  if ((base == 0) && (!strncmp(s, "0x", 2) || !strncmp(s, "0X", 2))) {
    base = 16;
    endc = s + 1;
    s += 2;
  } else if (base == 16) {
    if (!strncmp(s, "0x", 2) || !strncmp(s, "0X", 2)) {
      base = 16;
      endc = s + 1;
      s += 2;
    }
  } else if ((base == 0) && (*s == '0'))
    base = 8;
  else if (base == 0)
    base = 10;

  /* Determine min/max allowed digits */
  if (base <= 10) {
    dtop = '0' + base - 1;
    ltop = utop = '\0';
  } else {
    dtop = '0' + 9;
    ltop = 'a' + (base - 10) - 1;
    utop = 'A' + (base - 10) - 1;
  }

#if _STRTOX_VARIANT_UNSIGNED
  max_last_digit = _STRTOX_INTMAX % (_STRTOX_UNSIGNED_TNAME)base;
  max_unshifted_absval = _STRTOX_INTMAX / (_STRTOX_UNSIGNED_TNAME)base;
#else
  if (positive)
    max_unshifted_absval = _STRTOX_INTMAX;
  else
    max_unshifted_absval = -(_STRTOX_UNSIGNED_TNAME)_STRTOX_INTMIN;
  max_last_digit = max_unshifted_absval % (_STRTOX_UNSIGNED_TNAME)base;
  max_unshifted_absval /= (_STRTOX_UNSIGNED_TNAME)base;
#endif

  while (*s) {
    _STRTOX_UNSIGNED_TNAME digit;
    if ((*s >= '0') && (*s <= dtop))
      digit = *s - '0';
    else if ((*s >= 'a') && (*s <= ltop))
      digit = 10 + (*s - 'a');
    else if ((*s >= 'A') && (*s <= utop))
      digit = 10 + (*s - 'A');
    else
      break; /* unallowed digit */

    s++;
    endc = s;

    if (!overflow) {
      if (absval > max_unshifted_absval)
        overflow = 1;
      else if ((absval == max_unshifted_absval) && (digit > max_last_digit))
        overflow = 1;
      else {
        absval *= base;
        absval += digit;
      }
    }
  }

  if (overflow) {
#if !_STRTOX_VARIANT_UNSIGNED
    if (!positive)
      absval = _STRTOX_INTMIN;
    else
#endif
      absval = _STRTOX_INTMAX;
  } else if (!positive)
    absval = -absval;

  if (endptr) *endptr = (char *)endc;

  return absval;
}
