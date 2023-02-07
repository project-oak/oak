/*
FUNCTION
	<<wcstoull>>, <<wcstoull_l>>---wide string to unsigned long long

INDEX
	wcstoull

INDEX
	wcstoull_l

INDEX
	_wcstoull_r

SYNOPSIS
	#include <wchar.h>
        unsigned long long wcstoull(const wchar_t *__restrict <[s]>,
				    wchar_t **__restrict <[ptr]>,
				    int <[base]>);

	#include <wchar.h>
        unsigned long long wcstoull_l(const wchar_t *__restrict <[s]>,
				      wchar_t **__restrict <[ptr]>,
				      int <[base]>,
				      locale_t <[locale]>);

        unsigned long long _wcstoull_r(void *<[reent]>, const wchar_t *<[s]>,
				       wchar_t **<[ptr]>, int <[base]>);

DESCRIPTION
The function <<wcstoull>> converts the wide string <<*<[s]>>> to
an <<unsigned long long>>. First, it breaks down the string into three parts:
leading whitespace, which is ignored; a subject string consisting
of the digits meaningful in the radix specified by <[base]>
(for example, <<0>> through <<7>> if the value of <[base]> is 8);
and a trailing portion consisting of one or more unparseable characters,
which always includes the terminating null character. Then, it attempts
to convert the subject string into an unsigned long long integer, and returns the
result.

If the value of <[base]> is zero, the subject string is expected to look
like a normal C integer constant:  an optional sign (<<+>> or <<->>),
a possible <<0x>> indicating hexadecimal radix or a possible <0> indicating
octal radix, and a number.
If <[base]> is between 2 and 36, the expected form of the subject is a
sequence of digits (which may include letters, depending on the
base) representing an integer in the radix specified by <[base]>.
The letters <<a>>--<<z>> (or <<A>>--<<Z>>) are used as digits valued from
10 to 35. If <[base]> is 16, a leading <<0x>> is permitted.

The subject sequence is the longest initial sequence of the input
string that has the expected form, starting with the first
non-whitespace character.  If the string is empty or consists entirely
of whitespace, or if the first non-whitespace character is not a
permissible digit, the subject string is empty.

If the subject string is acceptable, and the value of <[base]> is zero,
<<wcstoull>> attempts to determine the radix from the input string. A
string with a leading <<0x>> is treated as a hexadecimal value; a string with
a leading <<0>> and no <<x>> is treated as octal; all other strings are
treated as decimal. If <[base]> is between 2 and 36, it is used as the
conversion radix, as described above. Finally, a pointer to the first
character past the converted subject string is stored in <[ptr]>, if
<[ptr]> is not <<NULL>>.

If the subject string is empty (that is, if <<*>><[s]> does not start
with a substring in acceptable form), no conversion
is performed and the value of <[s]> is stored in <[ptr]> (if <[ptr]> is
not <<NULL>>).

The alternate function <<_wcstoull_r>> is a reentrant version.  The
extra argument <[reent]> is a pointer to a reentrancy structure.


<<wcstoull_l>> is like <<wcstoull>> but performs the conversion based on the
locale specified by the locale object locale.  If <[locale]> is
LC_GLOBAL_LOCALE or not a valid locale object, the behaviour is undefined.

RETURNS
<<wcstoull>>, <<wcstoull_l>> return <<0>> and sets <<errno>> to <<EINVAL>>
if the value of <[base]> is not supported.

<<wcstoull>>, <<wcstoull_l>> return the converted value, if any. If no
conversion was made, <<0>> is returned.

<<wcstoull>>, <<wcstoull_l>> return <<ULLONG_MAX>> if the magnitude of
the converted value is too large, and sets <<errno>> to <<ERANGE>>.

PORTABILITY
<<wcstoull>> is ANSI.
<<wcstoull_l>> is a GNU extension.

<<wcstoull>> requires no supporting OS subroutines.
*/

/*
 * Copyright (c) 1990 Regents of the University of California.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#define _GNU_SOURCE
#include <_ansi.h>
#include <limits.h>
#include <wchar.h>
#include <wctype.h>
#include <errno.h>
#include <reent.h>
#include "../locale/setlocale.h"

/* Make up for older non-compliant limits.h.  (This is a C99/POSIX function,
 * and both require ULLONG_MAX in limits.h.)  */
#if !defined(ULLONG_MAX)
# define ULLONG_MAX	ULONG_LONG_MAX
#endif

/*
 * Convert a wide string to an unsigned long long integer.
 */
unsigned long long
_wcstoull_l (struct _reent *rptr, const wchar_t *nptr, wchar_t **endptr,
	     int base, locale_t loc)
{
	register const wchar_t *s = nptr;
	register unsigned long long acc;
	register int c;
	register unsigned long long cutoff;
	register int neg = 0, any, cutlim;

	if(base < 0  ||  base == 1  ||  base > 36)  {
		_REENT_ERRNO(rptr) = EINVAL;
		return(0ULL);
	}
	/*
	 * See strtol for comments as to the logic used.
	 */
	do {
		c = *s++;
	} while (iswspace_l(c, loc));
	if (c == L'-') {
		neg = 1;
		c = *s++;
	} else if (c == L'+')
		c = *s++;
	if ((base == 0 || base == 16) &&
	    c == L'0' && (*s == L'x' || *s == L'X')) {
		c = s[1];
		s += 2;
		base = 16;
	}
	if (base == 0)
		base = c == L'0' ? 8 : 10;
	cutoff = (unsigned long long)ULLONG_MAX / (unsigned long long)base;
	cutlim = (unsigned long long)ULLONG_MAX % (unsigned long long)base;
	for (acc = 0, any = 0;; c = *s++) {
		if (c >= L'0' && c <= L'9')
			c -= L'0';
		else if (c >= L'A' && c <= L'Z')
			c -= L'A' - 10;
		else if (c >= L'a' && c <= L'z')
			c -= L'a' - 10;
		else
			break;
		if (c >= base)
			break;
               if (any < 0 || acc > cutoff || (acc == cutoff && c > cutlim))
			any = -1;
		else {
			any = 1;
			acc *= base;
			acc += c;
		}
	}
	if (any < 0) {
		acc = ULLONG_MAX;
		_REENT_ERRNO(rptr) = ERANGE;
	} else if (neg)
		acc = -acc;
	if (endptr != 0)
		*endptr = (wchar_t *) (any ? s - 1 : nptr);
	return (acc);
}

unsigned long long
_wcstoull_r (struct _reent *rptr,
	const wchar_t *nptr,
	wchar_t **endptr,
	int base)
{
	return _wcstoull_l (rptr, nptr, endptr, base, __get_current_locale ());
}

#ifndef _REENT_ONLY

unsigned long long
wcstoull_l (const wchar_t *__restrict s, wchar_t **__restrict ptr, int base,
	    locale_t loc)
{
	return _wcstoull_l (_REENT, s, ptr, base, loc);
}

unsigned long long
wcstoull (const wchar_t *__restrict s,
	wchar_t **__restrict ptr,
	int base)
{
	return _wcstoull_l (_REENT, s, ptr, base, __get_current_locale ());
}

#endif
