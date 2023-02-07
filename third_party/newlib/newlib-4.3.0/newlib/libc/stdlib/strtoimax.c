/*-
 * Copyright (c) 1992, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * Copyright (c) 2011 The FreeBSD Foundation
 * All rights reserved.
 * Portions of this software were developed by David Chisnall
 * under sponsorship from the FreeBSD Foundation.
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

#if defined(LIBC_SCCS) && !defined(lint)
static char sccsid[] = "from @(#)strtol.c	8.1 (Berkeley) 6/4/93";
#endif /* LIBC_SCCS and not lint */
#include <sys/cdefs.h>
__FBSDID("$FreeBSD: head/lib/libc/stdlib/strtoimax.c 251672 2013-06-13 00:19:30Z emaste $");

#include <ctype.h>
#include <errno.h>
#include <stdlib.h>
#include <inttypes.h>
#include <stdint.h>
#include <reent.h>
#include "../locale/setlocale.h"

/*
 * Convert a string to an intmax_t integer.
 *
 * Assumes that the upper and lower case
 * alphabets and digits are each contiguous.
 */

/*
 *Reentrant version of strtoimax.
 */
static intmax_t
_strtoimax_l(struct _reent *rptr, const char * __restrict nptr,
	     char ** __restrict endptr, int base, locale_t loc)
{
	const char *s = nptr;
	uintmax_t acc = 0;
	char c;
	uintmax_t cutoff;
	int neg = 0, any = 0, cutlim;

	/*
	 * Skip white space and pick up leading +/- sign if any.
	 * If base is 0, allow 0x for hex and 0 for octal, else
	 * assume decimal; if base is already 16, allow 0x.
	 */
	do {
		c = *s++;
	} while (isspace_l(c, loc));
	if (c == '-') {
		neg = 1;
		c = *s++;
	} else {
		neg = 0;
		if (c == '+')
			c = *s++;
	}
	if ((base == 0 || base == 16) &&
	    c == '0' && (*s == 'x' || *s == 'X')) {
		c = s[1];
		s += 2;
		base = 16;
	}
	if (base == 0)
		base = c == '0' ? 8 : 10;

	if (base < 2 || base > 36)
		goto noconv;

	/*
	 * Compute the cutoff value between legal numbers and illegal
	 * numbers.  That is the largest legal value, divided by the
	 * base.  An input number that is greater than this value, if
	 * followed by a legal input character, is too big.  One that
	 * is equal to this value may be valid or not; the limit
	 * between valid and invalid numbers is then based on the last
	 * digit.  For instance, if the range for intmax_t is
	 * [-9223372036854775808..9223372036854775807] and the input base
	 * is 10, cutoff will be set to 922337203685477580 and cutlim to
	 * either 7 (neg==0) or 8 (neg==1), meaning that if we have
	 * accumulated a value > 922337203685477580, or equal but the
	 * next digit is > 7 (or 8), the number is too big, and we will
	 * return a range error.
	 *
	 * Set 'any' if any `digits' consumed; make it negative to indicate
	 * overflow.
	 */
	cutoff = neg ? -(uintmax_t)INTMAX_MIN : INTMAX_MAX;
	cutlim = cutoff % base;
	cutoff /= base;
	for ( ; ; c = *s++) {
		if (c >= '0' && c <= '9')
			c -= '0';
		else if (c >= 'A' && c <= 'Z')
			c -= 'A' - 10;
		else if (c >= 'a' && c <= 'z')
			c -= 'a' - 10;
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
		acc = neg ? INTMAX_MIN : INTMAX_MAX;
		_REENT_ERRNO(rptr) = ERANGE;
	} else if (!any) {
noconv:
		_REENT_ERRNO(rptr) = EINVAL;
	} else if (neg)
		acc = -acc;
	if (endptr != NULL)
		*endptr = (char *)(any ? s - 1 : nptr);
	return (acc);
}

intmax_t
_strtoimax_r(struct _reent *rptr, const char *__restrict nptr,
	     char **__restrict endptr, int base)
{
	return _strtoimax_l(rptr, nptr, endptr, base, __get_current_locale());
}

#ifndef _REENT_ONLY

intmax_t
strtoimax_l(const char * __restrict nptr, char ** __restrict endptr, int base,
	    locale_t loc)
{
	return _strtoimax_l(_REENT, nptr, endptr, base, loc);
}

intmax_t
strtoimax(const char* __restrict nptr, char** __restrict endptr, int base)
{
	return _strtoimax_l(_REENT, nptr, endptr, base, __get_current_locale());
}

#endif
