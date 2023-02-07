/*
FUNCTION
       <<wmemset>>---set wide characters in memory 

SYNOPSIS
       #include <wchar.h>
       wchar_t *wmemset(wchar_t *<[s]>, wchar_t <[c]>, size_t <[n]>);

DESCRIPTION
       The <<wmemset>> function copies the value of <[c]> into each of the
       first <[n]> wide characters of the object pointed to by <[s]>.  This
       function is not affected by locale and all wchar_t values are treated
       identically.  The null wide character and wchar_t values not
       corresponding to valid characters are not treated specially.

       If <[n]> is zero, <[s]> must be a valid pointer and the function
       copies zero wide characters.

RETURNS
       The <<wmemset>> function returns the value of <[s]>.

PORTABILITY
<<wmemset>> is ISO/IEC 9899/AMD1:1995 (ISO C).

No supporting OS subroutines are required.
*/

/*     $NetBSD: wmemset.c,v 1.1 2000/12/23 23:14:37 itojun Exp $       */

/*-
 * Copyright (c)1999 Citrus Project,
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
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 *	citrus Id: wmemset.c,v 1.2 2000/12/20 14:08:31 itojun Exp
 */

#include <_ansi.h>
#include <wchar.h>

wchar_t	*
wmemset (wchar_t *s,
	wchar_t c,
	size_t n)
{
	size_t i;
	wchar_t *p;

	p = (wchar_t *)s;
	for (i = 0; i < n; i++) {
		*p = c;
		p++;
	}
	return s;
}
