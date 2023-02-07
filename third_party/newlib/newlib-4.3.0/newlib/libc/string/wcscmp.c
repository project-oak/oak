/*
FUNCTION
	<<wcscmp>>---compare two wide-character strings

SYNOPSIS
	#include <wchar.h>
	int wcscmp(const wchar_t *<[s1]>, *<[s2]>);

DESCRIPTION
	The <<wcscmp>> function compares the wide-character string pointed to
	by <[s1]> to the wide-character string pointed to by <[s2]>.

	The sign of a non-zero return value is determined by the sign of the
	difference between the values of the first pair of wide-character codes
	that differ in the objects being compared.

RETURNS
	Upon completion, <<wcscmp>> returns an integer greater than, equal to
	or less than 0, if the wide-character string pointed to by <[s1]> is
	greater than, equal to or less than the wide-character string pointed
	to by <[s2]> respectively. 

PORTABILITY
<<wcscmp>> is ISO/IEC 9899/AMD1:1995 (ISO C).

No supporting OS subroutines are required.
*/

/*	$NetBSD$	*/

/*-
 * Copyright (c) 1990, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * This code is derived from software contributed to Berkeley by
 * Chris Torek.
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

#include <_ansi.h>
#include <wchar.h>

/*
 * Compare strings.
 */
int
wcscmp (const wchar_t * s1,
	const wchar_t * s2)
{

  while (*s1 == *s2++)
    if (*s1++ == 0)
      return (0);
  return (*s1 - *--s2);
}
