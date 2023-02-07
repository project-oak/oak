/*
FUNCTION
	<<wcslen>>---get wide-character string length 

SYNOPSIS
	#include <wchar.h>
	size_t wcslen(const wchar_t *<[s]>);

DESCRIPTION
	The <<wcslen>> function computes the number of wide-character codes
	in the wide-character string to which <[s]> points, not including the
	terminating null wide-character code.

RETURNS
	The <<wcslen>> function returns the length of <[s]>; no return value is
	reserved to indicate an error.

PORTABILITY
<<wcslen>> is ISO/IEC 9899/AMD1:1995 (ISO C).

No supporting OS subroutines are required.
*/

/*	$NetBSD: wcslen.c,v 1.1 2000/12/23 23:14:36 itojun Exp $	*/

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
 *	citrus Id: wcslen.c,v 1.1 1999/12/29 21:47:45 tshiozak Exp
 */

#include <_ansi.h>
#include <wchar.h>

size_t
wcslen (const wchar_t * s)
{
  const wchar_t *p;

  p = s;
  while (*p)
    p++;

  return p - s;
}
