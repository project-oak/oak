/*	$NetBSD: bsearch.c,v 1.15 2012/03/04 20:01:45 christos Exp $	*/

/*
 * Copyright (c) 1990, 1993
 *	The Regents of the University of California.  All rights reserved.
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

#include <sys/cdefs.h>
#if defined(LIBC_SCCS) && !defined(lint)
#if 0
static char sccsid[] = "@(#)bsearch.c	8.1 (Berkeley) 6/4/93";
#else
__RCSID("$NetBSD: bsearch.c,v 1.15 2012/03/04 20:01:45 christos Exp $");
#endif
#endif /* LIBC_SCCS and not lint */

#include <assert.h>
#include <errno.h>
#include <stdlib.h>

/* Oak modification: START */
// Pull definitions from netbsd-compat.h

// NetBSD uses _DIAGASSERT to null-check arguments and the like,
// but it's clear from the number of mistakes in their assertions
// that they don't actually test or ship with this.
#define _DIAGASSERT(e) /* nothing */

/*
 * The following macro is used to remove const cast-away warnings
 * from gcc -Wcast-qual; it should be used with caution because it
 * can hide valid errors; in particular most valid uses are in
 * situations where the API requires it, not to cast away string
 * constants. We don't use *intptr_t on purpose here and we are
 * explicit about unsigned long so that we don't have additional
 * dependencies.
 */
#define __UNCONST(a)    ((void *)(unsigned long)(const void *)(a))
/* Oak modification: END */

/*
 * Perform a binary search.
 *
 * The code below is a bit sneaky.  After a comparison fails, we
 * divide the work in half by moving either left or right. If lim
 * is odd, moving left simply involves halving lim: e.g., when lim
 * is 5 we look at item 2, so we change lim to 2 so that we will
 * look at items 0 & 1.  If lim is even, the same applies.  If lim
 * is odd, moving right again involes halving lim, this time moving
 * the base up one item past p: e.g., when lim is 5 we change base
 * to item 3 and make lim 2 so that we will look at items 3 and 4.
 * If lim is even, however, we have to shrink it by one before
 * halving: e.g., when lim is 4, we still looked at item 2, so we
 * have to make lim 3, then halve, obtaining 1, so that we will only
 * look at item 3.
 */
void *
bsearch(const void *key, const void *base0, size_t nmemb, size_t size,
    int (*compar)(const void *, const void *))
{
	const char *base = base0;
	size_t lim;
	int cmp;
	const void *p;
    
	_DIAGASSERT(key != NULL);
	_DIAGASSERT(base0 != NULL || nmemb == 0);
	_DIAGASSERT(compar != NULL);

	for (lim = nmemb; lim != 0; lim >>= 1) {
		p = base + (lim >> 1) * size;
		cmp = (*compar)(key, p);
		if (cmp == 0)
			return __UNCONST(p);
		if (cmp > 0) {	/* key > p: move right */
			base = (const char *)p + size;
			lim--;
		}		/* else move left */
	}
	return (NULL);
}