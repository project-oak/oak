/*	$NetBSD: gets_chk.c,v 1.7 2013/10/04 20:49:16 christos Exp $	*/

/*-
 * Copyright (c) 2006 The NetBSD Foundation, Inc.
 * All rights reserved.
 *
 * This code is derived from software contributed to The NetBSD Foundation
 * by Christos Zoulas.
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
 * THIS SOFTWARE IS PROVIDED BY THE NETBSD FOUNDATION, INC. AND CONTRIBUTORS
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE FOUNDATION OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */
#include <sys/cdefs.h>
__RCSID("$NetBSD: gets_chk.c,v 1.7 2013/10/04 20:49:16 christos Exp $");

/*LINTLIBRARY*/

#include <ssp/ssp.h>
#include <stdio.h>
#include <string.h>
#include <limits.h>
#include <stdlib.h>
#include <ssp/stdio.h>

extern char *__gets(char *);
#undef gets
#ifdef __NEWLIB__
#define __gets gets
#endif

char *
__gets_chk(char * __restrict buf, size_t slen)
{
	char *abuf;
	size_t len;

	if (slen >= (size_t)INT_MAX)
		return __gets(buf);

	if ((abuf = malloc(slen + 1)) == NULL)
		return __gets(buf);

	if (fgets(abuf, (int)(slen + 1), stdin) == NULL) {
		free(abuf);
		return NULL;
	}

	len = strlen(abuf);
	if (len > 0 && abuf[len - 1] == '\n')
		--len;

	if (len >= slen)
		__chk_fail();

	(void)memcpy(buf, abuf, len);

	buf[len] = '\0';
	free(abuf);
	return buf;
}
