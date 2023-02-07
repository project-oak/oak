/*-
 * Copyright (c) 1992, 1993, 1994 Henry Spencer.
 * Copyright (c) 1992, 1993, 1994
 *	The Regents of the University of California.  All rights reserved.
 *
 * This code is derived from software contributed to Berkeley by
 * Henry Spencer.
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
 *
 *	@(#)cclass.h	8.3 (Berkeley) 3/20/94
 * $FreeBSD: src/lib/libc/regex/cclass.h,v 1.4 2002/03/22 23:41:56 obrien Exp $
 */


typedef enum {CALNUM, CALPHA, CBLANK, CCNTRL, CDIGIT, CGRAPH,
	      CLOWER, CPRINT, CPUNCT, CSPACE, CUPPER, CXDIGIT} citype;

/* character-class table */
static struct cclass {
	char *name;
	citype fidx;
} cclasses[] = {
	{"alnum",       CALNUM},
	{"alpha",       CALPHA},
	{"blank",       CBLANK},
	{"cntrl",       CCNTRL},
	{"digit",       CDIGIT},
	{"graph",       CGRAPH},
	{"lower",       CLOWER},
	{"print",       CPRINT},
	{"punct",       CPUNCT},
	{"space",       CSPACE},
	{"upper",       CUPPER},
	{"xdigit",      CXDIGIT},
	{NULL,          }
};
