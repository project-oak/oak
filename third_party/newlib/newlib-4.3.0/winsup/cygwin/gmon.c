/*-
 * Copyright (c) 1983, 1992, 1993
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
 * 4. Neither the name of the University nor the names of its contributors
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

#if !defined(lint) && defined(LIBC_SCCS)
static char rcsid[] = "$OpenBSD: gmon.c,v 1.8 1997/07/23 21:11:27 kstailey Exp $";
#endif

/*
 * This file is taken from Cygwin distribution. Please keep it in sync.
 * The differences should be within __MINGW32__ guard.
 */

#include <fcntl.h>
#include <stdlib.h>
#include <stdio.h>
#ifndef __MINGW32__
#include <unistd.h>
#include <sys/param.h>
#endif
#include <sys/types.h>
#include "gmon.h"
#include "profil.h"

/* XXX needed? */
//extern char *minbrk __asm ("minbrk");

#ifdef _WIN64
#define MINUS_ONE_P (-1LL)
#else
#define MINUS_ONE_P (-1)
#endif

#include <string.h>
#define bzero(ptr,size) memset (ptr, 0, size);

struct gmonparam _gmonparam = { GMON_PROF_OFF, NULL, 0, NULL, 0, NULL, 0, 0L,
  0, 0, 0, 0};

static int	s_scale;
/* see profil(2) where this is describe (incorrectly) */
#define		SCALE_1_TO_1	0x10000L

#define ERR(s) write(2, s, sizeof(s))

void	moncontrol __P((int));

static void *
fake_sbrk(int size)
{
    void *rv = malloc(size);
    if (rv)
      return rv;
    else
      return (void *) MINUS_ONE_P;
}

void monstartup (size_t, size_t);

void
monstartup (size_t lowpc, size_t highpc)
{
	register size_t o;
	char *cp;
	struct gmonparam *p = &_gmonparam;

	/*
	 * round lowpc and highpc to multiples of the density we're using
	 * so the rest of the scaling (here and in gprof) stays in ints.
	 */
	p->lowpc = ROUNDDOWN(lowpc, HISTFRACTION * sizeof(HISTCOUNTER));
	p->highpc = ROUNDUP(highpc, HISTFRACTION * sizeof(HISTCOUNTER));
	p->textsize = p->highpc - p->lowpc;
	p->kcountsize = p->textsize / HISTFRACTION;
	p->hashfraction = HASHFRACTION;
	p->fromssize = p->textsize / p->hashfraction;
	p->tolimit = p->textsize * ARCDENSITY / 100;
	if (p->tolimit < MINARCS)
		p->tolimit = MINARCS;
	else if (p->tolimit > MAXARCS)
		p->tolimit = MAXARCS;
	p->tossize = p->tolimit * sizeof(struct tostruct);

	cp = fake_sbrk(p->kcountsize + p->fromssize + p->tossize);
	if (cp == (char *)MINUS_ONE_P) {
		ERR("monstartup: out of memory\n");
		return;
	}

	/* zero out cp as value will be added there */
	bzero(cp, p->kcountsize + p->fromssize + p->tossize);

	p->tos = (struct tostruct *)cp;
	cp += p->tossize;
	p->kcount = (u_int16_t *)cp;
	cp += p->kcountsize;
	p->froms = (u_int16_t *)cp;

	/* XXX minbrk needed? */
	//minbrk = fake_sbrk(0);
	p->tos[0].link = 0;

	o = p->highpc - p->lowpc;
	if (p->kcountsize < o) {
#ifndef notdef
		s_scale = ((float)p->kcountsize / o ) * SCALE_1_TO_1;
#else /* avoid floating point */
		int quot = o / p->kcountsize;

		if (quot >= 0x10000)
			s_scale = 1;
		else if (quot >= 0x100)
			s_scale = 0x10000 / quot;
		else if (o >= 0x800000)
			s_scale = 0x1000000 / (o / (p->kcountsize >> 8));
		else
			s_scale = 0x1000000 / ((o << 8) / p->kcountsize);
#endif
	} else
		s_scale = SCALE_1_TO_1;

	moncontrol(1);
}

void _mcleanup (void);
void
_mcleanup(void)
{
	int fd;
	int hz;
	int fromindex;
	int endfrom;
	size_t frompc;
	int toindex;
	struct rawarc rawarc;
	struct gmonparam *p = &_gmonparam;
	struct gmonhdr gmonhdr, *hdr;
	char *filename = (char *) "gmon.out";
	char *prefix;
#ifdef DEBUG
	int log, len;
	char dbuf[200];
#endif

	if (p->state == GMON_PROF_ERROR)
		ERR("_mcleanup: tos overflow\n");

	hz = PROF_HZ;
	moncontrol(0);

	/* We copy an undocumented glibc feature: customizing the profiler's
	   output file name somewhat, depending on the env var GMON_OUT_PREFIX.
	   if GMON_OUT_PREFIX is unspecified, the file's name is "gmon.out".

	   if GMON_OUT_PREFIX is specified with at least one character, the
	   file's name is computed as "$GMON_OUT_PREFIX.$pid".

	   if GMON_OUT_PREFIX is specified but contains no characters, the
	   file's name is computed as "gmon.out.$pid".  Cygwin-specific.
	*/
	if ((prefix = getenv("GMON_OUT_PREFIX")) != NULL) {
		char *buf;
		/* Covers positive pid_t values. */
		int32_t divisor = 1000*1000*1000;
		pid_t pid = getpid();
		size_t len = strlen(prefix);

		if (len == 0)
			len = strlen(prefix = filename);
		buf = alloca(len + 13);// allow for '.', 10-digit pid, NUL, +1

		memcpy(buf, prefix, len);
		buf[len++] = '.';

		while (divisor > pid)  // skip leading zeroes
			divisor /= 10;
		do {                   // convert pid to digits and store 'em
			buf[len++] = (pid / divisor) + '0';
			pid %= divisor;
		} while (divisor /= 10);

		buf[len] = '\0';
		filename = buf;
	}

	fd = open(filename, O_CREAT|O_TRUNC|O_WRONLY|O_BINARY, 0666);
	if (fd < 0) {
		perror(filename);
		return;
	}
#ifdef DEBUG
	log = open("gmon.log", O_CREAT|O_TRUNC|O_WRONLY, 0664);
	if (log < 0) {
		perror("mcount: gmon.log");
		return;
	}
	len = sprintf(dbuf, "[mcleanup1] kcount 0x%x ssiz %d\n",
	    p->kcount, p->kcountsize);
	write(log, dbuf, len);
#endif
	hdr = (struct gmonhdr *)&gmonhdr;
	bzero(hdr, sizeof *hdr);
	hdr->lpc = p->lowpc;
	hdr->hpc = p->highpc;
	hdr->ncnt = p->kcountsize + sizeof(gmonhdr);
	hdr->version = GMONVERSION;
	hdr->profrate = hz;
	write(fd, (char *)hdr, sizeof *hdr);
	write(fd, p->kcount, p->kcountsize);
	endfrom = p->fromssize / sizeof(*p->froms);
	for (fromindex = 0; fromindex < endfrom; fromindex++) {
		if (p->froms[fromindex] == 0)
			continue;

		frompc = p->lowpc;
		frompc += fromindex * p->hashfraction * sizeof(*p->froms);
		for (toindex = p->froms[fromindex]; toindex != 0;
		     toindex = p->tos[toindex].link) {
#ifdef DEBUG
			len = sprintf(dbuf,
			"[mcleanup2] frompc 0x%x selfpc 0x%x count %d\n" ,
				frompc, p->tos[toindex].selfpc,
				p->tos[toindex].count);
			write(log, dbuf, len);
#endif
			rawarc.raw_frompc = frompc;
			rawarc.raw_selfpc = p->tos[toindex].selfpc;
			rawarc.raw_count = p->tos[toindex].count;
			write(fd, &rawarc, sizeof rawarc);
		}
	}
	close(fd);
}

/*
 * Control profiling
 *	profiling is what mcount checks to see if
 *	all the data structures are ready.
 */
void
moncontrol(int mode)
{
	struct gmonparam *p = &_gmonparam;

	if (mode) {
		/* start */
		profil((char *)p->kcount, p->kcountsize, p->lowpc,
		    s_scale);
		p->state = GMON_PROF_ON;
	} else {
		/* stop */
		profil((char *)0, 0, 0, 0);
		p->state = GMON_PROF_OFF;
	}
}


