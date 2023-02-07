/*
 * Copyright (c) 1983 Regents of the University of California.
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

#if defined(LIBC_SCCS) && !defined(lint)
static char sccsid[] = "@(#)telldir.c	5.9 (Berkeley) 2/23/91";
#endif /* LIBC_SCCS and not lint */

#include <sys/param.h>
#include <dirent.h>
#include <stdlib.h>
#include <unistd.h>

/*
 * The option SINGLEUSE may be defined to say that a telldir
 * cookie may be used only once before it is freed. This option
 * is used to avoid having memory usage grow without bound.
 */
#define SINGLEUSE

/*
 * One of these structures is malloced to describe the current directory
 * position each time telldir is called. It records the current magic 
 * cookie returned by getdirentries and the offset within the buffer
 * associated with that return value.
 */
struct ddloc {
	struct	ddloc *loc_next;/* next structure in list */
	long	loc_index;	/* key associated with structure */
	long	loc_seek;	/* magic cookie returned by getdirentries */
	long	loc_loc;	/* offset of entry in buffer */
};

#define	NDIRHASH	32	/* Num of hash lists, must be a power of 2 */
#define	LOCHASH(i)	((i)&(NDIRHASH-1))

static long	dd_loccnt;	/* Index of entry for sequential readdir's */
static struct	ddloc *dd_hash[NDIRHASH];   /* Hash list heads for ddlocs */

/*
 * return a pointer into a directory
 */
long
telldir(dirp)
	const DIR *dirp;
{
	register int index;
	register struct ddloc *lp;

	if ((lp = (struct ddloc *)malloc(sizeof(struct ddloc))) == NULL)
		return (-1);
	index = dd_loccnt++;
	lp->loc_index = index;
	lp->loc_seek = dirp->dd_seek;
	lp->loc_loc = dirp->dd_loc;
	lp->loc_next = dd_hash[LOCHASH(index)];
	dd_hash[LOCHASH(index)] = lp;
	return (index);
}

/*
 * seek to an entry in a directory.
 * Only values returned by "telldir" should be passed to seekdir.
 */
void
_seekdir(dirp, loc)
	register DIR *dirp;
	long loc;
{
	register struct ddloc *lp;
	register struct ddloc **prevlp;
	struct dirent *dp;
	extern long lseek();

	prevlp = &dd_hash[LOCHASH(loc)];
	lp = *prevlp;
	while (lp != NULL) {
		if (lp->loc_index == loc)
			break;
		prevlp = &lp->loc_next;
		lp = lp->loc_next;
	}
	if (lp == NULL)
		return;
	if (lp->loc_loc == dirp->dd_loc && lp->loc_seek == dirp->dd_seek)
		goto found;
	(void) lseek(dirp->dd_fd, lp->loc_seek, 0);
	dirp->dd_seek = lp->loc_seek;
	dirp->dd_loc = 0;
	while (dirp->dd_loc < lp->loc_loc) {
		dp = readdir(dirp);
		if (dp == NULL)
			break;
	}
found:
#ifdef SINGLEUSE
	*prevlp = lp->loc_next;
	free((caddr_t)lp);
#endif
}
