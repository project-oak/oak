/*-
 * Copyright (c) 1991, 2000 The Regents of the University of California.
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

/*
 * This is a modified gmon.c by J.W.Hawtin <oolon@ankh.org>,
 * 14/8/96 based on the original gmon.c in GCC and the hacked version
 * solaris 2 sparc version (config/sparc/gmon-sol.c) by Mark Eichin. To do
 * process profiling on solaris 2.X X86
 *
 * It must be used in conjunction with sol2-gc1.asm, which is used to start
 * and stop process monitoring.
 *
 * Differences.
 *
 * On Solaris 2 _mcount is called by library functions not mcount, so support
 * has been added for both.
 *
 * Also the prototype for profil() is different
 *
 * Solaris 2 does not seem to have char *minbrk which allows the setting of
 * the minimum SBRK region so this code has been removed and lets pray malloc
 * does not mess it up.
 *
 * Notes
 *
 * This code could easily be integrated with the original gmon.c and perhaps
 * should be.
 */

#ifndef lint
static char sccsid[] = "@(#)gmon.c	5.3 (Berkeley) 5/22/91";
#endif /* not lint */

#define DEBUG
#ifdef DEBUG
#include <stdio.h>
#endif

#include "cygmon-gmon.h"

/*
 *	froms is actually a bunch of unsigned shorts indexing tos
 */
static int		profiling = 3;
static unsigned short	*froms;
static struct tostruct	*tos = 0;
static long		tolimit = 0;
static char		*s_lowpc = 0;
static char		*s_highpc = 0;
static unsigned long	s_textsize = 0;

static int	ssiz;
static char	*sbuf;
static int	s_scale;
    /* see profil(2) where this is describe (incorrectly) */
#define		SCALE_1_TO_1	0x10000L

#define	MSG "No space for profiling buffer(s)\n"

extern int errno;

int
monstartup(lowpc, highpc)
     char	*lowpc;
     char	*highpc;
{
  int		monsize;
  char		*buffer;
  register int	o;

	/*
	 *	round lowpc and highpc to multiples of the density we're using
	 *	so the rest of the scaling (here and in gprof) stays in ints.
	 */
  lowpc = (char *)
    ROUNDDOWN((unsigned)lowpc, HISTFRACTION*sizeof(HISTCOUNTER));
  s_lowpc = lowpc;
  highpc = (char *)
    ROUNDUP((unsigned)highpc, HISTFRACTION*sizeof(HISTCOUNTER));
  s_highpc = highpc;
  s_textsize = highpc - lowpc;
  monsize = (s_textsize / HISTFRACTION) + sizeof(struct phdr);
  buffer = (char *) sbrk (monsize);
  if (buffer == (char *) -1) 
    {
      write (2, MSG , sizeof(MSG));
      return;
    }
  bzero (buffer, monsize);
  froms = (unsigned short *) sbrk (s_textsize / HASHFRACTION);
  if (froms == (unsigned short *) -1)
    {
      write(2, MSG, sizeof(MSG));
      froms = 0;
      return;
    }
  bzero (froms, s_textsize / HASHFRACTION);
  tolimit = s_textsize * ARCDENSITY / 100;
  if (tolimit < MINARCS) 
    {
      tolimit = MINARCS;
    }
  else 
    {
      if (tolimit > 65534) 
	{
	  tolimit = 65534;
	}
    }
  tos = (struct tostruct *) sbrk( tolimit * sizeof( struct tostruct ) );
  if (tos == (struct tostruct *) -1)
    {
      write (2, MSG, sizeof(MSG));
      froms = 0;
      tos = 0;
      return;
    }
  bzero (tos, tolimit * sizeof( struct tostruct ) );
  tos[0].link = 0;
  sbuf = buffer;
  ssiz = monsize;
  ( (struct phdr *) buffer ) -> lpc = lowpc;
  ( (struct phdr *) buffer ) -> hpc = highpc;
  ( (struct phdr *) buffer ) -> ncnt = ssiz;
  monsize -= sizeof(struct phdr);
  if ( monsize <= 0 )
    return;
  o = highpc - lowpc;
  if (monsize < o)
    {
	s_scale = ( (float) monsize / o ) * SCALE_1_TO_1;
    }
  else
    s_scale = SCALE_1_TO_1;
  moncontrol (1);
}

void
_mcleanup()
{
  int		fd;
  int		fromindex;
  int		endfrom;
  char		*frompc;
  int		toindex;
  struct rawarc	rawarc;

  moncontrol (0);
  profil_write (1, sbuf, ssiz);

  endfrom = s_textsize / (HASHFRACTION * sizeof(*froms));
  for ( fromindex = 0 ; fromindex < endfrom ; fromindex++ ) 
    {
      if ( froms[fromindex] == 0 ) 
	{
	  continue;
	}
      frompc = s_lowpc + (fromindex * HASHFRACTION * sizeof(*froms));
      for (toindex=froms[fromindex]; toindex!=0; toindex=tos[toindex].link) 
	{
	  rawarc.raw_frompc = (unsigned long) frompc;
	  rawarc.raw_selfpc = (unsigned long) tos[toindex].selfpc;
	  rawarc.raw_count = tos[toindex].count;
	  profil_write (2, &rawarc, sizeof (rawarc));
	}
    }
  profil_write (3, 0, 0);
}

static char already_setup = 0;

_mcount()
{
  register char			*selfpc;
  register unsigned short	*frompcindex;
  register struct tostruct	*top;
  register struct tostruct	*prevtop;
  register long			toindex;

  /*
   *	find the return address for mcount,
   *	and the return address for mcount's caller.
   */

  /* selfpc = pc pushed by mcount call.
     This identifies the function that was just entered.  */
  selfpc = (void *) __builtin_return_address (0);
  /* frompcindex = pc in preceding frame.
     This identifies the caller of the function just entered.  */
  frompcindex = (void *) __builtin_return_address (1);

  if (! already_setup) 
    {
      extern _etext();
      extern _ftext();
      already_setup = 1;
      monstartup(_ftext, _etext);
      atexit(_mcleanup);
    }
  /*
   *	check that we are profiling
   *	and that we aren't recursively invoked.
   */
  if (profiling) 
    {
      goto out;
    }
  profiling++;
  /*
   *	check that frompcindex is a reasonable pc value.
   *	for example:	signal catchers get called from the stack,
   *			not from text space.  too bad.
   */
  frompcindex = (unsigned short *)((long)frompcindex - (long)s_lowpc);
  if ((unsigned long)frompcindex > s_textsize) 
    {
      goto done;
    }
  frompcindex =
    &froms[((long)frompcindex) / (HASHFRACTION * sizeof(*froms))];
  toindex = *frompcindex;
  if (toindex == 0) 
    {
      /*
       *	first time traversing this arc
       */
      toindex = ++tos[0].link;
      if (toindex >= tolimit) 
	{
	  goto overflow;
	}
      *frompcindex = toindex;
      top = &tos[toindex];
      top->selfpc = selfpc;
      top->count = 1;
      top->link = 0;
      goto done;
    }
  top = &tos[toindex];
  if (top->selfpc == selfpc) 
    {
      /*
       *	arc at front of chain; usual case.
       */
      top->count++;
      goto done;
    }
  /*
   *	have to go looking down chain for it.
   *	top points to what we are looking at,
   *	prevtop points to previous top.
   *	we know it is not at the head of the chain.
   */
  for (; /* goto done */; ) 
    {
      if (top->link == 0) 
	{
	  /*
	   *	top is end of the chain and none of the chain
	   *	had top->selfpc == selfpc.
	   *	so we allocate a new tostruct
	   *	and link it to the head of the chain.
	   */
	  toindex = ++tos[0].link;
	  if (toindex >= tolimit) 
	    {
	      goto overflow;
	    }
	  top = &tos[toindex];
	  top->selfpc = selfpc;
	  top->count = 1;
	  top->link = *frompcindex;
	  *frompcindex = toindex;
	  goto done;
	}
      /*
       *	otherwise, check the next arc on the chain.
       */
      prevtop = top;
      top = &tos[top->link];
      if (top->selfpc == selfpc) 
	{
	  /*
	   *	there it is.
	   *	increment its count
	   *	move it to the head of the chain.
	   */
	  top->count++;
	  toindex = prevtop->link;
	  prevtop->link = top->link;
	  top->link = *frompcindex;
	  *frompcindex = toindex;
	  goto done;
	}
    }
done:
  profiling--;
  /* and fall through */
out:
  return;		/* normal return restores saved registers */

overflow:
  profiling++; /* halt further profiling */
#   define	TOLIMIT	"mcount: tos overflow\n"
  write (2, TOLIMIT, sizeof(TOLIMIT));
  goto out;
}

/*
 * Control profiling
 *	profiling is what mcount checks to see if
 *	all the data structures are ready.
 */
moncontrol(mode)
    int mode;
{
  if (mode)
    {
      /* start */
      profil((unsigned short *)(sbuf + sizeof(struct phdr)),
	     ssiz - sizeof(struct phdr),
	     (int)s_lowpc, s_scale);
      
      profiling = 0;
    }
  else 
    {
      /* stop */
      profil((unsigned short *)0, 0, 0, 0);
      profiling = 3;
    }
}
