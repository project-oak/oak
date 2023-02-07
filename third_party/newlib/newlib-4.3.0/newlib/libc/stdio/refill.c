/*
 * Copyright (c) 1990 The Regents of the University of California.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms are permitted
 * provided that the above copyright notice and this paragraph are
 * duplicated in all such forms and that any documentation,
 * and/or other materials related to such
 * distribution and use acknowledge that the software was developed
 * by the University of California, Berkeley.  The name of the
 * University may not be used to endorse or promote products derived
 * from this software without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.
 */
/* No user fns here.  Pesch 15apr92. */

#include <_ansi.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include "local.h"

static int
lflush (struct _reent * ptr __unused, FILE *fp)
{
  if ((fp->_flags & (__SLBF | __SWR)) == (__SLBF | __SWR))
    return _fflush_r (_REENT, fp);
  return 0;
}

/*
 * Refill a stdio buffer.
 * Return EOF on eof or error, 0 otherwise.
 */

int
__srefill_r (struct _reent * ptr,
       register FILE * fp)
{
  /* make sure stdio is set up */

  CHECK_INIT (ptr, fp);

  ORIENT (fp, -1);

  fp->_r = 0;			/* largely a convenience for callers */

  /* SysV does not make this test; take it out for compatibility */
  if (fp->_flags & __SEOF)
    return EOF;

  /* if not already reading, have to be reading and writing */
  if ((fp->_flags & __SRD) == 0)
    {
      if ((fp->_flags & __SRW) == 0)
	{
	  _REENT_ERRNO(ptr) = EBADF;
	  fp->_flags |= __SERR;
	  return EOF;
	}
      /* switch to reading */
      if (fp->_flags & __SWR)
	{
	  if (_fflush_r (ptr, fp))
	    return EOF;
	  fp->_flags &= ~__SWR;
	  fp->_w = 0;
	  fp->_lbfsize = 0;
	}
      fp->_flags |= __SRD;
    }
  else
    {
      /*
       * We were reading.  If there is an ungetc buffer,
       * we must have been reading from that.  Drop it,
       * restoring the previous buffer (if any).  If there
       * is anything in that buffer, return.
       */
      if (HASUB (fp))
	{
	  FREEUB (ptr, fp);
	  if ((fp->_r = fp->_ur) != 0)
	    {
	      fp->_p = fp->_up;
	      return 0;
	    }
	}
    }

  if (fp->_bf._base == NULL)
    __smakebuf_r (ptr, fp);

  /*
   * Before reading from a line buffered or unbuffered file,
   * flush all line buffered output files, per the ANSI C
   * standard.
   */
  if (fp->_flags & (__SLBF | __SNBF))
    {
      /* Ignore this file in _fwalk_sglue to avoid potential deadlock. */
      short orig_flags = fp->_flags;
      fp->_flags = 1;
      (void) _fwalk_sglue (_GLOBAL_REENT, lflush, &__sglue);
      fp->_flags = orig_flags;

      /* Now flush this file without locking it. */
      if ((fp->_flags & (__SLBF|__SWR)) == (__SLBF|__SWR))
	__sflush_r (ptr, fp);
    }

  fp->_p = fp->_bf._base;
  fp->_r = fp->_read (ptr, fp->_cookie, (char *) fp->_p, fp->_bf._size);
  if (fp->_r <= 0)
    {
      if (fp->_r == 0)
	fp->_flags |= __SEOF;
      else
	{
	  fp->_r = 0;
	  fp->_flags |= __SERR;
	}
      return EOF;
    }
  return 0;
}
