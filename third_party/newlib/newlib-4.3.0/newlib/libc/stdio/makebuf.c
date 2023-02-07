/*
 * Copyright (c) 1990, 2007 The Regents of the University of California.
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
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/unistd.h>
#include "local.h"

#define _DEFAULT_ASPRINTF_BUFSIZE 64

/*
 * Allocate a file buffer, or switch to unbuffered I/O.
 * Per the ANSI C standard, ALL tty devices default to line buffered.
 *
 * As a side effect, we set __SOPT or __SNPT (en/dis-able fseek
 * optimization) right after the _fstat() that finds the buffer size.
 */

void
__smakebuf_r (struct _reent *ptr,
       register FILE *fp)
{
  register void *p;
  int flags;
  size_t size;
  int couldbetty;

  if (fp->_flags & __SNBF)
    {
      fp->_bf._base = fp->_p = fp->_nbuf;
      fp->_bf._size = 1;
      return;
    }
  flags = __swhatbuf_r (ptr, fp, &size, &couldbetty);
  if ((p = _malloc_r (ptr, size)) == NULL)
    {
      if (!(fp->_flags & __SSTR))
	{
	  fp->_flags = (fp->_flags & ~__SLBF) | __SNBF;
	  fp->_bf._base = fp->_p = fp->_nbuf;
	  fp->_bf._size = 1;
	}
    }
  else
    {
      fp->_flags |= __SMBF;
      fp->_bf._base = fp->_p = (unsigned char *) p;
      fp->_bf._size = size;
      if (couldbetty && _isatty_r (ptr, fp->_file))
	fp->_flags = (fp->_flags & ~__SNBF) | __SLBF;
      fp->_flags |= flags;
    }
}

/*
 * Internal routine to determine `proper' buffering for a file.
 */
int
__swhatbuf_r (struct _reent *ptr,
	FILE *fp,
	size_t *bufsize,
	int *couldbetty)
{
#ifdef _FSEEK_OPTIMIZATION
  const int snpt = __SNPT;
#else
  const int snpt = 0;
#endif

#ifdef __USE_INTERNAL_STAT64
  struct stat64 st;

  if (fp->_file < 0 || _fstat64_r (ptr, fp->_file, &st) < 0)
#else
  struct stat st;

  if (fp->_file < 0 || _fstat_r (ptr, fp->_file, &st) < 0)
#endif
    {
      *couldbetty = 0;
      /* Check if we are be called by asprintf family for initial buffer.  */
      if (fp->_flags & __SMBF)
        *bufsize = _DEFAULT_ASPRINTF_BUFSIZE;
      else
        *bufsize = BUFSIZ;
      return (0);
    }

  /* could be a tty iff it is a character device */
  *couldbetty = S_ISCHR(st.st_mode);
#ifdef HAVE_BLKSIZE
  if (st.st_blksize > 0)
    {
      /*
       * Optimise fseek() only if it is a regular file.  (The test for
       * __sseek is mainly paranoia.)  It is safe to set _blksize
       * unconditionally; it will only be used if __SOPT is also set.
       */
      *bufsize = st.st_blksize;
      fp->_blksize = st.st_blksize;
      return ((st.st_mode & S_IFMT) == S_IFREG ?  __SOPT : snpt);
    }
#endif
  *bufsize = BUFSIZ;
  return (snpt);
}
