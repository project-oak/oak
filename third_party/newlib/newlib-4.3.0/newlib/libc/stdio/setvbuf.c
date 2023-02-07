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

/*
FUNCTION
<<setvbuf>>---specify file or stream buffering

INDEX
	setvbuf

SYNOPSIS
	#include <stdio.h>
	int setvbuf(FILE *<[fp]>, char *<[buf]>,
	            int <[mode]>, size_t <[size]>);

DESCRIPTION
Use <<setvbuf>> to specify what kind of buffering you want for the
file or stream identified by <[fp]>, by using one of the following
values (from <<stdio.h>>) as the <[mode]> argument:

o+
o _IONBF
Do not use a buffer: send output directly to the host system for the
file or stream identified by <[fp]>.

o _IOFBF
Use full output buffering: output will be passed on to the host system
only when the buffer is full, or when an input operation intervenes.

o _IOLBF
Use line buffering: pass on output to the host system at every
newline, as well as when the buffer is full, or when an input
operation intervenes.
o-

Use the <[size]> argument to specify how large a buffer you wish.  You
can supply the buffer itself, if you wish, by passing a pointer to a
suitable area of memory as <[buf]>.  Otherwise, you may pass <<NULL>>
as the <[buf]> argument, and <<setvbuf>> will allocate the buffer.

WARNINGS
You may only use <<setvbuf>> before performing any file operation other
than opening the file.

If you supply a non-null <[buf]>, you must ensure that the associated
storage continues to be available until you close the stream
identified by <[fp]>.

RETURNS
A <<0>> result indicates success, <<EOF>> failure (invalid <[mode]> or
<[size]> can cause failure).

PORTABILITY
Both ANSI C and the System V Interface Definition (Issue 2) require
<<setvbuf>>. However, they differ on the meaning of a <<NULL>> buffer
pointer: the SVID issue 2 specification says that a <<NULL>> buffer
pointer requests unbuffered output.  For maximum portability, avoid
<<NULL>> buffer pointers.

Both specifications describe the result on failure only as a
nonzero value.

Supporting OS subroutines required: <<close>>, <<fstat>>, <<isatty>>,
<<lseek>>, <<read>>, <<sbrk>>, <<write>>.
*/

#include <_ansi.h>
#include <stdio.h>
#include <stdlib.h>
#include "local.h"

/*
 * Set one of the three kinds of buffering, optionally including a buffer.
 */

int
setvbuf (register FILE * fp,
       char *buf,
       register int mode,
       register size_t size)
{
  int ret = 0;
  struct _reent *reent = _REENT;
  size_t iosize;
  int ttyflag;

  CHECK_INIT (reent, fp);

  /*
   * Verify arguments.  The `int' limit on `size' is due to this
   * particular implementation.  Note, buf and size are ignored
   * when setting _IONBF.
   */
  if (mode != _IONBF)
    if ((mode != _IOFBF && mode != _IOLBF) || (int)(_POINTER_INT) size < 0)
      return (EOF);


  /*
   * Write current buffer, if any; drop read count, if any.
   * Make sure putc() will not think fp is line buffered.
   * Free old buffer if it was from malloc().  Clear line and
   * non buffer flags, and clear malloc flag.
   */
  _newlib_flockfile_start (fp);
  _fflush_r (reent, fp);
  if (HASUB(fp))
    FREEUB(reent, fp);
  fp->_r = fp->_lbfsize = 0;
  if (fp->_flags & __SMBF)
    _free_r (reent, (void *) fp->_bf._base);
  fp->_flags &= ~(__SLBF | __SNBF | __SMBF | __SOPT | __SNPT | __SEOF);

  if (mode == _IONBF)
    goto nbf;

  /*
   * Find optimal I/O size for seek optimization.  This also returns
   * a `tty flag' to suggest that we check isatty(fd), but we do not
   * care since our caller told us how to buffer.
   */
  fp->_flags |= __swhatbuf_r (reent, fp, &iosize, &ttyflag);
  if (size == 0)
    {
      buf = NULL;
      size = iosize;
    }

  /* Allocate buffer if needed. */
  if (buf == NULL)
    {
      if ((buf = malloc (size)) == NULL)
	{
	  /*
	   * Unable to honor user's request.  We will return
	   * failure, but try again with file system size.
	   */
	  ret = EOF;
	  if (size != iosize)
	    {
	      size = iosize;
	      buf = malloc (size);
	    }
	}
      if (buf == NULL)
        {
          /* No luck; switch to unbuffered I/O. */
nbf:
          fp->_flags |= __SNBF;
          fp->_w = 0;
          fp->_bf._base = fp->_p = fp->_nbuf;
          fp->_bf._size = 1;
          _newlib_flockfile_exit (fp);
          return (ret);
        }
      fp->_flags |= __SMBF;
    }

  /*
   * We're committed to buffering from here, so make sure we've
   * registered to flush buffers on exit.
   */
  if (!_REENT_CLEANUP(reent))
    __sinit(reent);

#ifdef _FSEEK_OPTIMIZATION
  /*
   * Kill any seek optimization if the buffer is not the
   * right size.
   *
   * SHOULD WE ALLOW MULTIPLES HERE (i.e., ok iff (size % iosize) == 0)?
   */
  if (size != iosize)
     fp->_flags |= __SNPT;
#endif

  /*
   * Fix up the FILE fields, and set __cleanup for output flush on
   * exit (since we are buffered in some way).
   */
  if (mode == _IOLBF)
    fp->_flags |= __SLBF;
  fp->_bf._base = fp->_p = (unsigned char *) buf;
  fp->_bf._size = size;
  /* fp->_lbfsize is still 0 */
  if (fp->_flags & __SWR)
    {
      /*
       * Begin or continue writing: see __swsetup().  Note
       * that __SNBF is impossible (it was handled earlier).
       */
      if (fp->_flags & __SLBF)
	{
	  fp->_w = 0;
	  fp->_lbfsize = -fp->_bf._size;
	}
      else
        fp->_w = size;
    }
  else
    {
      /* begin/continue reading, or stay in intermediate state */
      fp->_w = 0;
    }

  _newlib_flockfile_end (fp);
  return 0;
}
