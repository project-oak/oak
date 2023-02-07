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
#include <reent.h>
#include <stdio.h>
#include <sys/types.h>
#include <fcntl.h>
#include <sys/unistd.h>
#include "local.h"

/*
 * Small standard I/O/seek/close functions.
 * These maintain the `known seek offset' for seek optimisation.
 */

_READ_WRITE_RETURN_TYPE
__sread (struct _reent *ptr,
       void *cookie,
       char *buf,
       _READ_WRITE_BUFSIZE_TYPE n)
{
  register FILE *fp = (FILE *) cookie;
  register ssize_t ret;

#ifdef __SCLE
  int oldmode = 0;
  if (fp->_flags & __SCLE)
    oldmode = setmode (fp->_file, O_BINARY);
#endif

  ret = _read_r (ptr, fp->_file, buf, n);

#ifdef __SCLE
  if (oldmode)
    setmode (fp->_file, oldmode);
#endif

  /* If the read succeeded, update the current offset.  */

  if (ret >= 0)
    fp->_offset += ret;
  else
    fp->_flags &= ~__SOFF;	/* paranoia */
  return ret;
}

/* Dummy function used in sscanf/swscanf. */
_READ_WRITE_RETURN_TYPE
__seofread (struct _reent *_ptr,
       void *cookie,
       char *buf,
       _READ_WRITE_BUFSIZE_TYPE len)
{
  return 0;
}

_READ_WRITE_RETURN_TYPE
__swrite (struct _reent *ptr,
       void *cookie,
       char const *buf,
       _READ_WRITE_BUFSIZE_TYPE n)
{
  register FILE *fp = (FILE *) cookie;
  ssize_t w;
#ifdef __SCLE
  int oldmode=0;
#endif

  if (fp->_flags & __SAPP)
    _lseek_r (ptr, fp->_file, (_off_t) 0, SEEK_END);
  fp->_flags &= ~__SOFF;	/* in case O_APPEND mode is set */

#ifdef __SCLE
  if (fp->_flags & __SCLE)
    oldmode = setmode (fp->_file, O_BINARY);
#endif

  w = _write_r (ptr, fp->_file, buf, n);

#ifdef __SCLE
  if (oldmode)
    setmode (fp->_file, oldmode);
#endif

  return w;
}

_fpos_t
__sseek (struct _reent *ptr,
       void *cookie,
       _fpos_t offset,
       int whence)
{
  register FILE *fp = (FILE *) cookie;
  register _off_t ret;

  ret = _lseek_r (ptr, fp->_file, (_off_t) offset, whence);
  if (ret == -1L)
    fp->_flags &= ~__SOFF;
  else
    {
      fp->_flags |= __SOFF;
      fp->_offset = ret;
    }
  return ret;
}

int
__sclose (struct _reent *ptr,
       void *cookie)
{
  FILE *fp = (FILE *) cookie;

  return _close_r (ptr, fp->_file);
}

#ifdef __SCLE
int
__stextmode (int fd)
{
#ifdef __CYGWIN__
  extern int _cygwin_istext_for_stdio (int);
  return _cygwin_istext_for_stdio (fd);
#else
  return 0;
#endif
}
#endif
