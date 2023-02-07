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
/* This code was copied from asprintf.c */
/* doc in siprintf.c */

#include <_ansi.h>
#include <reent.h>
#include <stdio.h>
#include <stdarg.h>
#include <limits.h>
#include "local.h"

int
_asiprintf_r (struct _reent *ptr,
       char **strp,
       const char *fmt, ...)
{
  int ret;
  va_list ap;
  FILE f;

  /* mark a zero-length reallocatable buffer */
  f._flags = __SWR | __SSTR | __SMBF;
  f._bf._base = f._p = NULL;
  f._bf._size = f._w = 0;
  f._file = -1;  /* No file. */
  va_start (ap, fmt);
  ret = _svfiprintf_r (ptr, &f, fmt, ap);
  va_end (ap);
  if (ret >= 0)
    {
      *f._p = 0;
      *strp = (char *) f._bf._base;
    }
  return (ret);
}

#ifndef _REENT_ONLY

int
asiprintf (char **strp,
       const char *fmt, ...)
{
  int ret;
  va_list ap;
  FILE f;

  /* mark a zero-length reallocatable buffer */
  f._flags = __SWR | __SSTR | __SMBF;
  f._bf._base = f._p = NULL;
  f._bf._size = f._w = 0;
  f._file = -1;  /* No file. */
  va_start (ap, fmt);
  ret = _svfiprintf_r (_REENT, &f, fmt, ap);
  va_end (ap);
  if (ret >= 0)
    {
      *f._p = 0;
      *strp = (char *) f._bf._base;
    }
  return (ret);
}

#endif /* ! _REENT_ONLY */
