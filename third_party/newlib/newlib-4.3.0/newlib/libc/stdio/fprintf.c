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
/* doc in sprintf.c */

#include <_ansi.h>
#include <reent.h>
#include <stdio.h>
#include <stdarg.h>

int
_fprintf_r (struct _reent *ptr,
       FILE *__restrict fp,
       const char *__restrict fmt, ...)
{
  int ret;
  va_list ap;

  va_start (ap, fmt);
  ret = _vfprintf_r (ptr, fp, fmt, ap);
  va_end (ap);
  return ret;
}

#ifdef _NANO_FORMATTED_IO
int
_fiprintf_r (struct _reent *, FILE *, const char *, ...)
       _ATTRIBUTE ((__alias__("_fprintf_r")));
#endif

#ifndef _REENT_ONLY

int
fprintf (FILE *__restrict fp,
       const char *__restrict fmt, ...)
{
  int ret;
  va_list ap;

  va_start (ap, fmt);
  ret = _vfprintf_r (_REENT, fp, fmt, ap);
  va_end (ap);
  return ret;
}

#ifdef _NANO_FORMATTED_IO
int
fiprintf (FILE *, const char *, ...)
       _ATTRIBUTE ((__alias__("fprintf")));
#endif
#endif /* ! _REENT_ONLY */
