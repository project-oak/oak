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

#include <_ansi.h>
#include <reent.h>
#include <stdio.h>
#include <stdarg.h>
#include "local.h"

#ifndef _REENT_ONLY

int
iscanf(const char *fmt, ...)
{
  int ret;
  va_list ap;

  _REENT_SMALL_CHECK_INIT (_REENT);
  va_start (ap, fmt);
  ret = __svfiscanf_r (_REENT, _stdin_r (_REENT), fmt, ap);
  va_end (ap);
  return ret;
}

#endif /* !_REENT_ONLY */

int
_iscanf_r(struct _reent *ptr, const char *fmt, ...)
{
  int ret;
  va_list ap;

  _REENT_SMALL_CHECK_INIT (ptr);
  va_start (ap, fmt);
  ret = __svfiscanf_r (ptr, _stdin_r (ptr), fmt, ap);
  va_end (ap);
  return (ret);
}

