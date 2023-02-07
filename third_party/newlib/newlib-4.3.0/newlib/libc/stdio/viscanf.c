/*-
 * Code created by modifying iscanf.c which has following copyright.
 *
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
<<viscanf>>, <<vfiscanf>>, <<vsiscanf>>---format argument list

INDEX
	viscanf
INDEX
	_viscanf_r
INDEX
	vfiscanf
INDEX
	_vfiscanf_r
INDEX
	vsiscanf
INDEX
	_vsiscanf_r

SYNOPSIS
	#include <stdio.h>
	#include <stdarg.h>
	int viscanf(const char *<[fmt]>, va_list <[list]>);
	int vfiscanf(FILE *<[fp]>, const char *<[fmt]>, va_list <[list]>);
	int vsiscanf(const char *<[str]>, const char *<[fmt]>, va_list <[list]>);

	int _viscanf_r(struct _reent *<[reent]>, const char *<[fmt]>, 
                       va_list <[list]>);
	int _vfiscanf_r(struct _reent *<[reent]>, FILE *<[fp]>, const char *<[fmt]>, 
                       va_list <[list]>);
	int _vsiscanf_r(struct _reent *<[reent]>, const char *<[str]>,
                       const char *<[fmt]>, va_list <[list]>);

DESCRIPTION
<<viscanf>>, <<vfiscanf>>, and <<vsiscanf>> are (respectively) variants
of <<iscanf>>, <<fiscanf>>, and <<siscanf>>.  They differ only in 
allowing their caller to pass the variable argument list as a 
<<va_list>> object (initialized by <<va_start>>) rather than 
directly accepting a variable number of arguments.

RETURNS
The return values are consistent with the corresponding functions:
<<viscanf>> returns the number of input fields successfully scanned,
converted, and stored; the return value does not include scanned
fields which were not stored.  

If <<viscanf>> attempts to read at end-of-file, the return value 
is <<EOF>>.

If no fields were stored, the return value is <<0>>.

The routines <<_viscanf_r>>, <<_vfiscanf_f>>, and <<_vsiscanf_r>> are
reentrant versions which take an additional first parameter which points to the
reentrancy structure.

PORTABILITY
These are newlib extensions.

Supporting OS subroutines required:
*/

#include <_ansi.h>
#include <reent.h>
#include <stdio.h>
#include <stdarg.h>
#include "local.h"

#ifndef _REENT_ONLY

int
viscanf (const char *fmt,
       va_list ap)
{
  struct _reent *reent = _REENT;

  _REENT_SMALL_CHECK_INIT (reent);
  return __svfiscanf_r (reent, _stdin_r (reent), fmt, ap);
}

#endif /* !_REENT_ONLY */

int
_viscanf_r (struct _reent *ptr,
       const char *fmt,
       va_list ap)
{
  _REENT_SMALL_CHECK_INIT (ptr);
  return __svfiscanf_r (ptr, _stdin_r (ptr), fmt, ap);
}

