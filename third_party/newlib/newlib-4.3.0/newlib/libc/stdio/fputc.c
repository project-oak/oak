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
<<fputc>>, <<fputc_unlocked>>---write a character on a stream or file

INDEX
	fputc
INDEX
	fputc_unlocked
INDEX
	_fputc_r
INDEX
	_fputc_unlocked_r

SYNOPSIS
	#include <stdio.h>
	int fputc(int <[ch]>, FILE *<[fp]>);

	#define _BSD_SOURCE
	#include <stdio.h>
	int fputc_unlocked(int <[ch]>, FILE *<[fp]>);

	#include <stdio.h>
	int _fputc_r(struct _rent *<[ptr]>, int <[ch]>, FILE *<[fp]>);

	#include <stdio.h>
	int _fputc_unlocked_r(struct _rent *<[ptr]>, int <[ch]>, FILE *<[fp]>);

DESCRIPTION
<<fputc>> converts the argument <[ch]> from an <<int>> to an
<<unsigned char>>, then writes it to the file or stream identified by
<[fp]>.

If the file was opened with append mode (or if the stream cannot
support positioning), then the new character goes at the end of the
file or stream.  Otherwise, the new character is written at the
current value of the position indicator, and the position indicator
oadvances by one.

For a macro version of this function, see <<putc>>.

<<fputc_unlocked>> is a non-thread-safe version of <<fputc>>.
<<fputc_unlocked>> may only safely be used within a scope
protected by flockfile() (or ftrylockfile()) and funlockfile().  This
function may safely be used in a multi-threaded program if and only
if they are called while the invoking thread owns the (FILE *)
object, as is the case after a successful call to the flockfile() or
ftrylockfile() functions.  If threads are disabled, then
<<fputc_unlocked>> is equivalent to <<fputc>>.

The <<_fputc_r>> and <<_fputc_unlocked_r>> functions are simply reentrant
versions of the above that take an additional reentrant structure
argument: <[ptr]>.

RETURNS
If successful, <<fputc>> returns its argument <[ch]>.  If an error
intervenes, the result is <<EOF>>.  You can use `<<ferror(<[fp]>)>>' to
query for errors.

PORTABILITY
<<fputc>> is required by ANSI C.

<<fputc_unlocked>> is a BSD extension also provided by GNU libc.

Supporting OS subroutines required: <<close>>, <<fstat>>, <<isatty>>,
<<lseek>>, <<read>>, <<sbrk>>, <<write>>.
*/

#include <_ansi.h>
#include <stdio.h>
#include "local.h"

int
_fputc_r (struct _reent *ptr,
       int ch,
       FILE * file)
{
  int result;
  CHECK_INIT(ptr, file);
   _newlib_flockfile_start (file);
  result = _putc_r (ptr, ch, file);
  _newlib_flockfile_end (file);
  return result;
}

#ifndef _REENT_ONLY
int
fputc (int ch,
       FILE * file)
{
#if !defined(__OPTIMIZE_SIZE__) && !defined(PREFER_SIZE_OVER_SPEED)
  int result;
  struct _reent *reent = _REENT;

  CHECK_INIT(reent, file);
   _newlib_flockfile_start (file);
  result = _putc_r (reent, ch, file);
  _newlib_flockfile_end (file);
  return result;
#else
  return _fputc_r (_REENT, ch, file);
#endif
}
#endif /* !_REENT_ONLY */
