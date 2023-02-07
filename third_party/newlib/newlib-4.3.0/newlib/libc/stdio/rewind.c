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
<<rewind>>---reinitialize a file or stream

INDEX
	rewind
INDEX
	_rewind_r

SYNOPSIS
	#include <stdio.h>
	void rewind(FILE *<[fp]>);
	void _rewind_r(struct _reent *<[ptr]>, FILE *<[fp]>);

DESCRIPTION
<<rewind>> returns the file position indicator (if any) for the file
or stream identified by <[fp]> to the beginning of the file.  It also
clears any error indicator and flushes any pending output.

RETURNS
<<rewind>> does not return a result.

PORTABILITY
ANSI C requires <<rewind>>.

No supporting OS subroutines are required.
*/

#if defined(LIBC_SCCS) && !defined(lint)
static char sccsid[] = "%W% (Berkeley) %G%";
#endif /* LIBC_SCCS and not lint */

#include <_ansi.h>
#include <reent.h>
#include <stdio.h>

void
_rewind_r (struct _reent * ptr,
       register FILE * fp)
{
  (void) _fseek_r (ptr, fp, 0L, SEEK_SET);
  clearerr (fp);
}

#ifndef _REENT_ONLY

void
rewind (register FILE * fp)
{
  _rewind_r (_REENT, fp);
}

#endif /* !_REENT_ONLY */
