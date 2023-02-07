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
<<gets>>---get character string (obsolete, use <<fgets>> instead)

INDEX
	gets
INDEX
	_gets_r

SYNOPSIS
        #include <stdio.h>

	char *gets(char *<[buf]>);

	char *_gets_r(struct _reent *<[reent]>, char *<[buf]>);

DESCRIPTION
	Reads characters from standard input until a newline is found.
	The characters up to the newline are stored in <[buf]>. The
	newline is discarded, and the buffer is terminated with a 0.

	This is a @emph{dangerous} function, as it has no way of checking
	the amount of space available in <[buf]>. One of the attacks
	used by the Internet Worm of 1988 used this to overrun a
	buffer allocated on the stack of the finger daemon and
	overwrite the return address, causing the daemon to execute
	code downloaded into it over the connection.

	The alternate function <<_gets_r>> is a reentrant version.  The extra
	argument <[reent]> is a pointer to a reentrancy structure.


RETURNS
	<<gets>> returns the buffer passed to it, with the data filled
	in. If end of file occurs with some data already accumulated,
	the data is returned with no other indication. If end of file
	occurs with no data in the buffer, NULL is returned.

Supporting OS subroutines required: <<close>>, <<fstat>>, <<isatty>>,
<<lseek>>, <<read>>, <<sbrk>>, <<write>>.
*/

#include <_ansi.h>
#include <reent.h>
#include <stdio.h>
#include "local.h"

char *
_gets_r (struct _reent *ptr,
       char *buf)
{
  register int c;
  register char *s = buf;
  FILE *fp;

  _REENT_SMALL_CHECK_INIT (ptr);
  fp = _stdin_r (ptr);
  CHECK_INIT (ptr, fp);
  _newlib_flockfile_start (fp);
  while ((c = __sgetc_r (ptr, fp)) != '\n')
    if (c == EOF)
      if (s == buf)
	{
	  _newlib_flockfile_exit (fp);
	  return NULL;
	}
      else
	break;
    else
      *s++ = c;
  *s = 0;
  _newlib_flockfile_end (fp);
  return buf;
}

#ifndef _REENT_ONLY

char *
gets (char *buf)
{
  return _gets_r (_REENT, buf);
}

#endif
