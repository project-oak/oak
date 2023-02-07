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
/* No user fns here. Pesch 15apr92. */

#if defined(LIBC_SCCS) && !defined(lint)
static char sccsid[] = "%W% (Berkeley) %G%";
#endif /* LIBC_SCCS and not lint */

#include <_ansi.h>
#include <stdio.h>
#include <errno.h>
#include "local.h"

/*
 * Handle getc() when the buffer ran out:
 * Refill, then return the first character
 * in the newly-filled buffer.
 */

int
__srget_r (struct _reent *ptr,
       register FILE *fp)
{
  /* Ensure that any fake std stream is resolved before
     we call __srefill_r so we may access the true read buffer. */
  CHECK_INIT(ptr, fp);

  if (__srefill_r (ptr, fp) == 0)
    {
      fp->_r--;
      return *fp->_p++;
    }
  return EOF;
}

/* This function isn't any longer declared in stdio.h, but it's
   required for backward compatibility with applications built against
   earlier dynamically built newlib libraries. */
int
__srget (register FILE *fp)
{
  return __srget_r (_REENT, fp);
}
