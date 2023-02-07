#ifndef HAVE_OPENDIR

/*
 * Copyright (c) 1983 Regents of the University of California.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#if defined(LIBC_SCCS) && !defined(lint)
static char sccsid[] = "@(#)readdir.c	5.7 (Berkeley) 6/1/90";
#endif /* LIBC_SCCS and not lint */

#include <dirent.h>

extern int getdents (int fd, void *dp, int count);

/*
 * get next entry in a directory.
 */
struct dirent *
readdir (register DIR *dirp)
{
  register struct dirent *dp;
 
#ifdef HAVE_DD_LOCK
  __lock_acquire_recursive(dirp->dd_lock);
#endif
 
  for (;;) {
    if (dirp->dd_loc == 0) {
      dirp->dd_size = getdents (dirp->dd_fd,
				dirp->dd_buf,
				dirp->dd_len);
      
      if (dirp->dd_size <= 0) {
#ifdef HAVE_DD_LOCK
        __lock_release_recursive(dirp->dd_lock);
#endif
	return NULL;
      }
    }
    if (dirp->dd_loc >= dirp->dd_size) {
      dirp->dd_loc = 0;
      continue;
    }
    dp = (struct dirent *)(dirp->dd_buf + dirp->dd_loc);
    if (dp->d_reclen <= 0 ||
	dp->d_reclen > dirp->dd_len + 1 - dirp->dd_loc) {
#ifdef HAVE_DD_LOCK
      __lock_release_recursive(dirp->dd_lock);
#endif
      return NULL;
    }
    dirp->dd_loc += dp->d_reclen;
    if (dp->d_ino == 0)
      continue;
#ifdef HAVE_DD_LOCK
    __lock_release_recursive(dirp->dd_lock);
#endif
    return (dp);
  }
}

#endif /* ! HAVE_OPENDIR */
