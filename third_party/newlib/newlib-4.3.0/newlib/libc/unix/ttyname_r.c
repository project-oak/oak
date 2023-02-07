#ifndef _NO_TTYNAME
/*
 * Copyright (c) 1988 The Regents of the University of California.
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
 * 4. Neither the name of the University nor the names of its contributors
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

#include "ttyname.h"

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <dirent.h>
#include <unistd.h>
#include <string.h>
#include <paths.h>
#include <_syslist.h>
#include <errno.h>

/*
 *  ttyname_r() - POSIX 1003.1b 4.7.2 - Determine Terminal Device Name
 */
int
 ttyname_r (int fd,
	char   *name,
	size_t  namesize)
{
  struct stat sb;
  struct dirent *dirp;
  DIR *dp;
  struct stat dsb;
  char buf[TTYNAME_BUFSIZE];

  /* Must be a terminal. */
  if (!isatty(fd))
    return ENOTTY;

  /* Must be a character device. */
  if (fstat (fd, &sb) || !S_ISCHR (sb.st_mode))
    return ENOTTY;

  if ((dp = opendir (_PATH_DEV)) == NULL)
    return EBADF;

  strcpy(buf, _PATH_DEV);
  while ((dirp = readdir (dp)) != NULL)
    {
      if (dirp->d_ino != sb.st_ino)
	continue;
      strcpy (buf + sizeof (_PATH_DEV) - 1, dirp->d_name);
      if (stat (buf, &dsb) || sb.st_dev != dsb.st_dev ||
	  sb.st_ino != dsb.st_ino)
	continue;
      (void) closedir (dp);
      if(strlen(buf) < namesize)  /* < to account for terminating null */
	{
	strcpy(name, buf);
	return 0;
	}
      else
	{
	return ERANGE;
	}
    }
  (void) closedir (dp);
  return EBADF;
}

#endif /* !_NO_TTYNAME  */
