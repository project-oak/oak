/* Reentrant versions of stat system call.  This implementation just
   calls the stat system call.  */

#include <reent.h>
#include <unistd.h>
#include <sys/stat.h>
#include <_syslist.h>

/* Some targets provides their own versions of these functions.  Those
   targets should define REENTRANT_SYSCALLS_PROVIDED in
   TARGET_CFLAGS.  */

#ifdef _REENT_ONLY
#ifndef REENTRANT_SYSCALLS_PROVIDED
#define REENTRANT_SYSCALLS_PROVIDED
#endif
#endif

#ifdef REENTRANT_SYSCALLS_PROVIDED

int _dummy_stat_syscalls = 1;

#else

/* We use the errno variable used by the system dependent layer.  */
#undef errno
extern int errno;

/*
FUNCTION
	<<_stat_r>>---Reentrant version of stat
	
INDEX
	_stat_r

SYNOPSIS
	#include <reent.h>
	int _stat_r(struct _reent *<[ptr]>,
		    const char *<[file]>, struct stat *<[pstat]>);

DESCRIPTION
	This is a reentrant version of <<stat>>.  It
	takes a pointer to the global data block, which holds
	<<errno>>.
*/

int
_stat_r (struct _reent *ptr,
     const char *file,
     struct stat *pstat)
{
  int ret;

  errno = 0;
  if ((ret = _stat (file, pstat)) == -1 && errno != 0)
    _REENT_ERRNO(ptr) = errno;
  return ret;
}

#endif /* ! defined (REENTRANT_SYSCALLS_PROVIDED) */
