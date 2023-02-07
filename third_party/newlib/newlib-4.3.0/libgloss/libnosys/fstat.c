/*
 * Stub version of fstat.
 */

#include "config.h"
#include <_ansi.h>
#include <_syslist.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <errno.h>
#undef errno
extern int errno;
#include "warning.h"

int
_fstat (int          fildes,
        struct stat *st)
{
  errno = ENOSYS;
  return -1;
}

stub_warning(_fstat)
