/*
 * Stub version of fork.
 */

#include "config.h"
#include <_ansi.h>
#include <_syslist.h>
#include <errno.h>
#undef errno
extern int errno;
#include "warning.h"

int
_fork (void)
{
  errno = ENOSYS;
  return -1;
}

stub_warning(_fork)
