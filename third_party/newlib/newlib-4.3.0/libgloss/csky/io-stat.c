/*
 * io-stat.c -- 
 *
 * Copyright (c) 2006 CodeSourcery Inc
 *
 * The authors hereby grant permission to use, copy, modify, distribute,
 * and license this software and its documentation for any purpose, provided
 * that existing copyright notices are retained in all copies and that this
 * notice is included verbatim in any distributions. No written agreement,
 * license, or royalty fee is required for any of the authorized uses.
 * Modifications to this software may be copyrighted by their authors
 * and need not follow the licensing terms described here, provided that
 * the new terms are clearly indicated on the first page of each file where
 * they apply.
 */

#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <errno.h>
#define IO stat
#include "io.h"

/*
 * stat -- get file information
 * input parameters:
 *   0 : filename ptr
 *   1 : filename length
 *   2 : stat buf ptr
 * output parameters:
 *   0 : errno
 * result : r0
 */


int stat (const char *__restrict filename, struct stat *__restrict buf)
{
#if HOSTED
  gdb_parambuf_t parameters;
  struct gdb_stat gbuf;
  int ret;
  parameters[0] = (uint32_t) filename;
  parameters[1] = (uint32_t) strlen (filename);
  parameters[2] = (uint32_t) &gbuf;
  ret = __hosted (HOSTED_STAT, parameters);
  __hosted_from_gdb_stat (&gbuf, buf);
  errno = __hosted_from_gdb_errno (parameters[0]);
  return ret;
#else
  errno = ENOSYS;
  return -1;
#endif
}
