/*
 * sim-sbrk.c -- PowerPC sbrk support when running under the simulator.
 *
 * Copyright (c) 1995 Cygnus Support
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

extern char _end[];
static char *curbrk = _end;

char *
sbrk (incr)
     int incr;
{
  char *oldbrk = curbrk;
  curbrk += incr;
  if (brk (curbrk) == -1)
    return (char *) -1;

  return oldbrk;
}
