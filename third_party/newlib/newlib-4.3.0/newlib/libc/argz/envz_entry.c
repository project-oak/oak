/* Copyright (C) 2002 by  Red Hat, Incorporated. All rights reserved.
 *
 * Permission to use, copy, modify, and distribute this software
 * is freely granted, provided that this notice is preserved.
 */

#include <errno.h>
#include <sys/types.h>
#include <string.h>
#include <stdlib.h>
#include <envz.h>

#include "buf_findstr.h"

char *
envz_entry (const char *envz,
       size_t envz_len,
       const char *name)
{
  char *buf_ptr = (char *)envz;
  size_t buf_len = envz_len;

  while(buf_len)
    {
      if (_buf_findstr(name, &buf_ptr, &buf_len))
        {
          if (buf_ptr)
            {
              if (*buf_ptr == '=' || *buf_ptr == '\0')
                {
                  buf_ptr--;

                  /* Move buf_ptr back to start of entry. */
                  while(*buf_ptr != '\0' && buf_ptr != envz) buf_ptr--;
                  
                  if(*buf_ptr == '\0')
                    buf_ptr++;

                  return (char *)buf_ptr;
                }
            }
        }
    }
  return 0;
}
