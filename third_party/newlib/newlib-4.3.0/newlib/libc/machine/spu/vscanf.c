/*
(C) Copyright IBM Corp. 2006

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright notice,
this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.
    * Neither the name of IBM nor the names of its contributors may be
used to endorse or promote products derived from this software without
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.

Author: Joel Schopp <jschopp@austin.ibm.com>
*/

#include <_ansi.h>
#include <stdio.h>

#include "c99ppe.h"

#include <stdarg.h>

#ifdef INTEGER_ONLY
#  define vscanf viscanf
#endif

typedef struct
{
  char* fmt;
  unsigned int pad0[ 3 ];
  va_list ap;
} c99_vscanf_t;

#ifndef _REENT_ONLY

int
vscanf (const char *fmt,
     va_list ap)
{
  c99_vscanf_t args;

  args.fmt = (char*) fmt;
  va_copy(args.ap,ap);

  return __send_to_ppe(SPE_C99_SIGNALCODE, SPE_C99_VSCANF, &args);
}

#endif /* ! _REENT_ONLY */
