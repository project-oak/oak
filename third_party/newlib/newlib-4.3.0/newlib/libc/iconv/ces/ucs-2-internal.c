/*
 * Copyright (c) 2003-2004, Artem B. Bityuckiy
 * Copyright (c) 1999,2000, Konstantin Chuguev. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */
#include "cesbi.h"

#if defined (ICONV_TO_UCS_CES_UCS_2_INTERNAL) \
 || defined (ICONV_FROM_UCS_CES_UCS_2_INTERNAL)

#include <_ansi.h>
#include <reent.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include "../lib/local.h"
#include "../lib/ucsconv.h"
#include "../lib/endian.h"

/*
 * Internal 2-byte representation of UCS-2 codes without restrictions and
 * without BOM support.
 */
 
#if defined (ICONV_FROM_UCS_CES_UCS_2_INTERNAL)
static size_t
ucs_2_internal_convert_from_ucs (void *data,
                                        register ucs4_t in,
                                        unsigned char **outbuf,
                                        size_t *outbytesleft)
{
  if (in > 0x0000FFFF)
    return (size_t)ICONV_CES_INVALID_CHARACTER;
  
  if (*outbytesleft < sizeof (ucs2_t))
    return (size_t)ICONV_CES_NOSPACE;

  *((ucs2_t *)(*outbuf)) = (ucs2_t)in;
  *outbuf += sizeof (ucs2_t);
  *outbytesleft -= sizeof (ucs2_t);

  return sizeof (ucs2_t);
}
#endif /* ICONV_FROM_UCS_CES_UCS_2_INTERNAL */

#if defined (ICONV_TO_UCS_CES_UCS_2_INTERNAL)
static ucs4_t
ucs_2_internal_convert_to_ucs (void *data,
                                      const unsigned char **inbuf,
                                      size_t *inbytesleft)
{
  register ucs4_t res;
  
  if (*inbytesleft < sizeof (ucs2_t))
    return (ucs4_t)ICONV_CES_BAD_SEQUENCE;

  res = (ucs4_t)*((ucs2_t *)(*inbuf));
  
  if (res > 0x0000FFFF)
    return (ucs4_t)ICONV_CES_INVALID_CHARACTER;
    
  *inbuf += sizeof (ucs2_t);
  *inbytesleft -= sizeof (ucs2_t);

  return res;
}
#endif /* ICONV_TO_UCS_CES_UCS_2_INTERNAL */

static int
ucs_2_internal_get_mb_cur_max (void *data)
{
  return 2;
}

#if defined (ICONV_TO_UCS_CES_UCS_2_INTERNAL)
const iconv_to_ucs_ces_handlers_t
_iconv_to_ucs_ces_handlers_ucs_2_internal = 
{
  NULL,
  NULL,
  ucs_2_internal_get_mb_cur_max,
  NULL,
  NULL,
  NULL,
  ucs_2_internal_convert_to_ucs
};
#endif

#if defined (ICONV_FROM_UCS_CES_UCS_2_INTERNAL)
const iconv_from_ucs_ces_handlers_t
_iconv_from_ucs_ces_handlers_ucs_2_internal =
{
  NULL,
  NULL,
  ucs_2_internal_get_mb_cur_max,
  NULL,
  NULL,
  NULL,
  ucs_2_internal_convert_from_ucs
};
#endif

#endif /* ICONV_TO_UCS_CES_UCS_2_INTERNAL || ICONV_FROM_UCS_CES_UCS_2_INTERNAL */

