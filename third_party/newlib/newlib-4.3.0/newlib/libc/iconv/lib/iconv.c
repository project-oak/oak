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

/*
FUNCTION
<<iconv>>, <<iconv_open>>, <<iconv_close>>---charset conversion routines

INDEX
	iconv
INDEX
	iconv_open
INDEX
	iconv_close
INDEX
	_iconv_r
INDEX
	_iconv_open_r
INDEX
	_iconv_close_r

SYNOPSIS
	#include <iconv.h>
	iconv_t iconv_open (const char *<[to]>, const char *<[from]>);
	int iconv_close (iconv_t <[cd]>);
        size_t iconv (iconv_t <[cd]>, char **restrict <[inbuf]>, 
	              size_t *restrict <[inbytesleft]>, 
		      char **restrict <[outbuf]>, 
                      size_t *restrict <[outbytesleft]>);

	iconv_t _iconv_open_r (struct _reent *<[rptr]>, 
			       const char *<[to]>, const char *<[from]>);
	int _iconv_close_r (struct _reent *<[rptr]>, iconv_t <[cd]>);
        size_t _iconv_r (struct _reent *<[rptr]>,
			 iconv_t <[cd]>, const char **<[inbuf]>, 
	                 size_t *<[inbytesleft]>, 
		         char **<[outbuf]>, size_t *<[outbytesleft]>);

DESCRIPTION
The function <<iconv>> converts characters from <[in]> which are in one
encoding to characters of another encoding, outputting them to <[out]>.
The value <[inleft]> specifies the number of input bytes to convert whereas
the value <[outleft]> specifies the size remaining in the <[out]> buffer. 
The conversion descriptor <[cd]> specifies the conversion being performed
and is created via <<iconv_open>>.

An <<iconv>> conversion stops if: the input bytes are exhausted, the output
buffer is full, an invalid input character sequence occurs, or the
conversion specifier is invalid.

The function <<iconv_open>> is used to specify a conversion from one
encoding: <[from]> to another: <[to]>.  The result of the call is
to create a conversion specifier that can be used with <<iconv>>.

The function <<iconv_close>> is used to close a conversion specifier after
it is no longer needed.

The <<_iconv_r>>, <<_iconv_open_r>>, and <<_iconv_close_r>> functions are
reentrant versions of <<iconv>>, <<iconv_open>>, and <<iconv_close>>,
respectively.  An additional reentrancy struct pointer: <[rptr]> is passed
to properly set <<errno>>.

RETURNS
The <<iconv>> function returns the number of non-identical conversions
performed.  If an error occurs, (size_t)-1 is returned and <<errno>>
is set appropriately.  The values of <[inleft]>, <[in]>, <[out]>,
and <[outleft]> are modified to indicate how much input was processed
and how much output was created.

The <<iconv_open>> function returns either a valid conversion specifier
or (iconv_t)-1 to indicate failure.  If failure occurs, <<errno>> is set
appropriately.

The <<iconv_close>> function returns 0 on success or -1 on failure.
If failure occurs <<errno>> is set appropriately.

PORTABILITY
<<iconv>>, <<iconv_open>>, and <<iconv_close>> are non-ANSI and are specified
by the Single Unix specification.

No supporting OS subroutine calls are required.
*/
#include <_ansi.h>
#include <reent.h>
#include <sys/types.h>
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <iconv.h>
#include <wchar.h>
#include <sys/iconvnls.h>
#include "local.h"
#include "conv.h"
#include "ucsconv.h"

/*
 * iconv interface functions as specified by Single Unix specification.
 */

iconv_t
iconv_open (const char *to,
                   const char *from)
{
  return _iconv_open_r (_REENT, to, from);
}


size_t
iconv (iconv_t cd,
              char **__restrict inbuf,
              size_t *__restrict inbytesleft,
              char **__restrict outbuf,
              size_t *__restrict outbytesleft)
{
    return _iconv_r (_REENT, cd, (const char **) inbuf, inbytesleft,
		     outbuf, outbytesleft);
}


int
iconv_close (iconv_t cd)
{
    return _iconv_close_r (_REENT, cd);
}


#ifndef _REENT_ONLY
iconv_t
_iconv_open_r (struct _reent *rptr,
                      const char *to,
                      const char *from)
{
  iconv_conversion_t *ic;
    
  if (to == NULL || from == NULL || *to == '\0' || *from == '\0')
    return (iconv_t)-1;

  if ((to = (const char *)_iconv_resolve_encoding_name (rptr, to)) == NULL)
    return (iconv_t)-1;

  if ((from = (const char *)_iconv_resolve_encoding_name (rptr, from)) == NULL)
    {
      _free_r (rptr, (void *)to);
      return (iconv_t)-1;
    }

  ic = (iconv_conversion_t *)_malloc_r (rptr, sizeof (iconv_conversion_t));
  if (ic == NULL)
    return (iconv_t)-1;

  /* Select which conversion type to use */
  if (strcmp (from, to) == 0)
    {
      /* Use null conversion */
      ic->handlers = &_iconv_null_conversion_handlers;
      ic->data = ic->handlers->open (rptr, to, from);
    }
  else  
    {
      /* Use UCS-based conversion */
      ic->handlers = &_iconv_ucs_conversion_handlers;
      ic->data = ic->handlers->open (rptr, to, from);
    }

  _free_r (rptr, (void *)to);
  _free_r (rptr, (void *)from);

  if (ic->data == NULL)
    {
      _free_r (rptr, (void *)ic);
      return (iconv_t)-1;
    }

  return (void *)ic;
}


size_t
_iconv_r (struct _reent *rptr,
                 iconv_t cd,
                 const char **inbuf,
                 size_t *inbytesleft,
                 char **outbuf,
                 size_t *outbytesleft)
{
  iconv_conversion_t *ic = (iconv_conversion_t *)cd;

  if ((void *)cd == NULL || cd == (iconv_t)-1 || ic->data == NULL
       || (ic->handlers != &_iconv_null_conversion_handlers
           && ic->handlers != &_iconv_ucs_conversion_handlers))
    {
      _REENT_ERRNO (rptr) = EBADF;
      return (size_t)-1;
    }

  if (inbuf == NULL || *inbuf == NULL)
    {
      mbstate_t state_null = ICONV_ZERO_MB_STATE_T;
      
      if (!ic->handlers->is_stateful(ic->data, 1))
        return (size_t)0;
      
      if (outbuf == NULL || *outbuf == NULL)
        {
          /* Reset shift state */
          ic->handlers->set_state (ic->data, &state_null, 1);
          
          return (size_t)0;
        }
       
      if (outbytesleft != NULL)
        {
          mbstate_t state_save = ICONV_ZERO_MB_STATE_T;
          
          /* Save current shift state */          
          ic->handlers->get_state (ic->data, &state_save, 1);
          
          /* Reset shift state */
          ic->handlers->set_state (ic->data, &state_null, 1);

          /* Get initial shift state sequence and it's length */
          ic->handlers->get_state (ic->data, &state_null, 1);
          
          if (*outbytesleft >= state_null.__count)
            {
              memcpy ((void *)(*outbuf), (void *)&state_null, state_null.__count);
              
              *outbuf += state_null.__count;
              *outbytesleft -= state_null.__count;

              return (size_t)0;
            }

           /* Restore shift state if output buffer is too small */
           ic->handlers->set_state (ic->data, &state_save, 1);
        }
       
      _REENT_ERRNO (rptr) = E2BIG;
      return (size_t)-1;
    }
  
  if (*inbytesleft == 0)
    {
      _REENT_ERRNO (rptr) = EINVAL;
      return (size_t)-1;
    }
   
  if (*outbytesleft == 0 || *outbuf == NULL)
    {
      _REENT_ERRNO (rptr) = E2BIG;
      return (size_t)-1;
    }

  return ic->handlers->convert (rptr,
                                ic->data,
                                (const unsigned char**)inbuf,
                                inbytesleft,
                                (unsigned char**)outbuf,
                                outbytesleft,
                                0);
}


int
_iconv_close_r (struct _reent *rptr,
                       iconv_t cd)
{
  int res;
  iconv_conversion_t *ic = (iconv_conversion_t *)cd;
  
  if ((void *)cd == NULL || cd == (iconv_t)-1 || ic->data == NULL
       || (ic->handlers != &_iconv_null_conversion_handlers
           && ic->handlers != &_iconv_ucs_conversion_handlers))
    {
      _REENT_ERRNO (rptr) = EBADF;
      return -1;
    }

  res = (int)ic->handlers->close (rptr, ic->data);
  
  _free_r (rptr, (void *)cd);

  return res;
}
#endif /* !_REENT_ONLY */
