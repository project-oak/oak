#include <newlib.h>
#include <stdlib.h>
#include <locale.h>
#include "mbctype.h"
#include <wchar.h>
#include <string.h>
#include <errno.h>
#include "local.h"

int
_mbtowc_r (struct _reent *r,
        wchar_t       *__restrict pwc,
        const char    *__restrict s,
        size_t         n,
        mbstate_t      *state)
{
  return __MBTOWC (r, pwc, s, n, state);
}

int
__ascii_mbtowc (struct _reent *r,
        wchar_t       *pwc,
        const char    *s,
        size_t         n,
        mbstate_t      *state)
{
  wchar_t dummy;
  unsigned char *t = (unsigned char *)s;

  if (pwc == NULL)
    pwc = &dummy;

  if (s == NULL)
    return 0;

  if (n == 0)
    return -2;

#ifdef __CYGWIN__
  if ((wchar_t)*t >= 0x80)
    {
      _REENT_ERRNO(r) = EILSEQ;
      return -1;
    }
#endif

  *pwc = (wchar_t)*t;
  
  if (*t == '\0')
    return 0;

  return 1;
}

#ifdef _MB_CAPABLE
typedef enum __packed { ESCAPE, DOLLAR, BRACKET, AT, B, J,
               NUL, JIS_CHAR, OTHER, JIS_C_NUM } JIS_CHAR_TYPE;
typedef enum __packed { ASCII, JIS, A_ESC, A_ESC_DL, JIS_1, J_ESC, J_ESC_BR,
               INV, JIS_S_NUM } JIS_STATE; 
typedef enum __packed { COPY_A, COPY_J1, COPY_J2, MAKE_A, NOOP, EMPTY, ERROR } JIS_ACTION;

/************************************************************************************** 
 * state/action tables for processing JIS encoding
 * Where possible, switches to JIS are grouped with proceding JIS characters and switches
 * to ASCII are grouped with preceding JIS characters.  Thus, maximum returned length
 * is 2 (switch to JIS) + 2 (JIS characters) + 2 (switch back to ASCII) = 6.
 *************************************************************************************/

#ifndef  __CYGWIN__
static JIS_STATE JIS_state_table[JIS_S_NUM][JIS_C_NUM] = {
/*              ESCAPE   DOLLAR    BRACKET   AT       B       J        NUL      JIS_CHAR  OTHER */
/* ASCII */   { A_ESC,   ASCII,    ASCII,    ASCII,   ASCII,  ASCII,   ASCII,   ASCII,    ASCII },
/* JIS */     { J_ESC,   JIS_1,    JIS_1,    JIS_1,   JIS_1,  JIS_1,   INV,     JIS_1,    INV },
/* A_ESC */   { ASCII,   A_ESC_DL, ASCII,    ASCII,   ASCII,  ASCII,   ASCII,   ASCII,    ASCII },
/* A_ESC_DL */{ ASCII,   ASCII,    ASCII,    JIS,     JIS,    ASCII,   ASCII,   ASCII,    ASCII }, 
/* JIS_1 */   { INV,     JIS,      JIS,      JIS,     JIS,    JIS,     INV,     JIS,      INV },
/* J_ESC */   { INV,     INV,      J_ESC_BR, INV,     INV,    INV,     INV,     INV,      INV },
/* J_ESC_BR */{ INV,     INV,      INV,      INV,     ASCII,  ASCII,   INV,     INV,      INV },
};

static JIS_ACTION JIS_action_table[JIS_S_NUM][JIS_C_NUM] = {
/*              ESCAPE   DOLLAR    BRACKET   AT       B        J        NUL      JIS_CHAR  OTHER */
/* ASCII */   { NOOP,    COPY_A,   COPY_A,   COPY_A,  COPY_A,  COPY_A,  EMPTY,   COPY_A,  COPY_A},
/* JIS */     { NOOP,    COPY_J1,  COPY_J1,  COPY_J1, COPY_J1, COPY_J1, ERROR,   COPY_J1, ERROR },
/* A_ESC */   { COPY_A,  NOOP,     COPY_A,   COPY_A,  COPY_A,  COPY_A,  COPY_A,  COPY_A,  COPY_A},
/* A_ESC_DL */{ COPY_A,  COPY_A,   COPY_A,   NOOP,    NOOP,    COPY_A,  COPY_A,  COPY_A,  COPY_A},
/* JIS_1 */   { ERROR,   COPY_J2,  COPY_J2,  COPY_J2, COPY_J2, COPY_J2, ERROR,   COPY_J2, ERROR },
/* J_ESC */   { ERROR,   ERROR,    NOOP,     ERROR,   ERROR,   ERROR,   ERROR,   ERROR,   ERROR },
/* J_ESC_BR */{ ERROR,   ERROR,    ERROR,    ERROR,   MAKE_A,  MAKE_A,  ERROR,   ERROR,   ERROR },
};
#endif /* !__CYGWIN__ */

/* we override the mbstate_t __count field for more complex encodings and use it store a state value */
#define __state __count

#ifdef _MB_EXTENDED_CHARSETS_ISO
static int
___iso_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
	       int iso_idx, mbstate_t *state)
{
  wchar_t dummy;
  unsigned char *t = (unsigned char *)s;

  if (pwc == NULL)
    pwc = &dummy;

  if (s == NULL)
    return 0;

  if (n == 0)
    return -2;

  if (*t >= 0xa0)
    {
      if (iso_idx >= 0)
	{
	  *pwc = __iso_8859_conv[iso_idx][*t - 0xa0];
	  if (*pwc == 0) /* Invalid character */
	    {
	      _REENT_ERRNO(r) = EILSEQ;
	      return -1;
	    }
	  return 1;
	}
    }

  *pwc = (wchar_t) *t;
  
  if (*t == '\0')
    return 0;

  return 1;
}

static int
__iso_8859_1_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		     mbstate_t *state)
{
  return ___iso_mbtowc (r, pwc, s, n, -1, state);
}

static int
__iso_8859_2_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		     mbstate_t *state)
{
  return ___iso_mbtowc (r, pwc, s, n, 0, state);
}

static int
__iso_8859_3_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		     mbstate_t *state)
{
  return ___iso_mbtowc (r, pwc, s, n, 1, state);
}

static int
__iso_8859_4_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		     mbstate_t *state)
{
  return ___iso_mbtowc (r, pwc, s, n, 2, state);
}

static int
__iso_8859_5_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		     mbstate_t *state)
{
  return ___iso_mbtowc (r, pwc, s, n, 3, state);
}

static int
__iso_8859_6_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		     mbstate_t *state)
{
  return ___iso_mbtowc (r, pwc, s, n, 4, state);
}

static int
__iso_8859_7_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		     mbstate_t *state)
{
  return ___iso_mbtowc (r, pwc, s, n, 5, state);
}

static int
__iso_8859_8_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		     mbstate_t *state)
{
  return ___iso_mbtowc (r, pwc, s, n, 6, state);
}

static int
__iso_8859_9_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		     mbstate_t *state)
{
  return ___iso_mbtowc (r, pwc, s, n, 7, state);
}

static int
__iso_8859_10_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		      mbstate_t *state)
{
  return ___iso_mbtowc (r, pwc, s, n, 8, state);
}

static int
__iso_8859_11_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		      mbstate_t *state)
{
  return ___iso_mbtowc (r, pwc, s, n, 9, state);
}

static int
__iso_8859_13_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		      mbstate_t *state)
{
  return ___iso_mbtowc (r, pwc, s, n, 10, state);
}

static int
__iso_8859_14_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		      mbstate_t *state)
{
  return ___iso_mbtowc (r, pwc, s, n, 11, state);
}

static int
__iso_8859_15_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		      mbstate_t *state)
{
  return ___iso_mbtowc (r, pwc, s, n, 12, state);
}

static int
__iso_8859_16_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		      mbstate_t *state)
{
  return ___iso_mbtowc (r, pwc, s, n, 13, state);
}

static mbtowc_p __iso_8859_mbtowc[17] = {
  NULL,
  __iso_8859_1_mbtowc,
  __iso_8859_2_mbtowc,
  __iso_8859_3_mbtowc,
  __iso_8859_4_mbtowc,
  __iso_8859_5_mbtowc,
  __iso_8859_6_mbtowc,
  __iso_8859_7_mbtowc,
  __iso_8859_8_mbtowc,
  __iso_8859_9_mbtowc,
  __iso_8859_10_mbtowc,
  __iso_8859_11_mbtowc,
  NULL,			/* No ISO 8859-12 */
  __iso_8859_13_mbtowc,
  __iso_8859_14_mbtowc,
  __iso_8859_15_mbtowc,
  __iso_8859_16_mbtowc
};

/* val *MUST* be valid!  All checks for validity are supposed to be
   performed before calling this function. */
mbtowc_p
__iso_mbtowc (int val)
{
  return __iso_8859_mbtowc[val];
}
#endif /* _MB_EXTENDED_CHARSETS_ISO */

#ifdef _MB_EXTENDED_CHARSETS_WINDOWS
static int
___cp_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
	      int cp_idx, mbstate_t *state)
{
  wchar_t dummy;
  unsigned char *t = (unsigned char *)s;

  if (pwc == NULL)
    pwc = &dummy;

  if (s == NULL)
    return 0;

  if (n == 0)
    return -2;

  if (*t >= 0x80)
    {
      if (cp_idx >= 0)
	{
	  *pwc = __cp_conv[cp_idx][*t - 0x80];
	  if (*pwc == 0) /* Invalid character */
	    {
	      _REENT_ERRNO(r) = EILSEQ;
	      return -1;
	    }
	  return 1;
	}
    }

  *pwc = (wchar_t)*t;
  
  if (*t == '\0')
    return 0;

  return 1;
}

static int
__cp_437_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		 mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 0, state);
}

static int
__cp_720_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		 mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 1, state);
}

static int
__cp_737_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		 mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 2, state);
}

static int
__cp_775_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		 mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 3, state);
}

static int
__cp_850_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		 mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 4, state);
}

static int
__cp_852_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		 mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 5, state);
}

static int
__cp_855_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		 mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 6, state);
}

static int
__cp_857_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		 mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 7, state);
}

static int
__cp_858_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		 mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 8, state);
}

static int
__cp_862_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		 mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 9, state);
}

static int
__cp_866_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		 mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 10, state);
}

static int
__cp_874_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		 mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 11, state);
}

static int
__cp_1125_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		  mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 12, state);
}

static int
__cp_1250_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		  mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 13, state);
}

static int
__cp_1251_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		  mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 14, state);
}

static int
__cp_1252_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		  mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 15, state);
}

static int
__cp_1253_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		  mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 16, state);
}

static int
__cp_1254_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		  mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 17, state);
}

static int
__cp_1255_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		  mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 18, state);
}

static int
__cp_1256_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		  mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 19, state);
}

static int
__cp_1257_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		  mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 20, state);
}

static int
__cp_1258_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		  mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 21, state);
}

static int
__cp_20866_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		   mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 22, state);
}

static int
__cp_21866_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		   mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 23, state);
}

static int
__cp_101_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		 mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 24, state);
}

static int
__cp_102_mbtowc (struct _reent *r, wchar_t *pwc, const char *s, size_t n,
		 mbstate_t *state)
{
  return ___cp_mbtowc (r, pwc, s, n, 25, state);
}

static mbtowc_p __cp_xxx_mbtowc[26] = {
  __cp_437_mbtowc,
  __cp_720_mbtowc,
  __cp_737_mbtowc,
  __cp_775_mbtowc,
  __cp_850_mbtowc,
  __cp_852_mbtowc,
  __cp_855_mbtowc,
  __cp_857_mbtowc,
  __cp_858_mbtowc,
  __cp_862_mbtowc,
  __cp_866_mbtowc,
  __cp_874_mbtowc,
  __cp_1125_mbtowc,
  __cp_1250_mbtowc,
  __cp_1251_mbtowc,
  __cp_1252_mbtowc,
  __cp_1253_mbtowc,
  __cp_1254_mbtowc,
  __cp_1255_mbtowc,
  __cp_1256_mbtowc,
  __cp_1257_mbtowc,
  __cp_1258_mbtowc,
  __cp_20866_mbtowc,
  __cp_21866_mbtowc,
  __cp_101_mbtowc,
  __cp_102_mbtowc
};

/* val *MUST* be valid!  All checks for validity are supposed to be
   performed before calling this function. */
mbtowc_p
__cp_mbtowc (int val)
{
  return __cp_xxx_mbtowc[__cp_val_index (val)];
}
#endif /* _MB_EXTENDED_CHARSETS_WINDOWS */

int
__utf8_mbtowc (struct _reent *r,
        wchar_t       *pwc,
        const char    *s,
        size_t         n,
        mbstate_t      *state)
{
  wchar_t dummy;
  unsigned char *t = (unsigned char *)s;
  int ch;
  int i = 0;

  if (pwc == NULL)
    pwc = &dummy;

  if (s == NULL)
    return 0;

  if (n == 0)
    return -2;

  if (state->__count == 0)
    ch = t[i++];
  else
    ch = state->__value.__wchb[0];

  if (ch == '\0')
    {
      *pwc = 0;
      state->__count = 0;
      return 0; /* s points to the null character */
    }

  if (ch <= 0x7f)
    {
      /* single-byte sequence */
      state->__count = 0;
      *pwc = ch;
      return 1;
    }
  if (ch >= 0xc0 && ch <= 0xdf)
    {
      /* two-byte sequence */
      state->__value.__wchb[0] = ch;
      if (state->__count == 0)
	state->__count = 1;
      else if (n < (size_t)-1)
	++n;
      if (n < 2)
	return -2;
      ch = t[i++];
      if (ch < 0x80 || ch > 0xbf)
	{
	  _REENT_ERRNO(r) = EILSEQ;
	  return -1;
	}
      if (state->__value.__wchb[0] < 0xc2)
	{
	  /* overlong UTF-8 sequence */
	  _REENT_ERRNO(r) = EILSEQ;
	  return -1;
	}
      state->__count = 0;
      *pwc = (wchar_t)((state->__value.__wchb[0] & 0x1f) << 6)
	|    (wchar_t)(ch & 0x3f);
      return i;
    }
  if (ch >= 0xe0 && ch <= 0xef)
    {
      /* three-byte sequence */
      wchar_t tmp;
      state->__value.__wchb[0] = ch;
      if (state->__count == 0)
	state->__count = 1;
      else if (n < (size_t)-1)
	++n;
      if (n < 2)
	return -2;
      ch = (state->__count == 1) ? t[i++] : state->__value.__wchb[1];
      if (state->__value.__wchb[0] == 0xe0 && ch < 0xa0)
	{
	  /* overlong UTF-8 sequence */
	  _REENT_ERRNO(r) = EILSEQ;
	  return -1;
	}
      if (ch < 0x80 || ch > 0xbf)
	{
	  _REENT_ERRNO(r) = EILSEQ;
	  return -1;
	}
      state->__value.__wchb[1] = ch;
      if (state->__count == 1)
	state->__count = 2;
      else if (n < (size_t)-1)
	++n;
      if (n < 3)
	return -2;
      ch = t[i++];
      if (ch < 0x80 || ch > 0xbf)
	{
	  _REENT_ERRNO(r) = EILSEQ;
	  return -1;
	}
      state->__count = 0;
      tmp = (wchar_t)((state->__value.__wchb[0] & 0x0f) << 12)
	|    (wchar_t)((state->__value.__wchb[1] & 0x3f) << 6)
	|     (wchar_t)(ch & 0x3f);
      *pwc = tmp;
      return i;
    }
  if (ch >= 0xf0 && ch <= 0xf4)
    {
      /* four-byte sequence */
      wint_t tmp;
      state->__value.__wchb[0] = ch;
      if (state->__count == 0)
	state->__count = 1;
      else if (n < (size_t)-1)
	++n;
      if (n < 2)
	return -2;
      ch = (state->__count == 1) ? t[i++] : state->__value.__wchb[1];
      if ((state->__value.__wchb[0] == 0xf0 && ch < 0x90)
	  || (state->__value.__wchb[0] == 0xf4 && ch >= 0x90))
	{
	  /* overlong UTF-8 sequence or result is > 0x10ffff */
	  _REENT_ERRNO(r) = EILSEQ;
	  return -1;
	}
      if (ch < 0x80 || ch > 0xbf)
	{
	  _REENT_ERRNO(r) = EILSEQ;
	  return -1;
	}
      state->__value.__wchb[1] = ch;
      if (state->__count == 1)
	state->__count = 2;
      else if (n < (size_t)-1)
	++n;
      if (n < 3)
	return -2;
      ch = (state->__count == 2) ? t[i++] : state->__value.__wchb[2];
      if (ch < 0x80 || ch > 0xbf)
	{
	  _REENT_ERRNO(r) = EILSEQ;
	  return -1;
	}
      state->__value.__wchb[2] = ch;
      if (state->__count == 2)
	state->__count = 3;
      else if (n < (size_t)-1)
	++n;
      if (state->__count == 3 && sizeof(wchar_t) == 2)
	{
	  /* On systems which have wchar_t being UTF-16 values, the value
	     doesn't fit into a single wchar_t in this case.  So what we
	     do here is to store the state with a special value of __count
	     and return the first half of a surrogate pair.  The first
	     three bytes of a UTF-8 sequence are enough to generate the
	     first half of a UTF-16 surrogate pair.  As return value we
	     choose to return the number of bytes actually read up to
	     here.
	     The second half of the surrogate pair is returned in case we
	     recognize the special __count value of four, and the next
	     byte is actually a valid value.  See below. */
	  tmp = (wint_t)((state->__value.__wchb[0] & 0x07) << 18)
	    |   (wint_t)((state->__value.__wchb[1] & 0x3f) << 12)
	    |   (wint_t)((state->__value.__wchb[2] & 0x3f) << 6);
	  state->__count = 4;
	  *pwc = 0xd800 | ((tmp - 0x10000) >> 10);
	  return i;
	}
      if (n < 4)
	return -2;
      ch = t[i++];
      if (ch < 0x80 || ch > 0xbf)
	{
	  _REENT_ERRNO(r) = EILSEQ;
	  return -1;
	}
      tmp = (wint_t)((state->__value.__wchb[0] & 0x07) << 18)
	|   (wint_t)((state->__value.__wchb[1] & 0x3f) << 12)
	|   (wint_t)((state->__value.__wchb[2] & 0x3f) << 6)
	|   (wint_t)(ch & 0x3f);
      if (state->__count == 4 && sizeof(wchar_t) == 2)
	/* Create the second half of the surrogate pair for systems with
	   wchar_t == UTF-16 . */
	*pwc = 0xdc00 | (tmp & 0x3ff);
      else
	*pwc = tmp;
      state->__count = 0;
      return i;
    }

  _REENT_ERRNO(r) = EILSEQ;
  return -1;
}

/* Cygwin defines its own doublebyte charset conversion functions 
   because the underlying OS requires wchar_t == UTF-16. */
#ifndef  __CYGWIN__
int
__sjis_mbtowc (struct _reent *r,
        wchar_t       *pwc,
        const char    *s,
        size_t         n,
        mbstate_t      *state)
{
  wchar_t dummy;
  unsigned char *t = (unsigned char *)s;
  int ch;
  int i = 0;

  if (pwc == NULL)
    pwc = &dummy;

  if (s == NULL)
    return 0;  /* not state-dependent */

  if (n == 0)
    return -2;

  ch = t[i++];
  if (state->__count == 0)
    {
      if (_issjis1 (ch))
	{
	  state->__value.__wchb[0] = ch;
	  state->__count = 1;
	  if (n <= 1)
	    return -2;
	  ch = t[i++];
	}
    }
  if (state->__count == 1)
    {
      if (_issjis2 (ch))
	{
	  *pwc = (((wchar_t)state->__value.__wchb[0]) << 8) + (wchar_t)ch;
	  state->__count = 0;
	  return i;
	}
      else  
	{
	  _REENT_ERRNO(r) = EILSEQ;
	  return -1;
	}
    }

  *pwc = (wchar_t)*t;
  
  if (*t == '\0')
    return 0;

  return 1;
}

int
__eucjp_mbtowc (struct _reent *r,
        wchar_t       *pwc,
        const char    *s,
        size_t         n,
        mbstate_t      *state)
{
  wchar_t dummy;
  unsigned char *t = (unsigned char *)s;
  int ch;
  int i = 0;

  if (pwc == NULL)
    pwc = &dummy;

  if (s == NULL)
    return 0;

  if (n == 0)
    return -2;

  ch = t[i++];
  if (state->__count == 0)
    {
      if (_iseucjp1 (ch))
	{
	  state->__value.__wchb[0] = ch;
	  state->__count = 1;
	  if (n <= 1)
	    return -2;
	  ch = t[i++];
	}
    }
  if (state->__count == 1)
    {
      if (_iseucjp2 (ch))
	{
	  if (state->__value.__wchb[0] == 0x8f)
	    {
	      state->__value.__wchb[1] = ch;
	      state->__count = 2;
	      if (n <= i)
		return -2;
	      ch = t[i++];
	    }
	  else
	    {
	      *pwc = (((wchar_t)state->__value.__wchb[0]) << 8) + (wchar_t)ch;
	      state->__count = 0;
	      return i;
	    }
	}
      else
	{
	  _REENT_ERRNO(r) = EILSEQ;
	  return -1;
	}
    }
  if (state->__count == 2)
    {
      if (_iseucjp2 (ch))
	{
	  *pwc = (((wchar_t)state->__value.__wchb[1]) << 8)
		 + (wchar_t)(ch & 0x7f);
	  state->__count = 0;
	  return i;
	}
      else
	{
	  _REENT_ERRNO(r) = EILSEQ;
	  return -1;
	}
    }

  *pwc = (wchar_t)*t;
  
  if (*t == '\0')
    return 0;

  return 1;
}

int
__jis_mbtowc (struct _reent *r,
        wchar_t       *pwc,
        const char    *s,
        size_t         n,
        mbstate_t      *state)
{
  wchar_t dummy;
  unsigned char *t = (unsigned char *)s;
  JIS_STATE curr_state;
  JIS_ACTION action;
  JIS_CHAR_TYPE ch;
  unsigned char *ptr;
  unsigned int i;
  int curr_ch;

  if (pwc == NULL)
    pwc = &dummy;

  if (s == NULL)
    {
      state->__state = ASCII;
      return 1;  /* state-dependent */
    }

  if (n == 0)
    return -2;

  curr_state = state->__state;
  ptr = t;

  for (i = 0; i < n; ++i)
    {
      curr_ch = t[i];
      switch (curr_ch)
	{
	case ESC_CHAR:
	  ch = ESCAPE;
	  break;
	case '$':
	  ch = DOLLAR;
	  break;
	case '@':
	  ch = AT;
	  break;
	case '(':
	  ch = BRACKET;
	  break;
	case 'B':
	  ch = B;
	  break;
	case 'J':
	  ch = J;
	  break;
	case '\0':
	  ch = NUL;
	  break;
	default:
	  if (_isjis (curr_ch))
	    ch = JIS_CHAR;
	  else
	    ch = OTHER;
	}

      action = JIS_action_table[curr_state][ch];
      curr_state = JIS_state_table[curr_state][ch];
    
      switch (action)
	{
	case NOOP:
	  break;
	case EMPTY:
	  state->__state = ASCII;
	  *pwc = (wchar_t)0;
	  return 0;
	case COPY_A:
	  state->__state = ASCII;
	  *pwc = (wchar_t)*ptr;
	  return (i + 1);
	case COPY_J1:
	  state->__value.__wchb[0] = t[i];
	  break;
	case COPY_J2:
	  state->__state = JIS;
	  *pwc = (((wchar_t)state->__value.__wchb[0]) << 8) + (wchar_t)(t[i]);
	  return (i + 1);
	case MAKE_A:
	  ptr = (unsigned char *)(t + i + 1);
	  break;
	case ERROR:
	default:
	  _REENT_ERRNO(r) = EILSEQ;
	  return -1;
	}

    }

  state->__state = curr_state;
  return -2;  /* n < bytes needed */
}
#endif /* !__CYGWIN__*/
#endif /* _MB_CAPABLE */
