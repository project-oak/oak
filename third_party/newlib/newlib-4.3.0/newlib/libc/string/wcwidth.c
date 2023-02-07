/*
FUNCTION
	<<wcwidth>>---number of column positions of a wide-character code
	
INDEX
	wcwidth

SYNOPSIS
	#include <wchar.h>
	int wcwidth(const wint_t <[wc]>);

DESCRIPTION
	The <<wcwidth>> function shall determine the number of column
	positions required for the wide character <[wc]>. The application
	shall ensure that the value of <[wc]> is a character representable
	as a wint_t (combining Unicode surrogate pairs into single 21-bit
	Unicode code points), and is a wide-character code corresponding to a
	valid character in the current locale.

RETURNS
	The <<wcwidth>> function shall either return 0 (if <[wc]> is a null
	wide-character code), or return the number of column positions to
	be occupied by the wide-character code <[wc]>, or return -1 (if <[wc]>
	does not correspond to a printable wide-character code).

PORTABILITY
<<wcwidth>> has been introduced in the Single UNIX Specification Volume 2.
<<wcwidth>> has been marked as an extension in the Single UNIX Specification Volume 3.
*/

/*
 * This is an implementation of wcwidth() (defined in
 * IEEE Std 1002.1-2001) for Unicode.
 *
 * http://www.opengroup.org/onlinepubs/007904975/functions/wcwidth.html
 *
 * In fixed-width output devices, Latin characters all occupy a single
 * "cell" position of equal width, whereas ideographic CJK characters
 * occupy two such cells. Interoperability between terminal-line
 * applications and (teletype-style) character terminals using the
 * UTF-8 encoding requires agreement on which character should advance
 * the cursor by how many cell positions. No established formal
 * standards exist at present on which Unicode character shall occupy
 * how many cell positions on character terminals. These routines are
 * a first attempt of defining such behavior based on simple rules
 * applied to data provided by the Unicode Consortium.
 *
 * For some graphical characters, the Unicode standard explicitly
 * defines a character-cell width via the definition of the East Asian
 * FullWidth (F), Wide (W), Half-width (H), and Narrow (Na) classes.
 * In all these cases, there is no ambiguity about which width a
 * terminal shall use. For characters in the East Asian Ambiguous (A)
 * class, the width choice depends purely on a preference of backward
 * compatibility with either historic CJK or Western practice.
 * Choosing single-width for these characters is easy to justify as
 * the appropriate long-term solution, as the CJK practice of
 * displaying these characters as double-width comes from historic
 * implementation simplicity (8-bit encoded characters were displayed
 * single-width and 16-bit ones double-width, even for Greek,
 * Cyrillic, etc.) and not any typographic considerations.
 *
 * Much less clear is the choice of width for the Not East Asian
 * (Neutral) class. Existing practice does not dictate a width for any
 * of these characters. It would nevertheless make sense
 * typographically to allocate two character cells to characters such
 * as for instance EM SPACE or VOLUME INTEGRAL, which cannot be
 * represented adequately with a single-width glyph. The following
 * routines at present merely assign a single-cell width to all
 * neutral characters, in the interest of simplicity. This is not
 * entirely satisfactory and should be reconsidered before
 * establishing a formal standard in this area. At the moment, the
 * decision which Not East Asian (Neutral) characters should be
 * represented by double-width glyphs cannot yet be answered by
 * applying a simple rule from the Unicode database content. Setting
 * up a proper standard for the behavior of UTF-8 character terminals
 * will require a careful analysis not only of each Unicode character,
 * but also of each presentation form, something the author of these
 * routines has avoided to do so far.
 *
 * http://www.unicode.org/unicode/reports/tr11/
 *
 * Markus Kuhn -- 2007-05-26 (Unicode 5.0)
 *
 * Permission to use, copy, modify, and distribute this software
 * for any purpose and without fee is hereby granted. The author
 * disclaims all warranties with regard to this software.
 *
 * Latest version: http://www.cl.cam.ac.uk/~mgk25/ucs/wcwidth.c
 */

#include <_ansi.h>
#include <wchar.h>
#ifndef _MB_CAPABLE
#include <wctype.h> /* iswprint, iswcntrl */
#endif
#include "local.h"

#ifdef _MB_CAPABLE
struct interval
{
  int first;
  int last;
};

/* auxiliary function for binary search in interval table */
static int
bisearch(wint_t ucs, const struct interval *table, int max)
{
  int min = 0;
  int mid;

  if (ucs < table[0].first || ucs > table[max].last)
    return 0;
  while (max >= min)
    {
      mid = (min + max) / 2;
      if (ucs > table[mid].last)
	min = mid + 1;
      else if (ucs < table[mid].first)
	max = mid - 1;
      else
	return 1;
    }

  return 0;
}
#endif /* _MB_CAPABLE */

/* The following function defines the column width of an ISO 10646
 * character as follows:
 *
 *    - The null character (U+0000) has a column width of 0.
 *
 *    - Other C0/C1 control characters and DEL will lead to a return
 *      value of -1.
 *
 *    - If the current language is recognized as a language usually using
 *      CJK fonts, spacing characters in the East Asian Ambiguous (A)
 *      category as defined in Unicode Technical Report #11 have a column
 *      width of 2.
 *
 *    - Non-spacing and enclosing combining characters (general
 *      category code Mn or Me in the Unicode database) have a
 *      column width of 0.
 *
 *    - SOFT HYPHEN (U+00AD) has a column width of 1.
 *
 *    - Other format characters (general category code Cf in the Unicode
 *      database) and ZERO WIDTH SPACE (U+200B) have a column width of 0.
 *
 *    - Hangul Jamo medial vowels and final consonants (U+1160-U+11FF)
 *      have a column width of 0.
 *
 *    - Spacing characters in the East Asian Wide (W) or East Asian
 *      Full-width (F) category as defined in Unicode Technical
 *      Report #11 have a column width of 2.
 *
 *    - All remaining characters (including all printable
 *      ISO 8859-1 and WGL4 characters, Unicode control characters,
 *      etc.) have a column width of 1.
 *
 * This implementation assumes that wint_t characters are encoded
 * in ISO 10646.
 */

int
__wcwidth (const wint_t ucs)
{
#ifdef _MB_CAPABLE
  /* sorted list of non-overlapping intervals of East Asian Ambiguous chars */
  static const struct interval ambiguous[] =
#include "ambiguous.t"

  /* sorted list of non-overlapping intervals of non-spacing characters */
  static const struct interval combining[] =
#include "combining.t"

  /* sorted list of non-overlapping intervals of wide characters,
     ranges extended to Blocks where possible
   */
  static const struct interval wide[] =
#include "wide.t"

  /* Test for NUL character */
  if (ucs == 0)
    return 0;

  /* Test for printable ASCII characters */
  if (ucs >= 0x20 && ucs < 0x7f)
    return 1;

  /* Test for control characters */
  if (ucs < 0xa0)
    return -1;

  /* Test for surrogate pair values. */
  if (ucs >= 0xd800 && ucs <= 0xdfff)
    return -1;

  /* check CJK width mode (1: ambiguous-wide, 0: normal, -1: disabled) */
  int cjk_lang = __locale_cjk_lang ();

  /* binary search in table of ambiguous characters */
  if (cjk_lang > 0
      && bisearch(ucs, ambiguous,
		  sizeof(ambiguous) / sizeof(struct interval) - 1))
    return 2;

  /* binary search in table of non-spacing characters */
  if (bisearch(ucs, combining,
	       sizeof(combining) / sizeof(struct interval) - 1))
    return 0;

  /* if we arrive here, ucs is not a combining or C0/C1 control character */

  /* binary search in table of wide character codes */
  if (cjk_lang >= 0
      && bisearch(ucs, wide,
	       sizeof(wide) / sizeof(struct interval) - 1))
    return 2;
  else
    return 1;
#else /* !_MB_CAPABLE */
  if (iswprint (ucs))
    return 1;
  if (iswcntrl (ucs) || ucs == L'\0')
    return 0;
  return -1;
#endif /* _MB_CAPABLE */
}

int
wcwidth (const wint_t wc)
{
  wint_t wi = wc;

#ifdef _MB_CAPABLE
  wi = _jp2uc (wi);
#endif /* _MB_CAPABLE */
  return __wcwidth (wi);
}
