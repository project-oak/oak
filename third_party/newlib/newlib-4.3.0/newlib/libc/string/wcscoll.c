/*
FUNCTION
	<<wcscoll>>---locale-specific wide-character string compare
	
INDEX
	wcscoll

SYNOPSIS
	#include <wchar.h>
	int wcscoll(const wchar_t *<[stra]>, const wchar_t * <[strb]>);

DESCRIPTION
	<<wcscoll>> compares the wide-character string pointed to by
	<[stra]> to the wide-character string pointed to by <[strb]>,
	using an interpretation appropriate to the current <<LC_COLLATE>>
	state.

	(NOT Cygwin:) The current implementation of <<wcscoll>> simply
	uses <<wcscmp>> and does not support any language-specific sorting.

RETURNS
	If the first string is greater than the second string,
	<<wcscoll>> returns a number greater than zero.  If the two
	strings are equivalent, <<wcscoll>> returns zero.  If the first
	string is less than the second string, <<wcscoll>> returns a
	number less than zero.

PORTABILITY
<<wcscoll>> is ISO/IEC 9899/AMD1:1995 (ISO C).
*/

#include <_ansi.h>
#include <wchar.h>

int
wcscoll (const wchar_t *a,
	const wchar_t *b)

{
  return wcscmp (a, b);
}
