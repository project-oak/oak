/*
FUNCTION
	<<strtok>>, <<strtok_r>>, <<strsep>>---get next token from a string

INDEX
	strtok

INDEX
	strtok_r

INDEX
	strsep

SYNOPSIS
	#include <string.h>
      	char *strtok(char *restrict <[source]>,
                     const char *restrict <[delimiters]>);
      	char *strtok_r(char *restrict <[source]>,
                       const char *restrict <[delimiters]>,
                       char **<[lasts]>);
	char *strsep(char **<[source_ptr]>, const char *<[delimiters]>);

DESCRIPTION
	The <<strtok>> function is used to isolate sequential tokens in a 
	null-terminated string, <<*<[source]>>>. These tokens are delimited 
	in the string by at least one of the characters in <<*<[delimiters]>>>.
	The first time that <<strtok>> is called, <<*<[source]>>> should be
	specified; subsequent calls, wishing to obtain further tokens from
	the same string, should pass a null pointer instead.  The separator
	string, <<*<[delimiters]>>>, must be supplied each time and may 
	change between calls.

	The <<strtok>> function returns a pointer to the beginning of each 
	subsequent token in the string, after replacing the separator 
	character itself with a null character.  When no more tokens remain, 
	a null pointer is returned.

	The <<strtok_r>> function has the same behavior as <<strtok>>, except
	a pointer to placeholder <<*<[lasts]>>> must be supplied by the caller.

	The <<strsep>> function is similar in behavior to <<strtok>>, except
	a pointer to the string pointer must be supplied <<<[source_ptr]>>> and
	the function does not skip leading delimiters.  When the string starts
	with a delimiter, the delimiter is changed to the null character and
	the empty string is returned.  Like <<strtok_r>> and <<strtok>>, the
	<<*<[source_ptr]>>> is updated to the next character following the
	last delimiter found or NULL if the end of string is reached with
	no more delimiters.

RETURNS
	<<strtok>>, <<strtok_r>>, and <<strsep>> all return a pointer to the 
	next token, or <<NULL>> if no more tokens can be found.  For
	<<strsep>>, a token may be the empty string.

NOTES
	<<strtok>> is unsafe for multi-threaded applications.  <<strtok_r>>
	and <<strsep>> are thread-safe and should be used instead.

PORTABILITY
<<strtok>> is ANSI C.
<<strtok_r>> is POSIX.
<<strsep>> is a BSD extension.

<<strtok>>, <<strtok_r>>, and <<strsep>> require no supporting OS subroutines.

QUICKREF
	strtok ansi impure
*/

/* undef STRICT_ANSI so that strtok_r prototype will be defined */
#undef  __STRICT_ANSI__
#include <string.h>
#include <stdlib.h>
#include <_ansi.h>
#include <reent.h>

#ifdef _REENT_THREAD_LOCAL
_Thread_local char *_tls_strtok_last;
#endif

#ifndef _REENT_ONLY

extern char *__strtok_r (char *, const char *, char **, int);

char *
strtok (register char *__restrict s,
	register const char *__restrict delim)
{
	struct _reent *reent = _REENT;

	_REENT_CHECK_MISC(reent);
	return __strtok_r (s, delim, &(_REENT_STRTOK_LAST(reent)), 1);
}
#endif
