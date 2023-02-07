/*
FUNCTION
	<<strpbrk>>---find characters in string

INDEX
	strpbrk

SYNOPSIS
	#include <string.h>
	char *strpbrk(const char *<[s1]>, const char *<[s2]>);

DESCRIPTION
	This function locates the first occurence in the string
	pointed to by <[s1]> of any character in string pointed to by
	<[s2]> (excluding the terminating null character).

RETURNS
	<<strpbrk>> returns a pointer to the character found in <[s1]>, or a
	null pointer if no character from <[s2]> occurs in <[s1]>.

PORTABILITY
<<strpbrk>> requires no supporting OS subroutines.
*/

#include <string.h>

char *
strpbrk (const char *s1,
	const char *s2)
{
  const char *c = s2;
  if (!*s1)
    return (char *) NULL;

  while (*s1)
    {
      for (c = s2; *c; c++)
	{
	  if (*s1 == *c)
	    break;
	}
      if (*c)
	break;
      s1++;
    }

  if (*c == '\0')
    s1 = NULL;

  return (char *) s1;
}
