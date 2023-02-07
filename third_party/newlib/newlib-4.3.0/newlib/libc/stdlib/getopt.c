/****************************************************************************

getopt.c - Read command line options

AUTHOR: Gregory Pietsch
CREATED Fri Jan 10 21:13:05 1997

DESCRIPTION:

The getopt() function parses the command line arguments.  Its arguments argc
and argv are the argument count and array as passed to the main() function
on program invocation.  The argument optstring is a list of available option
characters.  If such a character is followed by a colon (`:'), the option
takes an argument, which is placed in optarg.  If such a character is
followed by two colons, the option takes an optional argument, which is
placed in optarg.  If the option does not take an argument, optarg is NULL.

The external variable optind is the index of the next array element of argv
to be processed; it communicates from one call to the next which element to
process.

The getopt_long() function works like getopt() except that it also accepts
long options started by two dashes `--'.  If these take values, it is either
in the form

--arg=value

 or

--arg value

It takes the additional arguments longopts which is a pointer to the first
element of an array of type struct option.  The last element of the array
has to be filled with NULL for the name field.

The longind pointer points to the index of the current long option relative
to longopts if it is non-NULL.

The getopt() function returns the option character if the option was found
successfully, `:' if there was a missing parameter for one of the options,
`?' for an unknown option character, and EOF for the end of the option list.

The getopt_long() function's return value is described in the header file.

The function getopt_long_only() is identical to getopt_long(), except that a
plus sign `+' can introduce long options as well as `--'.

The following describes how to deal with options that follow non-option
argv-elements.

If the caller did not specify anything, the default is REQUIRE_ORDER if the
environment variable POSIXLY_CORRECT is defined, PERMUTE otherwise.

REQUIRE_ORDER means don't recognize them as options; stop option processing
when the first non-option is seen.  This is what Unix does.  This mode of
operation is selected by either setting the environment variable
POSIXLY_CORRECT, or using `+' as the first character of the optstring
parameter.

PERMUTE is the default.  We permute the contents of ARGV as we scan, so that
eventually all the non-options are at the end.  This allows options to be
given in any order, even with programs that were not written to expect this.

RETURN_IN_ORDER is an option available to programs that were written to
expect options and other argv-elements in any order and that care about the
ordering of the two.  We describe each non-option argv-element as if it were
the argument of an option with character code 1.  Using `-' as the first
character of the optstring parameter selects this mode of operation.

The special argument `--' forces an end of option-scanning regardless of the
value of ordering.  In the case of RETURN_IN_ORDER, only `--' can cause
getopt() and friends to return EOF with optind != argc.

2012-08-26: Tried to make the error handling more sus4-like. The functions
return a colon if getopt() and friends detect a missing argument and the
first character of shortopts/optstring starts with a colon (`:'). If getopt()
and friends detect a missing argument and shortopts/optstring does not start
with a colon, the function returns a question mark (`?'). If it was a missing
argument to a short option, optopt is set to the character in question. The
colon goes after the ordering character (`+' or `-').

COPYRIGHT NOTICE AND DISCLAIMER:

Copyright (C) 1997 Gregory Pietsch

This file and the accompanying getopt.h header file are hereby placed in the 
public domain without restrictions.  Just give the author credit, don't
claim you wrote it or prevent anyone else from using it.

Gregory Pietsch's current e-mail address:
gpietsch@comcast.net
****************************************************************************/

#ifndef HAVE_GETOPT

/* include files */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define __need_getopt_newlib
#include <getopt.h>

/* macros */

/* types */
typedef enum GETOPT_ORDERING_T
{
  PERMUTE,
  RETURN_IN_ORDER,
  REQUIRE_ORDER
} GETOPT_ORDERING_T;

/* globally-defined variables */
char *optarg = 0;
int optind = 0;
int opterr = 1;
int optopt = '?';

/* static variables */
static int optwhere = 0;
static int permute_from = 0;
static int num_nonopts = 0;

/* functions */

/* reverse_argv_elements:  reverses num elements starting at argv */
static void
reverse_argv_elements (char **argv, int num)
{
  int i;
  char *tmp;

  for (i = 0; i < (num >> 1); i++)
    {
      tmp = argv[i];
      argv[i] = argv[num - i - 1];
      argv[num - i - 1] = tmp;
    }
}

/* permute: swap two blocks of argv-elements given their lengths */
static void
permute (char *const argv[], int len1, int len2)
{
  reverse_argv_elements ((char **) argv, len1);
  reverse_argv_elements ((char **) argv, len1 + len2);
  reverse_argv_elements ((char **) argv, len2);
}

/* is_option: is this argv-element an option or the end of the option list? */
static int
is_option (char *argv_element, int only)
{
  return ((argv_element == 0)
	  || (argv_element[0] == '-') || (only && argv_element[0] == '+'));
}

/* read_globals: read the values from the globals into a getopt_data 
   structure */
static void
read_globals (struct getopt_data *data)
{
  data->optarg = optarg;
  data->optind = optind;
  data->opterr = opterr;
  data->optopt = optopt;
  data->optwhere = optwhere;
  data->permute_from = permute_from;
  data->num_nonopts = num_nonopts;
}

/* write_globals: write the values into the globals from a getopt_data
   structure */
static void
write_globals (struct getopt_data *data)
{
  optarg = data->optarg;
  optind = data->optind;
  opterr = data->opterr;
  optopt = data->optopt;
  optwhere = data->optwhere;
  permute_from = data->permute_from;
  num_nonopts = data->num_nonopts;
}

/* getopt_internal:  the function that does all the dirty work
   NOTE: to reduce the code and RAM footprint this function uses
   fputs()/fputc() to do output to stderr instead of fprintf(). */
static int
getopt_internal (int argc, char *const argv[], const char *shortopts,
		 const struct option *longopts, int *longind, int only,
		 struct getopt_data *data)
{
  GETOPT_ORDERING_T ordering = PERMUTE;
  int optindex = 0;
  size_t match_chars = 0;
  char *possible_arg = 0;
  int longopt_match = -1;
  int has_arg = -1;
  char *cp = 0;
  int arg_next = 0;
  int initial_colon = 0;

  /* first, deal with silly parameters and easy stuff */
  if (argc == 0 || argv == 0 || (shortopts == 0 && longopts == 0)
      || data->optind >= argc || argv[data->optind] == 0)
    return EOF;
  if (strcmp (argv[data->optind], "--") == 0)
    {
      data->optind++;
      return EOF;
    }

  /* if this is our first time through */
  if (data->optind == 0)
    {
      data->optind = 1;
      data->optwhere = 1;
      data->permute_from = 0;
      data->num_nonopts = 0;
    }

  /* define ordering */
  if (shortopts != 0 && (*shortopts == '-' || *shortopts == '+'))
    {
      ordering = (*shortopts == '-') ? RETURN_IN_ORDER : REQUIRE_ORDER;
      shortopts++;
    }
  else
    ordering = (getenv ("POSIXLY_CORRECT") != 0) ? REQUIRE_ORDER : PERMUTE;

  /* check for initial colon in shortopts */
  if (shortopts != 0 && *shortopts == ':')
    {
      ++shortopts;
      initial_colon = 1;
    }

  /*
   * based on ordering, find our next option, if we're at the beginning of
   * one
   */
  if (data->optwhere == 1)
    {
      switch (ordering)
	{
	default:		/* shouldn't happen */
	case PERMUTE:
	  data->permute_from = data->optind;
	  data->num_nonopts = 0;
	  while (!is_option (argv[data->optind], only))
	    {
	      data->optind++;
	      data->num_nonopts++;
	    }
	  if (argv[data->optind] == 0)
	    {
	      /* no more options */
	      data->optind = data->permute_from;
	      return EOF;
	    }
	  else if (strcmp (argv[data->optind], "--") == 0)
	    {
	      /* no more options, but have to get `--' out of the way */
	      permute (argv + data->permute_from, data->num_nonopts, 1);
	      data->optind = data->permute_from + 1;
	      return EOF;
	    }
	  break;
	case RETURN_IN_ORDER:
	  if (!is_option (argv[data->optind], only))
	    {
	      data->optarg = argv[data->optind++];
	      return (data->optopt = 1);
	    }
	  break;
	case REQUIRE_ORDER:
	  if (!is_option (argv[data->optind], only))
	    return EOF;
	  break;
	}
    }
  /* End of option list? */
  if (argv[data->optind] == 0)
    return EOF;

  /* we've got an option, so parse it */

  /* first, is it a long option? */
  if (longopts != 0
      && (memcmp (argv[data->optind], "--", 2) == 0
	  || (only && argv[data->optind][0] == '+')) && data->optwhere == 1)
    {
      /* handle long options */
      if (memcmp (argv[data->optind], "--", 2) == 0)
	data->optwhere = 2;
      longopt_match = -1;
      possible_arg = strchr (argv[data->optind] + data->optwhere, '=');
      if (possible_arg == 0)
	{
	  /* no =, so next argv might be arg */
	  match_chars = strlen (argv[data->optind]);
	  possible_arg = argv[data->optind] + match_chars;
	  match_chars = match_chars - data->optwhere;
	}
      else
	match_chars = (possible_arg - argv[data->optind]) - data->optwhere;
      for (optindex = 0; longopts[optindex].name != 0; ++optindex)
	{
	  if (memcmp
	      (argv[data->optind] + data->optwhere, longopts[optindex].name,
	       match_chars) == 0)
	    {
	      /* do we have an exact match? */
	      if (match_chars == strlen (longopts[optindex].name))
		{
		  longopt_match = optindex;
		  break;
		}
	      /* do any characters match? */
	      else
		{
		  if (longopt_match < 0)
		    longopt_match = optindex;
		  else
		    {
		      /* we have ambiguous options */
		      if (data->opterr)
			{
			  fputs (argv[0], stderr);
			  fputs (": option `", stderr);
			  fputs (argv[data->optind], stderr);
			  fputs ("' is ambiguous (could be `--", stderr);
			  fputs (longopts[longopt_match].name, stderr);
			  fputs ("' or `--", stderr);
			  fputs (longopts[optindex].name, stderr);
			  fputs ("')\n", stderr);
			}
		      return (data->optopt = '?');
		    }
		}
	    }
	}
      if (longopt_match >= 0)
	has_arg = longopts[longopt_match].has_arg;
    }

  /* if we didn't find a long option, is it a short option? */
  if (longopt_match < 0 && shortopts != 0)
    {
      cp = strchr (shortopts, argv[data->optind][data->optwhere]);
      if (cp == 0)
	{
	  /* couldn't find option in shortopts */
	  if (data->opterr)
	    {
	      fputs (argv[0], stderr);
	      fputs (": invalid option -- `-", stderr);
	      fputc (argv[data->optind][data->optwhere], stderr);
	      fputs ("'\n", stderr);
	    }
	  data->optwhere++;
	  if (argv[data->optind][data->optwhere] == '\0')
	    {
	      data->optind++;
	      data->optwhere = 1;
	    }
	  return (data->optopt = '?');
	}
      has_arg = ((cp[1] == ':')
		 ? ((cp[2] == ':') ? OPTIONAL_ARG : REQUIRED_ARG) : NO_ARG);
      possible_arg = argv[data->optind] + data->optwhere + 1;
      data->optopt = *cp;
    }

  /* get argument and reset data->optwhere */
  arg_next = 0;
  switch (has_arg)
    {
    case OPTIONAL_ARG:
      if (*possible_arg == '=')
	possible_arg++;
      data->optarg = (*possible_arg != '\0') ? possible_arg : 0;
      data->optwhere = 1;
      break;
    case REQUIRED_ARG:
      if (*possible_arg == '=')
	possible_arg++;
      if (*possible_arg != '\0')
	{
	  data->optarg = possible_arg;
	  data->optwhere = 1;
	}
      else if (data->optind + 1 >= argc)
	{
	  if (data->opterr)
	    {
	      fputs (argv[0], stderr);
	      fputs (": argument required for option `-", stderr);
	      if (longopt_match >= 0)
		{
		  fputc ('-', stderr);
		  fputs (longopts[longopt_match].name, stderr);
		  data->optopt = initial_colon ? ':' : '\?';
		}
	      else
		{
		  fputc (*cp, stderr);
		  data->optopt = *cp;
		}
	      fputs ("'\n", stderr);
	    }
	  data->optind++;
	  return initial_colon ? ':' : '\?';
	}
      else
	{
	  data->optarg = argv[data->optind + 1];
	  arg_next = 1;
	  data->optwhere = 1;
	}
      break;
    default:			/* shouldn't happen */
    case NO_ARG:
      if (longopt_match < 0)
	{
	  data->optwhere++;
	  if (argv[data->optind][data->optwhere] == '\0')
	    data->optwhere = 1;
	}
      else
	data->optwhere = 1;
      data->optarg = 0;
      break;
    }

  /* do we have to permute or otherwise modify data->optind? */
  if (ordering == PERMUTE && data->optwhere == 1 && data->num_nonopts != 0)
    {
      permute (argv + data->permute_from, data->num_nonopts, 1 + arg_next);
      data->optind = data->permute_from + 1 + arg_next;
    }
  else if (data->optwhere == 1)
    data->optind = data->optind + 1 + arg_next;

  /* finally return */
  if (longopt_match >= 0)
    {
      if (longind != 0)
	*longind = longopt_match;
      if (longopts[longopt_match].flag != 0)
	{
	  *(longopts[longopt_match].flag) = longopts[longopt_match].val;
	  return 0;
	}
      else
	return longopts[longopt_match].val;
    }
  else
    return data->optopt;
}

int
getopt (int argc, char *const argv[], const char *optstring)
{
  struct getopt_data data;
  int r;

  read_globals (&data);
  r = getopt_internal (argc, argv, optstring, 0, 0, 0, &data);
  write_globals (&data);
  return r;
}

int
getopt_long (int argc, char *const argv[], const char *shortopts,
	     const struct option *longopts, int *longind)
{
  struct getopt_data data;
  int r;

  read_globals (&data);
  r = getopt_internal (argc, argv, shortopts, longopts, longind, 0, &data);
  write_globals (&data);
  return r;
}

int
getopt_long_only (int argc, char *const argv[], const char *shortopts,
		  const struct option *longopts, int *longind)
{
  struct getopt_data data;
  int r;

  read_globals (&data);
  r = getopt_internal (argc, argv, shortopts, longopts, longind, 1, &data);
  write_globals (&data);
  return r;
}

int
__getopt_r (int argc, char *const argv[], const char *optstring,
	    struct getopt_data *data)
{
  return getopt_internal (argc, argv, optstring, 0, 0, 0, data);
}

int
__getopt_long_r (int argc, char *const argv[], const char *shortopts,
		 const struct option *longopts, int *longind,
		 struct getopt_data *data)
{
  return getopt_internal (argc, argv, shortopts, longopts, longind, 0, data);
}

int
__getopt_long_only_r (int argc, char *const argv[], const char *shortopts,
		      const struct option *longopts, int *longind,
		      struct getopt_data *data)
{
  return getopt_internal (argc, argv, shortopts, longopts, longind, 1, data);
}

#endif /* !HAVE_GETOPT */

/* end of file GETOPT.C */
