/* dump_setup.cc

This file is part of Cygwin.

This software is a copyrighted work licensed under the terms of the
Cygwin license.  Please consult the file "CYGWIN_LICENSE" for
details. */

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <stdlib.h>
#include <string.h>
#include <io.h>
#include <sys/stat.h>
#include <errno.h>
#define WIN32_NO_STATUS	/* Disable status codes in winnt.h since we include
			   ntstatus.h for extended status codes below. */
#include <windows.h>
#undef WIN32_NO_STATUS
#include <winternl.h>
#include <ntstatus.h>
#include "path.h"
#include <zlib.h>

static int package_len = 20;
static unsigned int version_len = 10;


typedef struct
{
  char pkgtar[MAX_PATH + 1];
  char pkg[MAX_PATH + 1];
  char ver[MAX_PATH + 1];
  char tail[MAX_PATH + 1];
  char what[16];
} fileparse;

static int
find_tar_ext (const char *path)
{
  char *p = strchr (path, '\0') - 9;
  if (p <= path)
    return 0;
  if ((p = strstr (p, ".tar")) != NULL)
    return p - path;
  else
    return 0;
}

/* Parse a filename into package, version, and extension components. */
int
parse_filename (const char *in_fn, fileparse& f)
{
  char *p, *ver;
  char fn[strlen (in_fn) + 1];

  strcpy (fn, in_fn);
  int n = find_tar_ext (fn);

  if (!n)
    return 0;

  strcpy (f.tail, fn + n);
  fn[n] = '\0';
  f.pkg[0] = f.what[0] = '\0';
  p = fn;
  for (ver = p; *ver; ver++)
    if (*ver != '-')
      continue;
    else if (isdigit (ver[1]))
      {
	*ver++ = '\0';
	strcpy (f.pkg, p);
	break;
      }
    else if (strcasecmp (ver, "-src") == 0 ||
	     strcasecmp (ver, "-patch") == 0)
      {
	size_t len;

	*ver++ = '\0';
	strcpy (f.pkg, p);
	strcpy (f.what, strlwr (ver));
	strcpy (f.pkgtar, p);
	len = strlen (f.pkgtar);
	strncpy (f.pkgtar + len, f.tail, sizeof (f.pkgtar) - len);
	f.pkgtar[MAX_PATH] = '\0';
	ver = strchr (ver, '\0');
	break;
      }

  if (!f.pkg[0])
    strcpy (f.pkg, p);

  if (!f.what[0])
    {
      int n;
      p = strchr (ver, '\0');
      strcpy (f.pkgtar, in_fn);
      if ((p -= 4) >= ver && strcasecmp (p, "-src") == 0)
	n = 4;
      else if ((p -= 2) >= ver && strcasecmp (p, "-patch") == 0)
	n = 6;
      else
	n = 0;
      if (n)
	{
	  strcpy (f.what, p + 1);
	  *p = '\0';
	  p = f.pkgtar + (p - fn) + n;
	  memmove (p - 4, p, strlen (p));
	}
    }

  strcpy (f.ver, *ver ? ver : "0.0");
  return 1;
}

static bool
dump_file (const char *msg, const char *fn)
{
  char buf[4096];
  bool printed = false;
  bool found = false;
  size_t len = strlen (fn);
  char *path = cygpath ("/etc/setup/setup.rc", NULL);
  FILE *fp = fopen (path, "rt");

  if (fp)
    {
      while (fgets (buf, 4096, fp))
      	{
	  if (found)
	    {
	      char *bufp = buf;

	      if (*bufp == '\t')
	      	++bufp;
	      char *p = strchr (bufp, '\0');
	      printf ("%s%s%s", msg, bufp,
				(p == bufp) || p[-1] != '\n' ? "\n" : "");
	      printed = true;
	      break;
	    }
	  if (!strncmp (buf, fn, len) && buf[len] == '\n')
	    found = true;
	}
      fclose (fp);
    }
  return printed;
}

struct pkgver
{
  char *name;
  char *ver;
};

extern "C" {
int
compar (const void *a, const void *b)
{
  const pkgver *pa = (const pkgver *) a;
  const pkgver *pb = (const pkgver *) b;
  return strcasecmp (pa->name, pb->name);
}
}

int
match_argv (char **argv, const char *name)
{
  if (!argv || !*argv)
    return -1;
  for (char **a = argv; *a; a++)
    if (strcasecmp (*a, name) == 0)
      return a - argv + 1;
  return 0;
}

static bool
could_not_access (int verbose, char *filename, char *package, const char *type)
{
  switch (errno)
    {
      case ENOTDIR:
	break;
      case ENOENT:
	if (verbose)
	  printf ("Missing %s: /%s from package %s\n",
		  type, filename, package);
	return true;
      case EACCES:
	if (verbose)
	  printf ("Unable to access %s /%s from package %s\n",
		  type, filename, package);
	return true;
    }
  return false;
}

static const WCHAR tfx_chars[] = {
	    0, 0xf000 |   1, 0xf000 |   2, 0xf000 |   3,
 0xf000 |   4, 0xf000 |   5, 0xf000 |   6, 0xf000 |   7,
 0xf000 |   8, 0xf000 |   9, 0xf000 |  10, 0xf000 |  11,
 0xf000 |  12, 0xf000 |  13, 0xf000 |  14, 0xf000 |  15,
 0xf000 |  16, 0xf000 |  17, 0xf000 |  18, 0xf000 |  19,
 0xf000 |  20, 0xf000 |  21, 0xf000 |  22, 0xf000 |  23,
 0xf000 |  24, 0xf000 |  25, 0xf000 |  26, 0xf000 |  27,
 0xf000 |  28, 0xf000 |  29, 0xf000 |  30, 0xf000 |  31,
	  ' ',          '!', 0xf000 | '"',          '#',
	  '$',          '%',          '&',           39,
	  '(',          ')', 0xf000 | '*',          '+',
	  ',',          '-',          '.',          '\\',
	  '0',          '1',          '2',          '3',
	  '4',          '5',          '6',          '7',
	  '8',          '9', 0xf000 | ':',          ';',
 0xf000 | '<',          '=', 0xf000 | '>', 0xf000 | '?',
	  '@',          'A',          'B',          'C',
	  'D',          'E',          'F',          'G',
	  'H',          'I',          'J',          'K',
	  'L',          'M',          'N',          'O',
	  'P',          'Q',          'R',          'S',
	  'T',          'U',          'V',          'W',
	  'X',          'Y',          'Z',          '[',
	  '\\',          ']',          '^',          '_',
	  '`',          'a',          'b',          'c',
	  'd',          'e',          'f',          'g',
	  'h',          'i',          'j',          'k',
	  'l',          'm',          'n',          'o',
	  'p',          'q',          'r',          's',
	  't',          'u',          'v',          'w',
	  'x',          'y',          'z',          '{',
 0xf000 | '|',          '}',          '~',          127
};

static void
transform_chars (PWCHAR path, PWCHAR path_end)
{
  for (; path <= path_end; ++path)
    if (*path < 128)
      *path = tfx_chars[*path];
}

extern "C" NTAPI NTSTATUS NtQueryAttributesFile (POBJECT_ATTRIBUTES,
						 PFILE_BASIC_INFORMATION);

/* This function checks for file existance and fills the stat structure
   with only the required mode info.  We're using a native NT function
   here, otherwise we wouldn't be able to check for files with special
   characters not valid in Win32, and espacially not valid using the
   ANSI API. */
static int
simple_nt_stat (const char *filename, struct stat *st)
{
  size_t len = mbstowcs (NULL, filename, 0) + 1;
  WCHAR path[len + 8];	/* Enough space for the NT prefix */
  PWCHAR p = path;
  UNICODE_STRING upath;
  OBJECT_ATTRIBUTES attr;
  FILE_BASIC_INFORMATION fbi;
  NTSTATUS status;

  wcscpy (p, L"\\??\\");
  p += 4;
  if (filename[0] == '\\' && filename[1] == '\\')
    {
      wcscpy (p, L"UNC");
      p += 3;
      p += mbstowcs (p, filename + 1, len);
    }
  else
    p += mbstowcs (p, filename, len);
  /* Remove trailing backslashes.  NT functions don't like them. */
  if (p[-1] == L'\\')
    *--p = L'\0';
  /* Skip prefix and drive, otherwise question marks and colons are converted
     as well. */
  transform_chars (path + 7, p);
  RtlInitUnicodeString (&upath, path);
  InitializeObjectAttributes (&attr, &upath, OBJ_CASE_INSENSITIVE, NULL, NULL);
  status = NtQueryAttributesFile (&attr, &fbi);
  if (NT_SUCCESS (status))
    {
      st->st_mode = (fbi.FileAttributes & FILE_ATTRIBUTE_DIRECTORY)
		    ? S_IFDIR : S_IFREG;
      return 0;
    }
  if (status == STATUS_OBJECT_PATH_NOT_FOUND
      || status == STATUS_OBJECT_NAME_INVALID
      || status == STATUS_BAD_NETWORK_PATH
      || status == STATUS_BAD_NETWORK_NAME
      || status == STATUS_NO_MEDIA_IN_DEVICE
      || status == STATUS_OBJECT_NAME_NOT_FOUND
      || status == STATUS_NO_SUCH_FILE)
    errno = ENOENT;
  else
    errno = EACCES;
  return -1;
}

static bool
directory_exists (int verbose, char *filename, char *package)
{
  struct stat status;
  if (simple_nt_stat(cygpath("/", filename, NULL), &status))
    {
      if (could_not_access (verbose, filename, package, "directory"))
	return false;
    }
  else if (!S_ISDIR(status.st_mode))
    {
      if (verbose)
	printf ("Directory/file mismatch: /%s from package %s\n", filename, package);
      return false;
    }
  return true;
}

static bool
file_exists (int verbose, char *filename, const char *alt, char *package)
{
  struct stat status;
  if (simple_nt_stat(cygpath("/", filename, NULL), &status) &&
      (!alt || simple_nt_stat(cygpath("/", filename, alt, NULL), &status)))
    {
      if (could_not_access (verbose, filename, package, "file"))
	return false;
    }
  else if (!S_ISREG(status.st_mode))
    {
      if (verbose)
	printf ("File type mismatch: /%s from package %s\n", filename, package);
      return false;
    }
  return true;
}

static gzFile
open_package_list (char *package)
{
  char filelist[MAX_PATH + 1] = "/etc/setup/";
  strcat (strcat (filelist, package), ".lst.gz");
  if (!file_exists (false, filelist + 1, NULL, NULL))
    return NULL;

  gzFile fp;
#ifndef ZLIB_VERSION
  fp = NULL;
#else
  char *fn = cygpath (filelist, NULL);
  fp = gzopen (fn, "rb9");
  free (fn);
#endif

  return fp;
}

static bool
check_package_files (int verbose, char *package)
{
  gzFile fp = open_package_list (package);
  if (!fp)
    {
      if (verbose)
	printf ("Empty package %s\n", package);
      return true;
    }

  bool result = true;
  char buf[MAX_PATH + 1];
  while (gzgets (fp, buf, MAX_PATH))
    {
      char *filename = strtok(buf, "\n");

      if (*filename == '/')
	++filename;
      else if (!strncmp (filename, "./", 2))
	filename += 2;

      if (filename[strlen (filename) - 1] == '/')
	{
	  if (!directory_exists (verbose, filename, package))
	    result = false;
	}
      else if (strstr (filename, "/postinstall/"))
	{
	  if (!file_exists (verbose, filename, ".done", package))
	    result = false;
	}
      else
	{
	  if (!file_exists (verbose, filename, ".lnk", package))
	    result = false;
	}
    }

  gzclose (fp);
  return result;
}

/**
 * Returns a calloc'd sorted list of packages or NULL if no info.
 * The last entry in the list is {NULL,NULL}.
 */
static pkgver *
get_packages (char **argv)
{
  char *setup = cygpath ("/etc/setup/installed.db", NULL);
  FILE *fp = fopen (setup, "rt");

  if (fp == NULL)
    return NULL;

  int nlines;
  nlines = 0;
  char buf[4096];
  while (fgets (buf, 4096, fp))
    nlines += 2;	/* potentially binary + source */
  if (!nlines)
    {
      fclose (fp);
      return NULL;
    }
  rewind (fp);

  pkgver *packages;

  packages = (pkgver *) calloc (nlines + 1, sizeof(packages[0]));
  int n;
  for (n = 0; fgets (buf, 4096, fp) && n < nlines;)
    {
      char *package = strtok (buf, " ");
      if (!package || !*package || !match_argv (argv, package))
	continue;
      for (int i = 0; i < 2; i++)
	{
	  fileparse f;
	  char *tar = strtok (NULL, " ");
	  if (!tar || !*tar || !parse_filename (tar, f))
	    break;

	  int len = strlen (package);
	  if (f.what[0])
	    len += strlen (f.what) + 1;
	  if (len > package_len)
	    package_len = len;
	  packages[n].name = (char *) malloc (len + 1);
	  strcpy (packages[n].name, package);
	  if (f.what[0])
	    strcat (strcat (packages[n].name, "-"), f.what);
	  packages[n].ver = strdup (f.ver);
	  if (strlen(f.ver) > version_len)
	    version_len = strlen(f.ver);
	  n++;
	  if (strtok (NULL, " ") == NULL)
	    break;
	}
    }

  packages[n].name = packages[n].ver = NULL;

  qsort (packages, n, sizeof (packages[0]), compar);

  fclose (fp);

  return packages;
}

void
dump_setup (int verbose, char **argv, bool check_files)
{
  pkgver *packages = get_packages(argv);

  puts ("Cygwin Package Information");
  if (packages == NULL)
    {
      puts ("No setup information found");
      return;
    }

  if (verbose)
    {
      bool need_nl = dump_file ("Last downloaded files to: ", "last-cache");
      if (dump_file ("Last downloaded files from: ", "last-mirror") || need_nl)
	puts ("");
    }

  printf ("%-*s %-*s%s\n", package_len, "Package",
			   check_files ? version_len : 7, "Version",
			   check_files ? "     Status" : "");
  for (int i = 0; packages[i].name; i++)
    {
      if (check_files)
	printf ("%-*s %-*s%s\n", package_len, packages[i].name,
		version_len, packages[i].ver,
		check_package_files (verbose, packages[i].name)
		  ? "     OK" : "     Incomplete");
      else
	printf ("%-*s %s\n", package_len, packages[i].name, packages[i].ver);
      fflush(stdout);
    }

  free (packages);

  return;
}

void
package_list (int verbose, char **argv)
{
  pkgver *packages = get_packages(argv);
  if (packages == NULL)
    {
      puts ("No setup information found");
      return;
    }

  for (int i = 0; packages[i].name; i++)
    {
      gzFile fp = open_package_list (packages[i].name);
      if (!fp)
	{
	  if (verbose)
	    printf ("Can't open file list /etc/setup/%s.lst.gz for package %s\n",
		packages[i].name, packages[i].name);
	  continue;
	}

      if (verbose)
	printf ("Package: %s-%s\n", packages[i].name, packages[i].ver);

      char buf[MAX_PATH + 1];
      while (gzgets (fp, buf, MAX_PATH))
	{
	  char *lastchar = strchr(buf, '\n');
	  if (lastchar[-1] != '/')
	    printf ("%s/%s", (verbose?"    ":""), buf);
	}

      gzclose (fp);
    }

  free (packages);

  return;
}

void
package_find (int verbose, char **argv)
{
  pkgver *packages = get_packages(NULL);
  if (packages == NULL)
    {
      puts ("No setup information found");
      return;
    }

  for (int i = 0; packages[i].name; i++)
    {
      gzFile fp = open_package_list (packages[i].name);
      if (!fp)
	continue;

      char buf[MAX_PATH + 2];
      buf[0] = '/';
      while (gzgets (fp, buf + 1, MAX_PATH))
	{
	  char *filename = strtok(buf, "\n");
	  int flen = strlen (filename);
	  if (filename[flen - 1] != '/')
	    {
	      // FIXME: verify that /bin is mounted on /usr/bin; ditto for /lib
	      bool is_alias = !strncmp(filename, "/usr/bin/", 9) ||
			      !strncmp(filename, "/usr/lib/", 9);
	      int a = match_argv (argv, filename);
	      if (!a && is_alias)
		a = match_argv (argv, filename + 4);
	      if (!a && !strcmp(filename + flen - 4, ".exe"))
		{
		  filename[flen - 4] = '\0';
		  a = match_argv (argv, filename);
		}
	      if (!a && is_alias)
		a = match_argv (argv, filename + 4);
	      if (a > 0)
		{
		  if (verbose)
		    printf ("%s: found in package ", filename);
		  printf ("%s-%s\n", packages[i].name, packages[i].ver);
		}
	    }
	}

      gzclose (fp);
    }

  free (packages);

  return;
}

