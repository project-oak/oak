/* path.cc: path support.

  This file is part of Cygwin.

  This software is a copyrighted work licensed under the terms of the
  Cygwin license.  Please consult the file "CYGWIN_LICENSE" for
  details. */

  /* This module's job is to
     - convert between POSIX and Win32 style filenames,
     - support the `mount' functionality,
     - support symlinks for files and directories

     Pathnames are handled as follows:

     - A \ or : in a path denotes a pure windows spec.
     - Paths beginning with // (or \\) are not translated (i.e. looked
       up in the mount table) and are assumed to be UNC path names.

     The goal in the above set of rules is to allow both POSIX and Win32
     flavors of pathnames without either interfering.  The rules are
     intended to be as close to a superset of both as possible.

     Note that you can have more than one path to a file.  The mount
     table is always prefered when translating Win32 paths to POSIX
     paths.  Win32 paths in mount table entries may be UNC paths or
     standard Win32 paths starting with <drive-letter>:

     Text vs Binary issues are not considered here in path style
     decisions, although the appropriate flags are retrieved and
     stored in various structures.

     Removing mounted filesystem support would simplify things greatly,
     but having it gives us a mechanism of treating disk that lives on a
     UNIX machine as having UNIX semantics [it allows one to edit a text
     file on that disk and not have cr's magically appear and perhaps
     break apps running on UNIX boxes].  It also useful to be able to
     layout a hierarchy without changing the underlying directories.

     The semantics of mounting file systems is not intended to precisely
     follow normal UNIX systems.

     Each DOS drive is defined to have a current directory.  Supporting
     this would complicate things so for now things are defined so that
     c: means c:\.
  */

/* This file includes both the XPG and GNU basename functions, with the
   former exported as "basename" for ABI compatibility but the latter
   declared as such for source compatibility with glibc.  This tells
   <string.h> not to declare the GNU variant in order to prevent a conflicting
   declaration error with the XPG variant implemented herein. */
#define basename basename
#include "winsup.h"
#include <w32api/winioctl.h>
#include <w32api/shlobj.h>
#include <sys/param.h>
#include <sys/cygwin.h>
#include <wctype.h>
#include <assert.h>
#include "cygerrno.h"
#include "path.h"
#include "fhandler.h"
#include "dtable.h"
#include "cygheap.h"
#include "shared_info.h"
#include "tls_pbuf.h"
#include "environ.h"
#undef basename

suffix_info stat_suffixes[] =
{
  suffix_info ("", 1),
  suffix_info (".exe", 1),
  suffix_info (NULL)
};

struct symlink_info
{
  char contents[SYMLINK_MAX + 1];
  char *ext_here;
  int extn;
  unsigned path_flags;
  unsigned mount_flags;
  unsigned pc_flags;	/* Relevant pathconv_arg flags from path_conv caller */
  DWORD fileattr;
  int issymlink;
  bool ext_tacked_on;
  int error;
  bool isdevice;
  _major_t major;
  _minor_t minor;
  __mode_t mode;
  int check (char *path, const suffix_info *suffixes, fs_info &fs,
	     path_conv_handle &conv_hdl);
  int set (char *path);
  bool parse_device (const char *);
  int check_sysfile (HANDLE h);
  int check_shortcut (HANDLE h);
  int check_reparse_point (HANDLE h, bool remote);
  int check_nfs_symlink (HANDLE h);
  int posixify (char *srcbuf);
  bool set_error (int);
};

SRWLOCK NO_COPY cwdstuff::cwd_lock;

static const GUID GUID_shortcut
			= { 0x00021401L, 0, 0, {0xc0, 0, 0, 0, 0, 0, 0, 0x46}};

enum
{
  WSH_FLAG_IDLIST = 0x01,	/* Contains an ITEMIDLIST. */
  WSH_FLAG_FILE = 0x02,		/* Contains a file locator element. */
  WSH_FLAG_DESC = 0x04,		/* Contains a description. */
  WSH_FLAG_RELPATH = 0x08,	/* Contains a relative path. */
  WSH_FLAG_WD = 0x10,		/* Contains a working dir. */
  WSH_FLAG_CMDLINE = 0x20,	/* Contains command line args. */
  WSH_FLAG_ICON = 0x40		/* Contains a custom icon. */
};

struct win_shortcut_hdr
{
  DWORD size;		/* Header size in bytes.  Must contain 0x4c. */
  GUID magic;		/* GUID of shortcut files. */
  DWORD flags;	/* Content flags.  See above. */

  /* The next fields from attr to icon_no are always set to 0 in Cygwin
     and U/Win shortcuts. */
  DWORD attr;	/* Target file attributes. */
  FILETIME ctime;	/* These filetime items are never touched by the */
  FILETIME mtime;	/* system, apparently. Values don't matter. */
  FILETIME atime;
  DWORD filesize;	/* Target filesize. */
  DWORD icon_no;	/* Icon number. */

  DWORD run;		/* Values defined in winuser.h. Use SW_NORMAL. */
  DWORD hotkey;	/* Hotkey value. Set to 0.  */
  DWORD dummy[2];	/* Future extension probably. Always 0. */
};

/* Return non-zero if PATH1 is a prefix of PATH2.
   Both are assumed to be of the same path style and / vs \ usage.
   Neither may be "".
   LEN1 = strlen (PATH1).  It's passed because often it's already known.

   Examples:
   /foo/ is a prefix of /foo  <-- may seem odd, but desired
   /foo is a prefix of /foo/
   / is a prefix of /foo/bar
   / is not a prefix of foo/bar
   foo/ is a prefix foo/bar
   /foo is not a prefix of /foobar
*/

int
path_prefix_p (const char *path1, const char *path2, int len1,
	       bool caseinsensitive)
{
  /* Handle case where PATH1 has trailing '/' and when it doesn't.  */
  if (len1 > 0 && isdirsep (path1[len1 - 1]))
    len1--;

  if (len1 == 0)
    return isdirsep (path2[0]) && !isdirsep (path2[1]);

  if (isdirsep (path2[len1]) || path2[len1] == 0 || path1[len1 - 1] == ':')
    return caseinsensitive ? strncasematch (path1, path2, len1)
			   : !strncmp (path1, path2, len1);

  return 0;
}

/* Return non-zero if paths match in first len chars.
   Check is dependent of the case sensitivity setting. */
int
pathnmatch (const char *path1, const char *path2, int len, bool caseinsensitive)
{
  return caseinsensitive
	 ? strncasematch (path1, path2, len) : !strncmp (path1, path2, len);
}

/* Return non-zero if paths match. Check is dependent of the case
   sensitivity setting. */
int
pathmatch (const char *path1, const char *path2, bool caseinsensitive)
{
  return caseinsensitive
	 ? strcasematch (path1, path2) : !strcmp (path1, path2);
}

/* TODO: This function is used in mkdir and rmdir to generate correct
   error messages in case of paths ending in /. or /.. components.
   Right now, normalize_posix_path will just normalize
   those components away, which changes the semantics.  */
bool
has_dot_last_component (const char *dir, bool test_dot_dot)
{
  /* SUSv3: . and .. are not allowed as last components in various system
     calls.  Don't test for backslash path separator since that's a Win32
     path following Win32 rules. */
  const char *last_comp = strchr (dir, '\0');

  if (last_comp == dir)
    return false;	/* Empty string.  Probably shouldn't happen here? */

  /* Detect run of trailing slashes */
  while (last_comp > dir && *--last_comp == '/')
    continue;

  /* Detect just a run of slashes or a path that does not end with a slash. */
  if (*last_comp != '.')
    return false;

  /* We know we have a trailing dot here.  Check that it really is a standalone "."
     path component by checking that it is at the beginning of the string or is
     preceded by a "/" */
  if (last_comp == dir || *--last_comp == '/')
    return true;

  /* If we're not checking for '..' we're done.  Ditto if we're now pointing to
     a non-dot. */
  if (!test_dot_dot || *last_comp != '.')
    return false;		/* either not testing for .. or this was not '..' */

  /* Repeat previous test for standalone or path component. */
  return last_comp == dir || last_comp[-1] == '/';
}

/* Normalize a POSIX path.
   All duplicate /'s, except for 2 leading /'s, are deleted.
   The result is 0 for success, or an errno error value.  */

int
normalize_posix_path (const char *src, char *dst, char *&tail)
{
  const char *in_src = src;
  char *dst_start = dst;
  bool check_parent = false;
  syscall_printf ("src %s", src);

  if ((isdrive (src) && isdirsep (src[2])) || *src == '\\')
    goto win32_path;

  tail = dst;
  if (!isslash (src[0]))
    {
      if (!cygheap->cwd.get (dst))
	return get_errno ();
      tail = strchr (tail, '\0');
      if (isslash (dst[0]) && isslash (dst[1]))
	++dst_start;
      if (*src == '.')
	{
	  if (tail == dst_start + 1 && *dst_start == '/')
	     tail--;
	  goto sawdot;
	}
      if (tail > dst && !isslash (tail[-1]))
	*tail++ = '/';
    }
  /* Two leading /'s?  If so, preserve them.  */
  else if (isslash (src[1]) && !isslash (src[2]))
    {
      *tail++ = *src++;
      ++dst_start;
    }

  while (*src)
    {
      if (*src == '\\')
	goto win32_path;
      /* Strip runs of /'s.  */
      if (!isslash (*src))
	*tail++ = *src++;
      else
	{
	  check_parent = true;
	  while (*++src)
	    {
	      if (isslash (*src))
		continue;

	      if (*src != '.')
		break;

	    sawdot:
	      if (src[1] != '.')
		{
		  if (!src[1])
		    {
		      *tail++ = '/';
		      goto done;
		    }
		  if (!isslash (src[1]))
		    break;
		}
	      else if (src[2] && !isslash (src[2]))
		break;
	      else
		{
		  /* According to POSIX semantics all elements of path must
		     exist.  To follow it, we must validate our path before
		     removing the trailing component.  Check_parent is needed
		     for performance optimization, in order not to verify paths
		     which are already verified. For example this prevents
		     double check in case of foo/bar/../.. */
		  if (check_parent)
		    {
		      if (tail > dst_start) /* Don't check for / or // dir. */
			{
			  *tail = 0;
			  debug_printf ("checking %s before '..'", dst);
			  /* In conjunction with native and NFS symlinks,
			     this call can result in a recursion which eats
			     up our tmp_pathbuf buffers.  This in turn results
			     in a api_fatal call.  To avoid that, we're
			     checking our remaining buffers and return an
			     error code instead.  Note that this only happens
			     if the path contains 15 or more relative native/NFS
			     symlinks with a ".." in the target path. */
			  tmp_pathbuf tp;
			  if (!tp.check_usage (4, 3))
			    return ELOOP;
			  path_conv head (dst, PC_SYM_FOLLOW | PC_POSIX);
			  if (!head.exists ())
			    return ENOENT;
			  if (!head.isdir ())
			    return ENOTDIR;
			  /* At this point, dst is a normalized path.  If the
			     normalized path created by path_conv does not
			     match the normalized path we're just testing, then
			     the path in dst contains native symlinks.  If we
			     just plunge along, removing the previous path
			     component, we may end up removing a symlink from
			     the path and the resulting path will be invalid.
			     So we replace dst with what we found in head
			     instead.  All the work replacing symlinks has been
			     done in that path anyway, so why repeat it? */
			  tail = stpcpy (dst, head.get_posix ());
			}
		      check_parent = false;
		    }
		  while (tail > dst_start && !isslash (*--tail))
		    continue;
		  src++;
		}
	    }

	  *tail++ = '/';
	}
	if ((tail - dst) >= NT_MAX_PATH)
	  {
	    debug_printf ("ENAMETOOLONG = normalize_posix_path (%s)", src);
	    return ENAMETOOLONG;
	  }
    }

done:
  *tail = '\0';

  debug_printf ("%s = normalize_posix_path (%s)", dst, in_src);
  return 0;

win32_path:
  int err = normalize_win32_path (in_src, dst, tail);
  if (!err)
    for (char *p = dst; (p = strchr (p, '\\')); p++)
      *p = '/';
  return err ?: -1;
}

inline void
path_conv::add_ext_from_sym (symlink_info &sym)
{
  if (sym.ext_here && *sym.ext_here)
    {
      suffix = path + sym.extn;
      if (sym.ext_tacked_on)
	strcpy ((char *) suffix, sym.ext_here);
    }
}

static void mkrelpath (char *dst, bool caseinsensitive);

static void
mkrelpath (char *path, bool caseinsensitive)
{
  tmp_pathbuf tp;
  char *cwd_win32 = tp.c_get ();
  if (!cygheap->cwd.get (cwd_win32, 0))
    return;

  unsigned cwdlen = strlen (cwd_win32);
  if (!path_prefix_p (cwd_win32, path, cwdlen, caseinsensitive))
    return;

  size_t n = strlen (path);
  if (n < cwdlen)
    return;

  char *tail = path;
  if (n == cwdlen)
    tail += cwdlen;
  else
    tail += isdirsep (cwd_win32[cwdlen - 1]) ? cwdlen : cwdlen + 1;

  memmove (path, tail, strlen (tail) + 1);
  if (!*path)
    strcpy (path, ".");
}

void
path_conv::set_posix (const char *path_copy)
{
  if (path_copy)
    {
      size_t n = strlen (path_copy) + 1;
      char *p = (char *) crealloc_abort ((void *) posix_path, n);
      posix_path = (const char *) memcpy (p, path_copy, n);
    }
}

static inline void
str2uni_cat (UNICODE_STRING &tgt, const char *srcstr)
{
  int len = sys_mbstowcs (tgt.Buffer + tgt.Length / sizeof (WCHAR),
			  (tgt.MaximumLength - tgt.Length) / sizeof (WCHAR),
			  srcstr);
  if (len)
    tgt.Length += (len - 1) * sizeof (WCHAR);
}

PUNICODE_STRING
get_nt_native_path (const char *path, UNICODE_STRING& upath, bool dos)
{
  upath.Length = 0;
  if (path[0] == '/')		/* special path w/o NT path representation. */
    str2uni_cat (upath, path);
  else if (path[0] != '\\')	/* X:\...  or relative path. */
    {
      if (path[1] == ':')	/* X:\... */
	{
	  RtlAppendUnicodeStringToString (&upath, &ro_u_natp);
	  str2uni_cat (upath, path);
	  /* The drive letter must be upper case. */
	  upath.Buffer[4] = towupper (upath.Buffer[4]);
	  transform_chars (&upath, 7);
	}
      else			/* relative path */
	{
	  str2uni_cat (upath, path);
	  transform_chars (&upath, 0);
	}
    }
  else if (path[1] != '\\')	/* \Device\... */
    str2uni_cat (upath, path);
  else if ((path[2] != '.' && path[2] != '?')
	   || path[3] != '\\')	/* \\server\share\... */
    {
      RtlAppendUnicodeStringToString (&upath, &ro_u_uncp);
      str2uni_cat (upath, path + 2);
      transform_chars (&upath, 8);
    }
  else				/* \\.\device or \\?\foo */
    {
      RtlAppendUnicodeStringToString (&upath, &ro_u_natp);
      str2uni_cat (upath, path + 4);
    }
  if (dos)
    {
      /* Unfortunately we can't just use transform_chars with the tfx_rev_chars
	 table since only leading and trailing spaces and dots are affected.
	 So we step to every backslash and fix surrounding dots and spaces.
	 That makes these broken filesystems a bit slower, but, hey. */
      PWCHAR cp = upath.Buffer + 7;
      PWCHAR cend = upath.Buffer + upath.Length / sizeof (WCHAR);
      while (++cp < cend)
	if (*cp == L'\\')
	  {
	    PWCHAR ccp = cp - 1;
	    while (*ccp == L'.' || *ccp == L' ')
	      *ccp-- |= 0xf000;
	    while (cp[1] == L' ')
	      *++cp |= 0xf000;
	  }
      while (*--cp == L'.' || *cp == L' ')
	*cp |= 0xf000;
    }
  return &upath;
}

/* Handle with extrem care!  Only used in a certain instance in try_to_bin.
   Every other usage needs a careful check. */
void
path_conv::set_nt_native_path (PUNICODE_STRING new_path)
{
  wide_path = (PWCHAR) crealloc_abort (wide_path, new_path->MaximumLength);
  memcpy (wide_path, new_path->Buffer, new_path->Length);
  uni_path.Length = new_path->Length;
  uni_path.MaximumLength = new_path->MaximumLength;
  uni_path.Buffer = wide_path;
}

/* If suffix is not NULL, append the suffix string verbatim.
   This is used by fhandler_mqueue::mq_open to append an NTFS stream suffix. */
PUNICODE_STRING
path_conv::get_nt_native_path (PUNICODE_STRING suffix)
{
  PUNICODE_STRING res;
  if (wide_path)
    res = &uni_path;
  else if (!path)
    res = NULL;
  else
    {
      uni_path.Length = 0;
      uni_path.MaximumLength = (strlen (path) + 10) * sizeof (WCHAR);
      if (suffix)
	uni_path.MaximumLength += suffix->Length;
      wide_path = (PWCHAR) cmalloc_abort (HEAP_STR, uni_path.MaximumLength);
      uni_path.Buffer = wide_path;
      ::get_nt_native_path (path, uni_path, has_dos_filenames_only ());
      if (suffix)
	RtlAppendUnicodeStringToString (&uni_path, suffix);
      res = &uni_path;
    }
  return res;
}

PWCHAR
path_conv::get_wide_win32_path (PWCHAR wc)
{
  get_nt_native_path ();
  if (!wide_path)
    return NULL;
  wcpcpy (wc, wide_path);
  if (wc[1] == L'?')
    wc[1] = L'\\';
  return wc;
}

static DWORD
getfileattr (const char *path, bool caseinsensitive) /* path has to be always absolute. */
{
  tmp_pathbuf tp;
  UNICODE_STRING upath;
  OBJECT_ATTRIBUTES attr;
  FILE_BASIC_INFORMATION fbi;
  NTSTATUS status;
  IO_STATUS_BLOCK io;

  tp.u_get (&upath);
  InitializeObjectAttributes (&attr, &upath,
			      caseinsensitive ? OBJ_CASE_INSENSITIVE : 0,
			      NULL, NULL);
  get_nt_native_path (path, upath, false);

  status = NtQueryAttributesFile (&attr, &fbi);
  if (NT_SUCCESS (status))
    return fbi.FileAttributes;

  if (status != STATUS_OBJECT_NAME_NOT_FOUND
      && status != STATUS_NO_SUCH_FILE) /* File not found on 9x share */
    {
      /* File exists but access denied.  Try to get attribute through
	 directory query. */
      UNICODE_STRING dirname, basename;
      HANDLE dir;
      FILE_BOTH_DIR_INFORMATION fdi;

      RtlSplitUnicodePath (&upath, &dirname, &basename);
      InitializeObjectAttributes (&attr, &dirname,
				  caseinsensitive ? OBJ_CASE_INSENSITIVE : 0,
				  NULL, NULL);
      status = NtOpenFile (&dir, SYNCHRONIZE | FILE_LIST_DIRECTORY,
			   &attr, &io, FILE_SHARE_VALID_FLAGS,
			   FILE_SYNCHRONOUS_IO_NONALERT
			   | FILE_OPEN_FOR_BACKUP_INTENT
			   | FILE_DIRECTORY_FILE);
      if (NT_SUCCESS (status))
	{
	  status = NtQueryDirectoryFile (dir, NULL, NULL, 0, &io,
					 &fdi, sizeof fdi,
					 FileBothDirectoryInformation,
					 TRUE, &basename, TRUE);
	  NtClose (dir);
	  if (NT_SUCCESS (status) || status == STATUS_BUFFER_OVERFLOW)
	    return fdi.FileAttributes;
	}
    }
  SetLastError (RtlNtStatusToDosError (status));
  return INVALID_FILE_ATTRIBUTES;
}

/* Convert an arbitrary path SRC to a pure Win32 path, suitable for
   passing to Win32 API routines.

   If an error occurs, `error' is set to the errno value.
   Otherwise it is set to 0.

   follow_mode values:
	SYMLINK_FOLLOW	    - convert to PATH symlink points to
	SYMLINK_NOFOLLOW    - convert to PATH of symlink itself
	SYMLINK_IGNORE	    - do not check PATH for symlinks
	SYMLINK_CONTENTS    - just return symlink contents
*/

/* TODO: This implementation is only preliminary.  For internal
   purposes it's necessary to have a path_conv::check function which
   takes a UNICODE_STRING src path, otherwise we waste a lot of time
   for converting back and forth.  The below implementation does
   realy nothing but converting to char *, until path_conv handles
   wide-char paths directly. */
void
path_conv::check (const UNICODE_STRING *src, unsigned opt,
		  const suffix_info *suffixes)
{
  tmp_pathbuf tp;
  char *path = tp.c_get ();

  user_shared->warned_msdos = true;
  sys_wcstombs (path, NT_MAX_PATH, src->Buffer, src->Length / sizeof (WCHAR));
  path_conv::check (path, opt, suffixes);
}

void
path_conv::check (const char *src, unsigned opt,
		  const suffix_info *suffixes)
{
  /* The tmp_buf array is used when expanding symlinks.  It is NT_MAX_PATH * 2
     in length so that we can hold the expanded symlink plus a trailer.  */
  tmp_pathbuf tp;
  char *path_copy = tp.c_get ();
  char *pathbuf = tp.c_get ();
  char *tmp_buf = tp.t_get ();
  char *THIS_path = tp.c_get ();
  symlink_info sym;
  bool need_directory = 0;
  bool add_ext = false;
  bool is_relpath;
  char *tail, *path_end;

#if 0
  static path_conv last_path_conv;
  static char last_src[CYG_MAX_PATH];

  if (*last_src && strcmp (last_src, src) == 0)
    {
      *this = last_path_conv;
      return;
    }
#endif

  __try
    {
      int loop = 0;
      mount_flags = 0;
      path_flags = 0;
      suffix = NULL;
      fileattr = INVALID_FILE_ATTRIBUTES;
      caseinsensitive = OBJ_CASE_INSENSITIVE;
      if (wide_path)
	cfree (wide_path);
      wide_path = NULL;
      if (path)
	{
	  cfree (modifiable_path ());
	  path = NULL;
	}
      close_conv_handle ();
      fs.clear ();
      if (posix_path)
	{
	  cfree ((void *) posix_path);
	  posix_path = NULL;
	}
      int component = 0;		// Number of translated components

      if (!(opt & PC_NULLEMPTY))
	error = 0;
      else if (!*src)
	{
	  error = ENOENT;
	  return;
	}

      bool is_msdos = false;
      /* This loop handles symlink expansion.  */
      for (;;)
	{
	  is_relpath = !isabspath (src);
	  error = normalize_posix_path (src, path_copy, tail);
	  if (error > 0)
	    return;
	  if (error < 0)
	    {
	      if (component == 0)
		is_msdos = true;
	      error = 0;
	    }

	  /* Detect if the user was looking for a directory.  We have to strip
	     the trailing slash initially while trying to add extensions but
	     take it into account during processing */
	  if (tail > path_copy + 2 && isslash (tail[-1]))
	    {
	      need_directory = 1;
	      *--tail = '\0';
	    }
	  path_end = tail;

	  /* Scan path_copy from right to left looking either for a symlink
	     or an actual existing file.  If an existing file is found, just
	     return.  If a symlink is found, exit the for loop.
	     Also: be careful to preserve the errno returned from
	     symlink.check as the caller may need it. */
	  /* FIXME: Do we have to worry about multiple \'s here? */
	  component = 0;		// Number of translated components
	  sym.contents[0] = '\0';
	  sym.path_flags = 0;

	  int symlen = 0;

	  /* Make sure to check certain flags on last component only. */
	  for (unsigned pc_flags = opt & (PC_NO_ACCESS_CHECK | PC_KEEP_HANDLE
					 | PC_SYM_FOLLOW | PC_SYM_NOFOLLOW_REP);
	       ;
	       pc_flags = opt & (PC_SYM_FOLLOW | PC_SYM_NOFOLLOW_REP))
	    {
	      const suffix_info *suff;
	      char *full_path;

	      /* Don't allow symlink.check to set anything in the path_conv
		 class if we're working on an inner component of the path */
	      if (component)
		{
		  suff = NULL;
		  full_path = pathbuf;
		}
	      else
		{
		  suff = suffixes;
		  full_path = THIS_path;
		}

    retry_fs_via_processfd:

	      /* Convert to native path spec sans symbolic link info. */
	      error = mount_table->conv_to_win32_path (path_copy, full_path,
						       dev, &sym.mount_flags);

	      if (error)
		return;

	      sym.pc_flags = pc_flags;

	      if (!dev.exists ())
		{
		  error = ENXIO;
		  return;
		}

	      if (iscygdrive_dev (dev))
		{
		  if (!component)
		    fileattr = FILE_ATTRIBUTE_DIRECTORY
			       | FILE_ATTRIBUTE_READONLY;
		  else
		    {
		      fileattr = getfileattr (THIS_path,
					      sym.mount_flags & MOUNT_NOPOSIX);
		      dev = FH_FS;
		    }
		  goto out;
		}
	      else if (isdev_dev (dev))
		{
		  /* Make sure that the path handling goes on as with FH_FS. */
		}
	      else if (isvirtual_dev (dev))
		{
		  /* FIXME: Calling build_fhandler here is not the right way to
			    handle this. */
		  fhandler_virtual *fh = (fhandler_virtual *)
					 build_fh_dev (dev, path_copy);
		  virtual_ftype_t file_type;
		  if (!fh)
		    file_type = virt_none;
		  else
		    {
		      file_type = fh->exists ();
		      if (file_type == virt_symlink
			  || file_type == virt_fdsymlink)
			{
			  fh->fill_filebuf ();
			  symlen = sym.set (fh->get_filebuf ());
			}
		      else if (file_type == virt_fsdir && dev == FH_PROCESSFD)
			{
			  /* FIXME: This is YA bad hack to workaround that
			     we're checking for isvirtual_dev at this point.
			     This should only happen if the file is actually
			     a virtual file, and NOT already if the preceeding
			     path components constitute a virtual file.

			     Anyway, what we do here is this:  If the descriptor
			     symlink points to a dir, and if there are trailing
			     path components, it's actually pointing somewhere
			     else.  The format_process_fd function returns the
			     full path, resolved symlink plus trailing path
			     components, in its filebuf.  This is a POSIX path
			     we know nothing about, so we have to convert it to
			     native again, calling conv_to_win32_path.  Since
			     basically nothing happened yet, just copy it over
			     into full_path and jump back to the
			     conv_to_win32_path call.  What a mess. */
			  stpcpy (path_copy, fh->get_filebuf ());
			  delete fh;
			  goto retry_fs_via_processfd;
			}
		      else if (file_type == virt_none && dev == FH_PROCESSFD)
			{
			  error = get_errno ();
			  if (error)
			    {
			      delete fh;
			      return;
			    }
			}
		      delete fh;
		    }
		  switch (file_type)
		    {
		      case virt_directory:
		      case virt_rootdir:
			if (component == 0)
			  fileattr = FILE_ATTRIBUTE_DIRECTORY;
			break;
		      case virt_file:
			if (component == 0)
			  fileattr = 0;
			break;
		      case virt_fdsymlink:
			/* Allow open/linkat to do the right thing. */
			if (opt & PC_SYM_NOFOLLOW_PROCFD)
			  {
			    opt &= ~PC_SYM_FOLLOW;
			    sym.path_flags |= PATH_RESOLVE_PROCFD;
			  }
			fallthrough;
		      case virt_symlink:
			goto is_virtual_symlink;
		      case virt_pipe:
			if (component == 0)
			  {
			    fileattr = 0;
			    dev.parse (FH_PIPE);
			  }
			break;
		      case virt_socket:
			if (component == 0)
			  {
			    fileattr = 0;
			    dev.parse (FH_SOCKET);
			  }
			break;
		      case virt_fsdir:
		      case virt_fsfile:
			/* Access to real file or directory via block device
			   entry in /proc/sys.  Convert to real file and go with
			   the flow. */
			dev.parse (FH_FS);
			goto is_fs_via_procsys;
		      case virt_blk:
			/* Block special device.  Convert to a /dev/sd* like
			   block device unless the trailing slash has been
			   requested.  In this case, the target is the root
			   directory of the filesystem on this block device.
			   So we convert this to a real file and attach the
			   backslash. */
			if (component == 0)
			  {
			    fileattr = FILE_ATTRIBUTE_DEVICE;
			    if (!need_directory)
			      /* Use a /dev/sd* device number > /dev/sddx.
				 FIXME: Define a new major DEV_ice number. */
			      dev.parse (DEV_SD_HIGHPART_END, 9999);
			    else
			      {
				dev.parse (FH_FS);
				strcat (full_path, "\\");
				fileattr |= FILE_ATTRIBUTE_DIRECTORY;
			      }
			    goto out;
			  }
			break;
		      case virt_chr:
			if (component == 0)
			  fileattr = FILE_ATTRIBUTE_DEVICE;
			break;
		      default:
			if (component == 0)
			  fileattr = INVALID_FILE_ATTRIBUTES;
			goto virtual_component_retry;
		    }
		  if (component == 0 || dev != FH_NETDRIVE)
		    mount_flags |= MOUNT_RO;
		  goto out;
		}
	      /* devn should not be a device.  If it is, then stop parsing. */
	      else if (dev != FH_FS)
		{
		  fileattr = 0;
		  mount_flags = sym.mount_flags;
		  if (component)
		    {
		      error = ENOTDIR;
		      return;
		    }
		  goto out;		/* Found a device.  Stop parsing. */
		}

	      /* If path is only a drivename, Windows interprets it as the
		 current working directory on this drive instead of the root
		 dir which is what we want. So we need the trailing backslash
		 in this case. */
	      if (full_path[0] && full_path[1] == ':' && full_path[2] == '\0')
		{
		  full_path[2] = '\\';
		  full_path[3] = '\0';
		}

	      /* If the incoming path was given in DOS notation, always treat
		 it as caseinsensitive,noacl path.  This must be set before
		 calling sym.check, otherwise the path is potentially treated
		 casesensitive. */
	      if (is_msdos)
		sym.mount_flags |= MOUNT_NOPOSIX | MOUNT_NOACL;

    is_fs_via_procsys:

	      symlen = sym.check (full_path, suff, fs, conv_handle);

    is_virtual_symlink:

	      if (sym.isdevice)
		{
		  if (component)
		    {
		      error = ENOTDIR;
		      return;
		    }
		  dev.parse (sym.major, sym.minor);
		  dev.setfs (1);
		  dev.mode (sym.mode);
		  fileattr = sym.fileattr;
		  goto out;
		}

	      if (sym.path_flags & PATH_SOCKET)
		{
		  if (component)
		    {
		      error = ENOTDIR;
		      return;
		    }
		  fileattr = sym.fileattr;
#ifdef __WITH_AF_UNIX
		  dev.parse ((sym.path_flags & PATH_REP) ? FH_UNIX : FH_LOCAL);
#else
		  dev.parse (FH_LOCAL);
#endif /* __WITH_AF_UNIX */
		  dev.setfs (1);
		  mount_flags = sym.mount_flags;
		  path_flags = sym.path_flags;
		  goto out;
		}

	      if (!component)
		{
		  /* Make sure that /dev always exists. */
		  fileattr = isdev_dev (dev) ? FILE_ATTRIBUTE_DIRECTORY
					     : sym.fileattr;
		  mount_flags = sym.mount_flags;
		  path_flags = sym.path_flags;
		}
	      else if (isdev_dev (dev))
		{
		  /* If we're looking for a non-existing file below /dev,
		     make sure that the device type is converted to FH_FS, so
		     that subsequent code handles the file correctly.  Unless
		     /dev itself doesn't exist on disk.  In that case /dev
		     is handled as virtual filesystem, and virtual filesystems
		     are read-only.  The PC_KEEP_HANDLE check allows to check
		     for a call from an informational system call.  In that
		     case we just stick to ENOENT, and the device type doesn't
		     matter anyway. */
		  if (sym.error == ENOENT && !(opt & PC_KEEP_HANDLE))
		    sym.error = EROFS;
		  else
		    dev = FH_FS;
		}

	      /* If symlink.check found an existing non-symlink file, then
		 it sets the appropriate flag.  It also sets any suffix found
		 into `ext_here'. */
	      if (!sym.issymlink && sym.fileattr != INVALID_FILE_ATTRIBUTES)
		{
		  error = sym.error;
		  if (component == 0)
		    add_ext = true;
		  else if (!(sym.fileattr & FILE_ATTRIBUTE_DIRECTORY))
		    {
		      error = ENOTDIR;
		      goto out;
		    }
		  goto out;	// file found
		}
	      /* Found a symlink if symlen > 0 or short-circuited a native
		 symlink or junction point if symlen < 0.
		 If symlen > 0 and component == 0, then the src path itself
		 was a symlink.  If !follow_mode then we're done.  Otherwise
		 we have to insert the path found into the full path that we
		 are building and perform all of these operations again on the
		 newly derived path. */
	      else if (symlen)
		{
		  /* if symlen is negativ, the actual native symlink or
		      junction point is an inner path component.  Just fix up
		      symlen to be positive and don't try any PC_SYM_FOLLOW
		      handling. */
		  if (symlen < 0)
		    symlen = -symlen;
		  else if (component == 0
			   && (!(opt & PC_SYM_FOLLOW)
			       || (is_winapi_reparse_point ()
				   && (opt & PC_SYM_NOFOLLOW_REP))))
		    {
		      /* Usually a trailing slash requires to follow a symlink,
			 even with PC_SYM_NOFOLLOW.  The reason is that "foo/"
			 is equivalent to "foo/." so the symlink is in fact not
			 the last path component.

			 PC_SYM_NOFOLLOW_DIR is used to indicate that the
			 last path component is the target symlink and the
			 trailing slash is supposed to be ignored. */
		      if (!need_directory || (opt & PC_SYM_NOFOLLOW_DIR))
			{
			  /* last component of path is a symlink. */
			  set_symlink (symlen);
			  /* make sure not to set errno to ENOTDIR. */
			  need_directory = 0;
			  if (opt & PC_SYM_CONTENTS)
			    {
			      strcpy (THIS_path, sym.contents);
			      goto out;
			    }
			  add_ext = true;
			  goto out;
			}
		    }
		  /* Following a symlink we can't trust the collected
		     filesystem information any longer. */
		  fs.clear ();
		  /* Close handle, if we have any.  Otherwise we're collecting
		     handles while following symlinks. */
		  conv_handle.close ();
		  break;
		}
	      else if (sym.error && sym.error != ENOENT)
		{
		  error = sym.error;
		  goto out;
		}
	      /* No existing file found. */

    virtual_component_retry:
	      /* Find the new "tail" of the path, e.g. in '/for/bar/baz',
		 /baz is the tail. */
	      if (tail != path_end)
		*tail = '/';
	      while (--tail > path_copy + 1 && *tail != '/') {}
	      /* Exit loop if there is no tail or we are at the
		 beginning of a UNC path */
	      if (tail <= path_copy + 1)
		goto out;	// all done

	      /* Haven't found an existing pathname component yet.
		 Pinch off the tail and try again. */
	      *tail = '\0';
	      component++;
	    }

	  /* Arrive here if above loop detected a symlink. */
	  if (++loop > SYMLOOP_MAX)
	    {
	      error = ELOOP;   // Eep.
	      return;
	    }

	  /* Place the link content, possibly with head and/or tail,
	     in tmp_buf */

	  char *headptr;
	  if (isabspath (sym.contents))
	    headptr = tmp_buf;	/* absolute path */
	  else
	    {
	      /* Copy the first part of the path (with ending /) and point to
		 the end. */
	      char *prevtail = tail;
	      while (--prevtail > path_copy  && *prevtail != '/') {}
	      int headlen = prevtail - path_copy + 1;;
	      memcpy (tmp_buf, path_copy, headlen);
	      headptr = &tmp_buf[headlen];
	    }

	  /* Make sure there is enough space */
	  if (headptr + symlen >= tmp_buf + (2 * NT_MAX_PATH))
	    {
	    too_long:
	      error = ENAMETOOLONG;
	      set_path ("::ENAMETOOLONG::");
	      return;
	    }

	 /* Copy the symlink contents to the end of tmp_buf.
	    Convert slashes. */
	  for (char *p = sym.contents; *p; p++)
	    *headptr++ = *p == '\\' ? '/' : *p;
	  *headptr = '\0';

	  /* Copy any tail component (with the 0) */
	  if (tail++ < path_end)
	    {
	      /* Add a slash if needed. There is space. */
	      if (*(headptr - 1) != '/')
		*headptr++ = '/';
	      int taillen = path_end - tail + 1;
	      if (headptr + taillen > tmp_buf + (2 * NT_MAX_PATH))
		goto too_long;
	      memcpy (headptr, tail, taillen);
	    }

	  /* Evaluate everything all over again. */
	  src = tmp_buf;
	}

      if (!(opt & PC_SYM_CONTENTS))
	add_ext = true;

    out:
      set_path (THIS_path);
      if (add_ext)
	add_ext_from_sym (sym);
      if (dev == FH_NETDRIVE && component)
	{
	  /* This case indicates a non-existant resp. a non-retrievable
	     share.  This happens for instance if the share is a printer.
	     In this case the path must not be treated like a FH_NETDRIVE,
	     but like a FH_FS instead, so the usual open call for files
	     is used on it. */
	  dev.parse (FH_FS);
	}
      else if (isproc_dev (dev) && fileattr == INVALID_FILE_ATTRIBUTES)
	{
	  /* FIXME: Usually we don't set error to ENOENT if a file doesn't
	     exist.  This is typically indicated by the fileattr content.
	     So, why here?  The downside is that cygwin_conv_path just gets
	     an error for these paths so it reports the error back to the
	     application.  Unlike in all other cases of non-existant files,
	     for which check doesn't set error, so cygwin_conv_path just
	     returns the path, as intended. */
	  error = ENOENT;
	  return;
	}
      else if (!need_directory || error)
	/* nothing to do */;
      else if (fileattr == INVALID_FILE_ATTRIBUTES)
	/* Reattach trailing dirsep in native path. */
	strcat (modifiable_path (), "\\");
      else if (fileattr & FILE_ATTRIBUTE_DIRECTORY)
	path_flags &= ~PATH_SYMLINK;
      else
	{
	  debug_printf ("%s is a non-directory", path);
	  error = ENOTDIR;
	  return;
	}

      /* Restore last path component */
      if (tail < path_end && tail > path_copy + 1)
	*tail = '/';

      if (dev.isfs ())
	{
	  /* If FS hasn't been checked already in symlink_info::check,
	     do so now. */
	  if (fs.inited ()|| fs.update (get_nt_native_path (), NULL))
	    {
	      /* Incoming DOS paths are treated like DOS paths in native
		 Windows applications.  No ACLs, just default settings. */
	      if (is_msdos)
		fs.has_acls (false);
	      debug_printf ("this->path(%s), has_acls(%d)",
			    path, fs.has_acls ());
	      /* CV: We could use this->has_acls() but I want to make sure that
		 we don't forget that the MOUNT_NOACL flag must be taken into
		 account here. */
	      if (!(mount_flags & MOUNT_NOACL) && fs.has_acls ())
		set_exec (0);  /* We really don't know if this is executable or
				  not here but set it to not executable since
				  it will be figured out later by anything
				  which cares about this. */
	    }
	  /* If the FS has been found to have unreliable inodes, note
	     that in mount_flags. */
	  if (!fs.hasgood_inode ())
	    mount_flags |= MOUNT_IHASH;
	  /* If the OS is caseinsensitive or the FS is caseinsensitive,
	     don't handle path casesensitive. */
	  if (cygwin_shared->obcaseinsensitive || fs.caseinsensitive ())
	    mount_flags |= MOUNT_NOPOSIX;
	  caseinsensitive = (mount_flags & MOUNT_NOPOSIX)
			    ? OBJ_CASE_INSENSITIVE : 0;
	  if (exec_state () != dont_know_if_executable)
	    /* ok */;
	  else if (isdir ())
	    set_exec (1);
	  else if (issymlink () || issocket ())
	    set_exec (0);

	  /* FIXME: bad hack alert!!!  We need a better solution */
	  if (!strncmp (path_copy, MQ_PATH, MQ_LEN) && path_copy[MQ_LEN])
	    dev.parse (FH_MQUEUE);
	}

      if (opt & PC_NOFULL)
	{
	  if (is_relpath)
	    {
	      mkrelpath (this->modifiable_path (), !!caseinsensitive);
	      /* Invalidate wide_path so that wide relpath can be created
		 in later calls to get_nt_native_path or get_wide_win32_path. */
	      if (wide_path)
		cfree (wide_path);
	      wide_path = NULL;
	    }
	  if (need_directory)
	    {
	      size_t n = strlen (this->path);
	      /* Do not add trailing \ to UNC device names like \\.\a: */
	      if (this->path[n - 1] != '\\' &&
		  (strncmp (this->path, "\\\\.\\", 4) != 0))
		{
		  this->modifiable_path ()[n] = '\\';
		  this->modifiable_path ()[n + 1] = '\0';
		}
	    }
	}

      if (opt & PC_OPEN)
	path_flags |= PATH_OPEN;

      if (opt & PC_CTTY)
	path_flags |= PATH_CTTY;

      if (opt & PC_POSIX)
	set_posix (path_copy);

#if 0
      if (!error)
	{
	  last_path_conv = *this;
	  strcpy (last_src, src);
	}
#endif
    }
  __except (NO_ERROR)
    {
      error = EFAULT;
    }
  __endtry
}

struct pc_flat
{
  path_conv pc;
  HANDLE hdl;
  size_t name_len;
  size_t posix_len;
  char data[0];
};

void *
path_conv::serialize (HANDLE h, unsigned int &n) const
{
  pc_flat *pcf;
  size_t nlen = 0, plen = 0;
  char *p;

  if (path)
    nlen = strlen (path) + 1;
  if (posix_path)
    plen = strlen (posix_path) + 1;
  n = sizeof (pc_flat) + nlen + plen;
  pcf = (pc_flat *) cmalloc (HEAP_COMMUNE, n);
  if (!pcf)
    {
      n = 0;
      return NULL;
    }
  memcpy ((void *) &pcf->pc, this, sizeof *this);
  pcf->hdl = h;
  pcf->name_len = nlen;
  pcf->posix_len = plen;
  p = pcf->data;
  if (nlen)
    p = stpcpy (p, path) + 1;
  if (plen)
    stpcpy (p, posix_path);
  return pcf;
}

HANDLE
path_conv::deserialize (void *bufp)
{
  pc_flat *pcf = (pc_flat *) bufp;
  char *p;
  HANDLE ret;

  memcpy ((void *) this, &pcf->pc, sizeof *this);
  wide_path = uni_path.Buffer = NULL;
  uni_path.MaximumLength = uni_path.Length = 0;
  path = posix_path = NULL;
  p = pcf->data;
  if (pcf->name_len)
    {
      set_path (p);
      p += pcf->name_len;
    }
  if (pcf->posix_len)
    set_posix (p);
  dev.parse (pcf->pc.dev);
  ret = pcf->hdl;
  cfree (bufp);
  return ret;
}

path_conv::~path_conv ()
{
  if (posix_path)
    {
      cfree ((void *) posix_path);
      posix_path = NULL;
    }
  if (path)
    {
      cfree (modifiable_path ());
      path = NULL;
    }
  if (wide_path)
    {
      cfree (wide_path);
      wide_path = NULL;
    }
  close_conv_handle ();
}

bool
path_conv::is_binary ()
{
  tmp_pathbuf tp;
  PWCHAR bintest = tp.w_get ();
  DWORD bin;

  return GetBinaryTypeW (get_wide_win32_path (bintest), &bin)
	 && (bin == SCS_32BIT_BINARY || bin == SCS_64BIT_BINARY);
}

/* Helper function to fill the fai datastructure for a file. */
NTSTATUS
file_get_fai (HANDLE h, PFILE_ALL_INFORMATION pfai)
{
  NTSTATUS status;
  IO_STATUS_BLOCK io;

  /* Some FSes (Netapps) don't implement FileNetworkOpenInformation. */
  status = NtQueryInformationFile (h, &io, pfai, sizeof *pfai,
				   FileAllInformation);
  if (likely (status == STATUS_BUFFER_OVERFLOW))
    status = STATUS_SUCCESS;
  /* Filesystems with broken FileAllInformation exist, too.  See the thread
     starting with https://cygwin.com/ml/cygwin/2016-07/msg00350.html. */
  else if (!NT_SUCCESS (status) && status != STATUS_ACCESS_DENIED)
    {
      memset (pfai, 0, sizeof *pfai);
      status = NtQueryInformationFile (h, &io, &pfai->BasicInformation,
				       sizeof pfai->BasicInformation,
				       FileBasicInformation);
      if (NT_SUCCESS (status))
	{
	  /* The return value of FileInternalInformation is largely ignored.
	     We only make absolutely sure the inode number is set to 0 in
	     case it fails. */
	  status = NtQueryInformationFile (h, &io, &pfai->InternalInformation,
					   sizeof pfai->InternalInformation,
					   FileInternalInformation);
	  if (!NT_SUCCESS (status))
	    pfai->InternalInformation.IndexNumber.QuadPart = 0LL;
	  status = NtQueryInformationFile (h, &io, &pfai->StandardInformation,
					   sizeof pfai->StandardInformation,
					   FileStandardInformation);
	}
    }
  return status;
}

/* Normalize a Win32 path.
   /'s are converted to \'s in the process.
   All duplicate \'s, except for 2 leading \'s, are deleted.

   The result is 0 for success, or an errno error value.
   FIXME: A lot of this should be mergeable with the POSIX critter.  */
int
normalize_win32_path (const char *src, char *dst, char *&tail)
{
  const char *src_start = src;
  const char *dst_start = dst;
  bool beg_src_slash = isdirsep (src[0]);

  tail = dst;
  /* Skip Win32 long path name prefix and NT object directory prefix. */
  if (beg_src_slash && (src[1] == '?' || isdirsep (src[1]))
      && src[2] == '?' && isdirsep (src[3]))
    {
      src += 4;
      if (isdrive (src) && (isdirsep (src[2]) || !src[2]))
	beg_src_slash = false;
      else if (!strncmp (src, "UNC", 3) && isdirsep (src[3]))
	/* native UNC path */
	src += 2; /* Fortunately the first char is not copied... */
      else
	return EINVAL;
    }
  if (beg_src_slash && isdirsep (src[1]))
    {
      if (isdirsep (src[2]))
	{
	  /* More than two slashes are just folded into one. */
	  src += 2;
	  while (isdirsep (src[1]))
	    ++src;
	}
      else
	{
	  /* Two slashes start a network or device path. */
	  *tail++ = '\\';
	  src++;
	  if (src[1] == '.' && isdirsep (src[2]))
	    {
	      *tail++ = '\\';
	      *tail++ = '.';
	      src += 2;
	    }
	}
      dst = tail;
      /* If backslash is missing in src, add one. */
      if (!isdirsep (src[0]))
	*tail++ = '\\';
    }
  if (tail == dst_start)
    {
      if (isdrive (src))
	{
	  /* Always convert drive letter to uppercase for case sensitivity. */
	  *tail++ = cyg_toupper (*src++);
	  *tail++ = *src++;
	  dst = tail;
	  /* If backslash is missing in src, add one. */
	  if (!isdirsep (src[0]))
	    *tail++ = '\\';
	}
      else if (*src != '/')
	{
	  /* Make sure dst points to the rightmost backslash which must not
	     be backtracked over during ".." evaluation.  This is either
	     the backslash after the network path prefix (i.e. "\\") or
	     the backslash after a drive letter (i.e. C:\"). */
	  if (beg_src_slash)
	    {
	      tail += cygheap->cwd.get_drive (dst);
	      /* network path, drive == '\\\\'?  Decrement tail to avoid
	         triple backslash in output. */
	      if (dst[0] == '\\')
		--tail;
	      dst = tail;
	    }
	  else if (cygheap->cwd.get (dst, 0))
	    {
	      tail = strchr (tail, '\0');
	      if (tail[-1] != '\\')
		*tail++ = '\\';
	      ++dst;
	      if (dst[1] == '\\')
		++dst;
	    }
	  else
	    return get_errno ();
	}
    }

  /* At this point dst points to the first backslash, even if it only gets
     written in the first iteration of the following loop.  Backing up to
     handle ".." components can not underrun that border (thus avoiding
     subsequent buffer underruns with fatal results). */
  while (*src)
    {
      /* Strip duplicate /'s.  */
      if (isdirsep (src[0]) && isdirsep (src[1]))
	src++;
      /* Ignore "./".  */
      else if (src[0] == '.' && isdirsep (src[1])
	       && (src == src_start || isdirsep (src[-1])))
	{
	  src += 2;
	  /* Skip /'s to the next path component. */
	  while (isdirsep (*src))
	    src++;
	}

      /* Backup if "..".  */
      else if (src[0] == '.' && src[1] == '.' && tail[-1] == '\\')
	{
	  if (!isdirsep (src[2]) && src[2] != '\0')
	      *tail++ = *src++;
	  else
	    {
	      /* Back up over /, but not if it's the first one.  */
	      if (tail > dst + 1)
		tail--;
	      /* Now back up to the next /.  */
	      while (tail > dst + 1 && tail[-1] != '\\' && tail[-2] != ':')
		tail--;
	      src += 2;
	      /* Skip /'s to the next path component. */
	      while (isdirsep (*src))
		src++;
	    }
	}
      /* Otherwise, add char to result.  */
      else
	{
	  if (*src == '/')
	    *tail++ = '\\';
	  else
	    *tail++ = *src;
	  src++;
	}
      if ((tail - dst) >= NT_MAX_PATH)
	return ENAMETOOLONG;
    }
  if (tail > dst + 1 && tail[-1] == '.' && tail[-2] == '\\')
    tail--;
  *tail = '\0';
  debug_printf ("%s = normalize_win32_path (%s)", dst_start, src_start);
  return 0;
}

/* Various utilities.  */

/* nofinalslash: Remove trailing / and \ from SRC (except for the
   first one).  It is ok for src == dst.  */

void
nofinalslash (const char *src, char *dst)
{
  int len = strlen (src);
  if (src != dst)
    memcpy (dst, src, len + 1);
  while (len > 1 && isdirsep (dst[--len]))
    dst[len] = '\0';
}

/* conv_path_list: Convert a list of path names to/from Win32/POSIX. */

static int
conv_path_list (const char *src, char *dst, size_t size,
		cygwin_conv_path_t what)
{
  tmp_pathbuf tp;
  char src_delim, dst_delim;
  size_t len;
  bool env_cvt = false;

  if (what == (cygwin_conv_path_t) ENV_CVT)
    {
      what = CCP_WIN_A_TO_POSIX | CCP_RELATIVE;
      env_cvt = true;
    }
  if ((what & CCP_CONVTYPE_MASK) == CCP_WIN_A_TO_POSIX)
    {
      src_delim = ';';
      dst_delim = ':';
    }
  else
    {
      src_delim = ':';
      dst_delim = ';';
    }

  char *srcbuf;
  len = strlen (src) + 1;
  if (len <= NT_MAX_PATH * sizeof (WCHAR))
    srcbuf = (char *) tp.w_get ();
  else
    srcbuf = (char *) alloca (len);

  int err = 0;
  char *d = dst - 1;
  bool saw_empty = false;
  do
    {
      char *srcpath = srcbuf;
      char *s = strccpy (srcpath, &src, src_delim);
      size_t len = s - srcpath;
      if (len >= NT_MAX_PATH)
	{
	  err = ENAMETOOLONG;
	  break;
	}
      /* Paths in Win32 path lists in the environment (%Path%), are often
	 enclosed in quotes (usually paths with spaces).  Trailing backslashes
	 are common, too.  Remove them. */
      if (env_cvt && len)
	{
	  if (*srcpath == '"')
	    {
	      ++srcpath;
	      *--s = '\0';
	      len -= 2;
	    }
	  while (len && s[-1] == '\\')
	    {
	      *--s = '\0';
	      --len;
	    }
	}
      if (len)
	{
	  ++d;
	  err = cygwin_conv_path (what, srcpath, d, size - (d - dst));
	}
      else if ((what & CCP_CONVTYPE_MASK) == CCP_POSIX_TO_WIN_A)
	{
	  ++d;
	  err = cygwin_conv_path (what, ".", d, size - (d - dst));
	}
      else
	{
	  if (env_cvt)
	    saw_empty = true;
	  continue;
	}
      if (err)
	break;
      d = strchr (d, '\0');
      *d = dst_delim;
    }
  while (*src++);

  if (saw_empty)
    err = EIDRM;

  if (d < dst)
    d++;
  *d = '\0';
  return err;
}

/********************** Symbolic Link Support **************************/

/* Create a symlink from FROMPATH to TOPATH. */

extern "C" int
symlink (const char *oldpath, const char *newpath)
{
  path_conv win32_newpath;

  __try
    {
      if (!*oldpath || !*newpath)
	{
	  set_errno (ENOENT);
	  __leave;
	}

      /* Trailing dirsep is a no-no, only errno differs. */
      bool has_trailing_dirsep = isdirsep (newpath[strlen (newpath) - 1]);
      win32_newpath.check (newpath,
			   PC_SYM_NOFOLLOW | PC_SYM_NOFOLLOW_DIR | PC_POSIX,
			   stat_suffixes);

      if (win32_newpath.error || has_trailing_dirsep)
	{
	  set_errno (win32_newpath.error ?:
		     win32_newpath.exists () ? EEXIST : ENOENT);
	  __leave;
	}

      return symlink_worker (oldpath, win32_newpath, false);
    }
  __except (EFAULT) {}
  __endtry
  return -1;
}

static int
symlink_nfs (const char *oldpath, path_conv &win32_newpath)
{
  /* On NFS, create symlinks by calling NtCreateFile with an EA of type
     NfsSymlinkTargetName containing ... the symlink target name. */
  tmp_pathbuf tp;
  PFILE_FULL_EA_INFORMATION pffei;
  NTSTATUS status;
  HANDLE fh;
  OBJECT_ATTRIBUTES attr;
  IO_STATUS_BLOCK io;

  pffei = (PFILE_FULL_EA_INFORMATION) tp.w_get ();
  pffei->NextEntryOffset = 0;
  pffei->Flags = 0;
  pffei->EaNameLength = sizeof (NFS_SYML_TARGET) - 1;
  char *EaValue = stpcpy (pffei->EaName, NFS_SYML_TARGET) + 1;
  pffei->EaValueLength = sizeof (WCHAR) *
    (sys_mbstowcs ((PWCHAR) EaValue, NT_MAX_PATH, oldpath) - 1);
  status = NtCreateFile (&fh, FILE_WRITE_DATA | FILE_WRITE_EA | SYNCHRONIZE,
			 win32_newpath.get_object_attr (attr, sec_none_nih),
			 &io, NULL, FILE_ATTRIBUTE_SYSTEM,
			 FILE_SHARE_VALID_FLAGS, FILE_CREATE,
			 FILE_SYNCHRONOUS_IO_NONALERT
			 | FILE_OPEN_FOR_BACKUP_INTENT,
			 pffei, NT_MAX_PATH * sizeof (WCHAR));
  if (!NT_SUCCESS (status))
    {
      __seterrno_from_nt_status (status);
      return -1;
    }
  NtClose (fh);
  return 0;
}

/* Count backslashes between s and e. */
static inline int
cnt_bs (PWCHAR s, PWCHAR e)
{
  int num = 0;

  while (s < e)
    if (*s++ == L'\\')
      ++num;
  return num;
}

#ifndef SYMBOLIC_LINK_FLAG_ALLOW_UNPRIVILEGED_CREATE
#define SYMBOLIC_LINK_FLAG_ALLOW_UNPRIVILEGED_CREATE 2
#endif

static int
symlink_native (const char *oldpath, path_conv &win32_newpath)
{
  tmp_pathbuf tp;
  path_conv win32_oldpath;
  PUNICODE_STRING final_oldpath, final_newpath;
  UNICODE_STRING final_oldpath_buf;
  DWORD flags;

  if (isabspath (oldpath))
    {
      win32_oldpath.check (oldpath, PC_SYM_NOFOLLOW, stat_suffixes);
      final_oldpath = win32_oldpath.get_nt_native_path ();
    }
  else
    {
      /* The symlink target is relative to the directory in which
	 the symlink gets created, not relative to the cwd.  Therefore
	 we have to mangle the path quite a bit before calling path_conv. */
      ssize_t len = strrchr (win32_newpath.get_posix (), '/')
		    - win32_newpath.get_posix () + 1;
      char *absoldpath = tp.t_get ();
      stpcpy (stpncpy (absoldpath, win32_newpath.get_posix (), len),
	      oldpath);
      win32_oldpath.check (absoldpath, PC_SYM_NOFOLLOW, stat_suffixes);

      /* Try hard to keep Windows symlink path relative. */

      /* 1. Find common path prefix.  Skip leading \\?\, but take pre-increment
            of the following loop into account. */
      PWCHAR c_old = win32_oldpath.get_nt_native_path ()->Buffer + 3;
      PWCHAR c_new = win32_newpath.get_nt_native_path ()->Buffer + 3;
      /* Windows compatible == always check case insensitive.  */
      while (towupper (*++c_old) == towupper (*++c_new))
	;
      /* The last component could share a common prefix, so make sure we end
         up on the first char after the last common backslash. */
      while (c_old[-1] != L'\\')
	--c_old, --c_new;

      /* 2. Check if prefix is long enough.  The prefix must at least points to
            a complete device:  \\?\X:\ or \\?\UNC\server\share\ are the minimum
	    prefix strings.  We start counting behind the \\?\ for speed. */
      int num = cnt_bs (win32_oldpath.get_nt_native_path ()->Buffer + 4, c_old);
      if (num < 1		/* locale drive. */
	  || (win32_oldpath.get_nt_native_path ()->Buffer[5] != L':'
	      && num < 3))	/* UNC path. */
	{
	  /* 3a. No valid common path prefix: Create absolute symlink. */
	  final_oldpath = win32_oldpath.get_nt_native_path ();
	}
      else
	{
	  /* 3b. Common path prefx.  Count number of additional directories
		 in symlink's path, and prepend as much ".." path components
		 to the target path. */
	  PWCHAR e_new = win32_newpath.get_nt_native_path ()->Buffer
			 + win32_newpath.get_nt_native_path ()->Length
			   / sizeof (WCHAR);
	  num = cnt_bs (c_new, e_new);
	  final_oldpath = &final_oldpath_buf;
	  final_oldpath->Buffer = tp.w_get ();
	  PWCHAR e_old = final_oldpath->Buffer;
	  while (num-- > 0)
	    e_old = wcpcpy (e_old, L"..\\");
	  wcpcpy (e_old, c_old);
	}
    }
  /* If the symlink target doesn't exist, don't create native symlink.
     Otherwise the directory flag in the symlink is potentially wrong
     when the target comes into existence, and native tools will fail.
     This is so screwball. This is no problem on AFS, fortunately. */
  if (!win32_oldpath.exists () && !win32_oldpath.fs_is_afs ())
    {
      SetLastError (ERROR_FILE_NOT_FOUND);
      return -1;
    }
  /* Don't allow native symlinks to Cygwin special files.  However, the
     caller shoud know because this case shouldn't be covered by the
     default "nativestrict" behaviour, so we use a special return code. */
  if (win32_oldpath.isspecial ())
    return -2;
  /* Convert native paths to Win32 UNC paths. */
  final_newpath = win32_newpath.get_nt_native_path ();
  final_newpath->Buffer[1] = L'\\';
  /* oldpath may be relative.  Make sure to convert only absolute paths
     to Win32 paths. */
  if (final_oldpath->Buffer[0] == L'\\')
    {
      /* Starting with Windows 8.1, the ShellExecuteW function does not
	 handle the long path prefix correctly for symlink targets.  Thus,
	 we create simple short paths < MAX_PATH without long path prefix. */
      if (RtlEqualUnicodePathPrefix (final_oldpath, &ro_u_uncp, TRUE)
	  && final_oldpath->Length < (MAX_PATH + 6) * sizeof (WCHAR))
	{
	  final_oldpath->Buffer += 6;
	  final_oldpath->Buffer[0] = L'\\';
	}
      else if (final_oldpath->Length < (MAX_PATH + 4) * sizeof (WCHAR))
	final_oldpath->Buffer += 4;
      else /* Stick to long path, fix native prefix for Win32 API calls. */
	final_oldpath->Buffer[1] = L'\\';
    }
  /* Try to create native symlink. */
  flags = win32_oldpath.isdir () ? SYMBOLIC_LINK_FLAG_DIRECTORY : 0;
  if (wincap.has_unprivileged_createsymlink ())
    flags |= SYMBOLIC_LINK_FLAG_ALLOW_UNPRIVILEGED_CREATE;
  if (!CreateSymbolicLinkW (final_newpath->Buffer, final_oldpath->Buffer,
			    flags))
    {
      /* Repair native newpath, we still need it. */
      final_newpath->Buffer[1] = L'?';
      return -1;
    }
  return 0;
}

#ifndef IO_REPARSE_TAG_LX_SYMLINK
#define IO_REPARSE_TAG_LX_SYMLINK	(0xa000001d)
#endif

typedef struct _REPARSE_LX_SYMLINK_BUFFER
{
  DWORD	ReparseTag;
  WORD	ReparseDataLength;
  WORD	Reserved;
  struct {
    DWORD FileType;	/* Take member name with a grain of salt.  Value is
			   apparently always 2 for symlinks. */
    char  PathBuffer[1];/* POSIX path as given to symlink(2).
			   Path is not \0 terminated.
			   Length is ReparseDataLength - sizeof (FileType).
			   Always UTF-8.
			   Chars given in incompatible codesets, e. g. umlauts
			   in ISO-8859-x, are converted to the Unicode
			   REPLACEMENT CHARACTER 0xfffd == \xef\xbf\bd */
  } LxSymlinkReparseBuffer;
} REPARSE_LX_SYMLINK_BUFFER,*PREPARSE_LX_SYMLINK_BUFFER;

static int
symlink_wsl (const char *oldpath, path_conv &win32_newpath)
{
  tmp_pathbuf tp;
  PREPARSE_LX_SYMLINK_BUFFER rpl = (PREPARSE_LX_SYMLINK_BUFFER) tp.c_get ();
  char *path_buf = rpl->LxSymlinkReparseBuffer.PathBuffer;
  const int max_pathlen = MAXIMUM_REPARSE_DATA_BUFFER_SIZE
			  - offsetof (REPARSE_LX_SYMLINK_BUFFER,
				      LxSymlinkReparseBuffer.PathBuffer);
  PWCHAR utf16 = tp.w_get ();
  NTSTATUS status;
  IO_STATUS_BLOCK io;
  OBJECT_ATTRIBUTES attr;
  HANDLE fh;
  int len;

  rpl->ReparseTag = IO_REPARSE_TAG_LX_SYMLINK;
  rpl->Reserved = 0;
  rpl->LxSymlinkReparseBuffer.FileType = 2;
  /* Convert cygdrive prefix to "/mnt" for WSL compatibility, but only if
     cygdrive prefix is not "/", otherwise suffer random "/mnt" symlinks... */
  if (mount_table->cygdrive_len > 1
      && path_prefix_p (mount_table->cygdrive, oldpath,
			mount_table->cygdrive_len, false)
      && (strlen (oldpath + mount_table->cygdrive_len - 1) < 2
	  || (islower (oldpath[mount_table->cygdrive_len])
	      && (oldpath[mount_table->cygdrive_len + 1] == '/'
		  || oldpath[mount_table->cygdrive_len + 1] == '\0'))))
    stpcpy (stpcpy (path_buf, "/mnt"),
	    oldpath + mount_table->cygdrive_len - 1);
  else
    *stpncpy (path_buf, oldpath, max_pathlen) = '\0';
  /* Convert target path to UTF-16 and then back to UTF-8 to make sure the
     WSL symlink is in UTF-8, independent of the current Cygwin codeset. */
  sys_mbstowcs (utf16, NT_MAX_PATH, path_buf);
  len = WideCharToMultiByte (CP_UTF8, 0, utf16, -1, path_buf, max_pathlen,
			     NULL, NULL);
  /* Length is omitting trailing \0. */
  rpl->ReparseDataLength = sizeof (DWORD) + len - 1;
  /* Create reparse point. */
  status = NtCreateFile (&fh, DELETE | FILE_GENERIC_WRITE
			     | READ_CONTROL | WRITE_DAC,
			 win32_newpath.get_object_attr (attr, sec_none_nih),
			 &io, NULL, FILE_ATTRIBUTE_NORMAL,
			 FILE_SHARE_VALID_FLAGS, FILE_CREATE,
			 FILE_SYNCHRONOUS_IO_NONALERT
			 | FILE_NON_DIRECTORY_FILE
			 | FILE_OPEN_FOR_BACKUP_INTENT
			 | FILE_OPEN_REPARSE_POINT,
			 NULL, 0);
  if (!NT_SUCCESS (status))
    {
      SetLastError (RtlNtStatusToDosError (status));
      return -1;
    }
  set_created_file_access (fh, win32_newpath, S_IFLNK | STD_RBITS | STD_WBITS);
  status = NtFsControlFile (fh, NULL, NULL, NULL, &io, FSCTL_SET_REPARSE_POINT,
			    (LPVOID) rpl, REPARSE_DATA_BUFFER_HEADER_SIZE
					 + rpl->ReparseDataLength,
			    NULL, 0);
  if (!NT_SUCCESS (status))
    {
      SetLastError (RtlNtStatusToDosError (status));
      FILE_DISPOSITION_INFORMATION fdi = { TRUE };
      status = NtSetInformationFile (fh, &io, &fdi, sizeof fdi,
				     FileDispositionInformation);
      NtClose (fh);
      if (!NT_SUCCESS (status))
	debug_printf ("Setting delete dispostion failed, status = %y", status);
      return -1;
    }
  NtClose (fh);
  return 0;
}

int
symlink_worker (const char *oldpath, path_conv &win32_newpath, bool isdevice)
{
  int res = -1;
  size_t len;
  char *buf, *cp;
  tmp_pathbuf tp;
  winsym_t wsym_type;

  /* POSIX says that empty 'newpath' is invalid input while empty
     'oldpath' is valid -- it's symlink resolver job to verify if
     symlink contents point to existing filesystem object */
  __try
    {
      if (strlen (oldpath) > SYMLINK_MAX)
	{
	  set_errno (ENAMETOOLONG);
	  __leave;
	}

      /* Default symlink type is determined by global allow_winsymlinks
	 variable.  Device files are always shortcuts. */
      wsym_type = isdevice ? WSYM_lnk : allow_winsymlinks;
      /* NFS has its own, dedicated way to create symlinks. */
      if (win32_newpath.fs_is_nfs ())
	wsym_type = WSYM_nfs;
      /* MVFS doesn't handle the SYSTEM DOS attribute, but it handles the R/O
	 attribute. Therefore we create symlinks on MVFS always as shortcuts. */
      else if (win32_newpath.fs_is_mvfs ())
	wsym_type = WSYM_lnk;
      /* AFS only supports native symlinks. */
      else if (win32_newpath.fs_is_afs ())
	wsym_type = WSYM_nativestrict;
      /* Don't try native symlinks on FSes not supporting reparse points. */
      else if ((wsym_type == WSYM_native || wsym_type == WSYM_nativestrict)
	       && !(win32_newpath.fs_flags () & FILE_SUPPORTS_REPARSE_POINTS))
	wsym_type = WSYM_default;

      /* Attach .lnk suffix when shortcut is requested. */
      if (wsym_type == WSYM_lnk && !win32_newpath.exists ()
	  && (isdevice || !win32_newpath.fs_is_nfs ()))
	{
	  char *newplnk = tp.c_get ();
	  stpcpy (stpcpy (newplnk, win32_newpath.get_posix ()), ".lnk");
	  win32_newpath.check (newplnk, PC_SYM_NOFOLLOW | PC_POSIX);
	}

      if (win32_newpath.error)
	{
	  set_errno (win32_newpath.error);
	  __leave;
	}

      syscall_printf ("symlink (%s, %S) wsym_type %d", oldpath,
		      win32_newpath.get_nt_native_path (), wsym_type);

      if ((!isdevice && win32_newpath.exists ())
	  || (win32_newpath.isdevice () && !win32_newpath.is_fs_special ()))
	{
	  set_errno (EEXIST);
	  __leave;
	}

      /* Handle NFS, native symlinks and WSL symlinks in their own functions. */
      switch (wsym_type)
	{
	case WSYM_nfs:
	  res = symlink_nfs (oldpath, win32_newpath);
	  __leave;
	case WSYM_native:
	case WSYM_nativestrict:
	  res = symlink_native (oldpath, win32_newpath);
	  if (!res)
	    __leave;
	  /* Strictly native?  Too bad, unless the target is a Cygwin
	     special file. */
	  if (res == -1 && wsym_type == WSYM_nativestrict)
	    {
	      __seterrno ();
	      __leave;
	    }
	  /* Otherwise, fall back to default symlink type. */
	  wsym_type = WSYM_default;
	  fallthrough;
	case WSYM_default:
	  if (win32_newpath.fs_flags () & FILE_SUPPORTS_REPARSE_POINTS)
	    {
	      res = symlink_wsl (oldpath, win32_newpath);
	      if (!res)
		__leave;
	    }
	  /* On FSes not supporting reparse points, or in case of an error
	     creating the WSL symlink, fall back to creating the plain old
	     SYSTEM file symlink. */
	  wsym_type = WSYM_sysfile;
	  break;
	default:
	  break;
	}

      if (wsym_type == WSYM_lnk)
	{
	  path_conv win32_oldpath;
	  ITEMIDLIST *pidl = NULL;
	  size_t full_len = 0;
	  unsigned short oldpath_len, desc_len, relpath_len, pidl_len = 0;
	  char desc[MAX_PATH + 1], *relpath;

	  if (!isdevice)
	    {
	      /* First create an IDLIST to learn how big our shortcut is
		 going to be. */
	      IShellFolder *psl;

	      /* The symlink target is relative to the directory in which the
		 symlink gets created, not relative to the cwd.  Therefore we
		 have to mangle the path quite a bit before calling path_conv.*/
	      if (isabspath (oldpath))
		win32_oldpath.check (oldpath,
				     PC_SYM_NOFOLLOW,
				     stat_suffixes);
	      else
		{
		  len = strrchr (win32_newpath.get_posix (), '/')
			- win32_newpath.get_posix () + 1;
		  char *absoldpath = tp.t_get ();
		  stpcpy (stpncpy (absoldpath, win32_newpath.get_posix (),
				   len),
			  oldpath);
		  win32_oldpath.check (absoldpath, PC_SYM_NOFOLLOW,
				       stat_suffixes);
		}
	      if (SUCCEEDED (SHGetDesktopFolder (&psl)))
		{
		  WCHAR wc_path[win32_oldpath.get_wide_win32_path_len () + 1];
		  win32_oldpath.get_wide_win32_path (wc_path);
		  /* Amazing but true:  Even though the ParseDisplayName method
		     takes a wide char path name, it does not understand the
		     Win32 prefix for long pathnames!  So we have to tack off
		     the prefix and convert the path to the "normal" syntax
		     for ParseDisplayName.  */
		  PWCHAR wc = wc_path + 4;
		  if (wc[1] != L':') /* native UNC path */
		    *(wc += 2) = L'\\';
		  HRESULT res;
		  if (SUCCEEDED (res = psl->ParseDisplayName (NULL, NULL, wc,
							      NULL, &pidl,
							      NULL)))
		    {
		      ITEMIDLIST *p;

		      for (p = pidl; p->mkid.cb > 0;
			   p = (ITEMIDLIST *)((char *) p + p->mkid.cb))
			;
		      pidl_len = (char *) p - (char *) pidl + 2;
		    }
		  psl->Release ();
		}
	    }
	  /* Compute size of shortcut file. */
	  full_len = sizeof (win_shortcut_hdr);
	  if (pidl_len)
	    full_len += sizeof (unsigned short) + pidl_len;
	  oldpath_len = strlen (oldpath);
	  /* Unfortunately the length of the description is restricted to a
	     length of 2000 bytes.  We don't want to add considerations for
	     the different lengths and even 2000 bytes is not enough for long
	     path names.  So what we do here is to set the description to the
	     POSIX path only if the path is not longer than MAX_PATH characters.
	     We append the full path name after the regular shortcut data
	     (see below), which works fine with Windows Explorer as well
	     as older Cygwin versions (as long as the whole file isn't bigger
	     than 8K).  The description field is only used for backward
	     compatibility to older Cygwin versions and those versions are
	     not capable of handling long path names anyway. */
	  desc_len = stpcpy (desc, oldpath_len > MAX_PATH
				   ? "[path too long]" : oldpath) - desc;
	  full_len += sizeof (unsigned short) + desc_len;
	  /* Devices get the oldpath string unchanged as relative path. */
	  if (isdevice)
	    {
	      relpath_len = oldpath_len;
	      stpcpy (relpath = tp.c_get (), oldpath);
	    }
	  else
	    {
	      relpath_len = strlen (win32_oldpath.get_win32 ());
	      stpcpy (relpath = tp.c_get (), win32_oldpath.get_win32 ());
	    }
	  full_len += sizeof (unsigned short) + relpath_len;
	  full_len += sizeof (unsigned short) + oldpath_len;
	  /* 1 byte more for trailing 0 written by stpcpy. */
	  if (full_len < NT_MAX_PATH * sizeof (WCHAR))
	    buf = tp.t_get ();
	  else
	    buf = (char *) alloca (full_len + 1);

	  /* Create shortcut header */
	  win_shortcut_hdr *shortcut_header = (win_shortcut_hdr *) buf;
	  memset (shortcut_header, 0, sizeof *shortcut_header);
	  shortcut_header->size = sizeof *shortcut_header;
	  shortcut_header->magic = GUID_shortcut;
	  shortcut_header->flags = (WSH_FLAG_DESC | WSH_FLAG_RELPATH);
	  if (pidl)
	    shortcut_header->flags |= WSH_FLAG_IDLIST;
	  shortcut_header->run = SW_NORMAL;
	  cp = buf + sizeof (win_shortcut_hdr);

	  /* Create IDLIST */
	  if (pidl)
	    {
	      *(unsigned short *)cp = pidl_len;
	      memcpy (cp += 2, pidl, pidl_len);
	      cp += pidl_len;
	      CoTaskMemFree (pidl);
	    }

	  /* Create description */
	  *(unsigned short *)cp = desc_len;
	  cp = stpcpy (cp += 2, desc);

	  /* Create relpath */
	  *(unsigned short *)cp = relpath_len;
	  cp = stpcpy (cp += 2, relpath);

	  /* Append the POSIX path after the regular shortcut data for
	     the long path support. */
	  unsigned short *plen = (unsigned short *) cp;
	  cp += 2;
	  *(PWCHAR) cp = 0xfeff;		/* BOM */
	  cp += 2;
	  *plen = sys_mbstowcs ((PWCHAR) cp, NT_MAX_PATH, oldpath)
		  * sizeof (WCHAR);
	  cp += *plen;
	}
      else /* wsym_type == WSYM_sysfile */
	{
	  /* Default technique creating a symlink. */
	  buf = tp.t_get ();
	  cp = stpcpy (buf, SYMLINK_COOKIE);
	  *(PWCHAR) cp = 0xfeff;		/* BOM */
	  cp += 2;
	  /* Note that the terminating nul is written.  */
	  cp += sys_mbstowcs ((PWCHAR) cp, NT_MAX_PATH, oldpath)
		* sizeof (WCHAR);
	}

      OBJECT_ATTRIBUTES attr;
      IO_STATUS_BLOCK io;
      NTSTATUS status;
      ULONG access;
      HANDLE fh;

      access = DELETE | FILE_GENERIC_WRITE;
      if (isdevice && win32_newpath.exists ())
	{
	  status = NtOpenFile (&fh, FILE_WRITE_ATTRIBUTES,
			       win32_newpath.get_object_attr (attr,
							      sec_none_nih),
			       &io, 0, FILE_OPEN_FOR_BACKUP_INTENT);
	  if (!NT_SUCCESS (status))
	    {
	      __seterrno_from_nt_status (status);
	      __leave;
	    }
	  status = NtSetAttributesFile (fh, FILE_ATTRIBUTE_NORMAL);
	  NtClose (fh);
	  if (!NT_SUCCESS (status))
	    {
	      __seterrno_from_nt_status (status);
	      __leave;
	    }
	}
      else if (!isdevice && win32_newpath.has_acls ()
	       && !win32_newpath.isremote ())
	/* If the filesystem supports ACLs, we will overwrite the DACL after the
	   call to NtCreateFile.  This requires a handle with READ_CONTROL and
	   WRITE_DAC access, otherwise get_file_sd and set_file_sd both have to
	   open the file again.
	   FIXME: On remote NTFS shares open sometimes fails because even the
	   creator of the file doesn't have the right to change the DACL.
	   I don't know what setting that is or how to recognize such a share,
	   so for now we don't request WRITE_DAC on remote drives. */
	access |= READ_CONTROL | WRITE_DAC;

      status = NtCreateFile (&fh, access,
			     win32_newpath.get_object_attr (attr, sec_none_nih),
			     &io, NULL, FILE_ATTRIBUTE_NORMAL,
			     FILE_SHARE_VALID_FLAGS,
			     isdevice ? FILE_OVERWRITE_IF : FILE_CREATE,
			     FILE_SYNCHRONOUS_IO_NONALERT
			     | FILE_NON_DIRECTORY_FILE
			     | FILE_OPEN_FOR_BACKUP_INTENT,
			     NULL, 0);
      if (!NT_SUCCESS (status))
	{
	  __seterrno_from_nt_status (status);
	  __leave;
	}
      if (io.Information == FILE_CREATED && win32_newpath.has_acls ())
	set_created_file_access (fh, win32_newpath,
				 S_IFLNK | STD_RBITS | STD_WBITS);
      status = NtWriteFile (fh, NULL, NULL, NULL, &io, buf, cp - buf,
			    NULL, NULL);
      if (NT_SUCCESS (status) && io.Information == (ULONG) (cp - buf))
	{
	  status = NtSetAttributesFile (fh, wsym_type == WSYM_lnk
					    ? FILE_ATTRIBUTE_READONLY
					    : FILE_ATTRIBUTE_SYSTEM);
	  if (!NT_SUCCESS (status))
	    debug_printf ("Setting attributes failed, status = %y", status);
	  res = 0;
	}
      else
	{
	  __seterrno_from_nt_status (status);
	  FILE_DISPOSITION_INFORMATION fdi = { TRUE };
	  status = NtSetInformationFile (fh, &io, &fdi, sizeof fdi,
					 FileDispositionInformation);
	  if (!NT_SUCCESS (status))
	    debug_printf ("Setting delete dispostion failed, status = %y",
			  status);
	}
      NtClose (fh);

    }
  __except (EFAULT) {}
  __endtry
  syscall_printf ("%d = symlink_worker(%s, %s, %d)",
		  res, oldpath, win32_newpath.get_posix (), isdevice);
  return res;
}

static bool
cmp_shortcut_header (win_shortcut_hdr *file_header)
{
  /* A Cygwin or U/Win shortcut only contains a description and a relpath.
     Cygwin shortcuts also might contain an ITEMIDLIST. The run type is
     always set to SW_NORMAL. */
  return file_header->size == sizeof (win_shortcut_hdr)
      && !memcmp (&file_header->magic, &GUID_shortcut, sizeof GUID_shortcut)
      && (file_header->flags & ~WSH_FLAG_IDLIST)
	 == (WSH_FLAG_DESC | WSH_FLAG_RELPATH)
      && file_header->run == SW_NORMAL;
}

int
symlink_info::check_shortcut (HANDLE h)
{
  tmp_pathbuf tp;
  win_shortcut_hdr *file_header;
  char *buf, *cp;
  unsigned short len;
  int res = 0;
  NTSTATUS status;
  IO_STATUS_BLOCK io;
  FILE_STANDARD_INFORMATION fsi;
  LARGE_INTEGER off = { QuadPart:0LL };

  status = NtQueryInformationFile (h, &io, &fsi, sizeof fsi,
				   FileStandardInformation);
  if (!NT_SUCCESS (status))
    {
      set_error (EIO);
      return 0;
    }
  if (fsi.EndOfFile.QuadPart <= (LONGLONG) sizeof (win_shortcut_hdr)
      || fsi.EndOfFile.QuadPart > 4 * 65536)
    return 0;
  if (fsi.EndOfFile.LowPart < NT_MAX_PATH * sizeof (WCHAR))
    buf = (char *) tp.w_get ();
  else
    buf = (char *) alloca (fsi.EndOfFile.LowPart + 1);
  status = NtReadFile (h, NULL, NULL, NULL, &io, buf, fsi.EndOfFile.LowPart,
		       &off, NULL);
  if (!NT_SUCCESS (status))
    {
      if (status != STATUS_END_OF_FILE)
	set_error (EIO);
      return 0;
    }
  file_header = (win_shortcut_hdr *) buf;
  if (io.Information != fsi.EndOfFile.LowPart
      || !cmp_shortcut_header (file_header))
    return 0;
  cp = buf + sizeof (win_shortcut_hdr);
  if (file_header->flags & WSH_FLAG_IDLIST) /* Skip ITEMIDLIST */
    cp += *(unsigned short *) cp + 2;
  if (!(len = *(unsigned short *) cp))
    return 0;
  cp += 2;
  /* Check if this is a device file - these start with the sequence :\\ */
  if (strncmp (cp, ":\\", 2) == 0)
    res = strlen (strcpy (contents, cp)); /* Don't mess with device files */
  else
    {
      /* Has appended full path?  If so, use it instead of description. */
      unsigned short relpath_len = *(unsigned short *) (cp + len);
      if (cp + len + 2 + relpath_len < buf + fsi.EndOfFile.LowPart)
	{
	  cp += len + 2 + relpath_len;
	  len = *(unsigned short *) cp;
	  cp += 2;
	}
      if (*(PWCHAR) cp == 0xfeff)	/* BOM */
	{
	  char *tmpbuf = tp.c_get ();
	  if (sys_wcstombs (tmpbuf, NT_MAX_PATH, (PWCHAR) (cp + 2))
	      > SYMLINK_MAX)
	    return 0;
	  res = posixify (tmpbuf);
	}
      else if (len > SYMLINK_MAX)
	return 0;
      else
	{
	  cp[len] = '\0';
	  res = posixify (cp);
	}
    }
  if (res) /* It's a symlink.  */
    path_flags |= PATH_SYMLINK | PATH_LNK;
  return res;
}

int
symlink_info::check_sysfile (HANDLE h)
{
  tmp_pathbuf tp;
  char cookie_buf[sizeof (SYMLINK_COOKIE) - 1];
  char *srcbuf = tp.c_get ();
  int res = 0;
  NTSTATUS status;
  IO_STATUS_BLOCK io;
  bool interix_symlink = false;
  LARGE_INTEGER off = { QuadPart:0LL };

  status = NtReadFile (h, NULL, NULL, NULL, &io, cookie_buf,
		       sizeof (cookie_buf), &off, NULL);
  if (!NT_SUCCESS (status))
    {
      debug_printf ("ReadFile1 failed %y", status);
      if (status != STATUS_END_OF_FILE)
	set_error (EIO);
      return 0;
    }
  off.QuadPart = io.Information;
  if (io.Information == sizeof (cookie_buf)
	   && memcmp (cookie_buf, SYMLINK_COOKIE, sizeof (cookie_buf)) == 0)
    {
      /* It's a symlink.  */
      path_flags |= PATH_SYMLINK;
    }
  else if (io.Information == sizeof (cookie_buf)
	   && memcmp (cookie_buf, SOCKET_COOKIE, sizeof (cookie_buf)) == 0)
    path_flags |= PATH_SOCKET;
  else if (io.Information >= sizeof (INTERIX_SYMLINK_COOKIE)
	   && memcmp (cookie_buf, INTERIX_SYMLINK_COOKIE,
		      sizeof (INTERIX_SYMLINK_COOKIE) - 1) == 0)
    {
      /* It's an Interix symlink.  */
      path_flags |= PATH_SYMLINK;
      interix_symlink = true;
      /* Interix symlink cookies are shorter than Cygwin symlink cookies, so
	 in case of an Interix symlink cooky we have read too far into the
	 file.  Set file pointer back to the position right after the cookie. */
      off.QuadPart = sizeof (INTERIX_SYMLINK_COOKIE) - 1;
    }
  if (path_flags & PATH_SYMLINK)
    {
      status = NtReadFile (h, NULL, NULL, NULL, &io, srcbuf,
			   NT_MAX_PATH, &off, NULL);
      if (!NT_SUCCESS (status))
	{
	  debug_printf ("ReadFile2 failed");
	  if (status != STATUS_END_OF_FILE)
	    set_error (EIO);
	}
      else if (*(PWCHAR) srcbuf == 0xfeff	/* BOM */
	       || interix_symlink)
	{
	  /* Add trailing 0 to Interix symlink target.  Skip BOM in Cygwin
	     symlinks. */
	  if (interix_symlink)
	    ((PWCHAR) srcbuf)[io.Information / sizeof (WCHAR)] = L'\0';
	  else
	    srcbuf += 2;
	  char *tmpbuf = tp.c_get ();
	  if (sys_wcstombs (tmpbuf, NT_MAX_PATH, (PWCHAR) srcbuf)
	      > SYMLINK_MAX)
	    debug_printf ("symlink string too long");
	  else
	    res = posixify (tmpbuf);
	}
      else if (io.Information > SYMLINK_MAX + 1)
	debug_printf ("symlink string too long");
      else
	res = posixify (srcbuf);
    }
  return res;
}

typedef struct _REPARSE_APPEXECLINK_BUFFER
{
  DWORD ReparseTag;
  WORD  ReparseDataLength;
  WORD  Reserved;
  struct {
    DWORD Version;       /* Take member name with a grain of salt. */
    WCHAR Strings[1];    /* Four serialized, NUL-terminated WCHAR strings:
			   - Package ID
			   - Entry Point
			   - Executable Path
			   - Application Type
			   We're only interested in the Executable Path */
  } AppExecLinkReparseBuffer;
} REPARSE_APPEXECLINK_BUFFER,*PREPARSE_APPEXECLINK_BUFFER;

static bool
check_reparse_point_string (PUNICODE_STRING subst)
{
  /* Native mount points, or native non-relative symbolic links,
     can be treated as posix symlinks only if the SubstituteName
     can be converted from a native NT object namespace name to
     a win32 name. We only know how to convert names with two
     prefixes :
       "\??\UNC\..."
       "\??\X:..."
     Other reparse points will be treated as files or
     directories, not as posix symlinks.
     */
  if (RtlEqualUnicodePathPrefix (subst, &ro_u_natp, FALSE))
    {
      if (subst->Length >= 6 * sizeof(WCHAR) && subst->Buffer[5] == L':' &&
          (subst->Length == 6 * sizeof(WCHAR) || subst->Buffer[6] == L'\\'))
        return true;
      else if (subst->Length >= 8 * sizeof(WCHAR) &&
          wcsncmp (subst->Buffer + 4, L"UNC\\", 4) == 0)
        return true;
    }
  return false;
}

/* Return values:
    <0: Negative errno.
     0: Not a reparse point recognized by us.
    >0: Path flags for a recognized reparse point, always including PATH_REP.
*/
int
check_reparse_point_target (HANDLE h, bool remote, PREPARSE_DATA_BUFFER rp,
			    PUNICODE_STRING psymbuf)
{
  NTSTATUS status;
  IO_STATUS_BLOCK io;

  /* On remote drives or under heavy load, NtFsControlFile can return with
     STATUS_PENDING.  If so, instead of creating an event object, just set
     io.Status to an invalid value and perform a minimal wait until io.Status
     changed. */
  memset (&io, 0xff, sizeof io);
  status = NtFsControlFile (h, NULL, NULL, NULL, &io,
			    FSCTL_GET_REPARSE_POINT, NULL, 0, (LPVOID) rp,
			    MAXIMUM_REPARSE_DATA_BUFFER_SIZE);
  if (status == STATUS_PENDING)
    {
      while (io.Status == (NTSTATUS) 0xffffffff)
	Sleep (1L);
      status = io.Status;
    }
  if (!NT_SUCCESS (status))
    {
      debug_printf ("NtFsControlFile(FSCTL_GET_REPARSE_POINT) failed, %y",
		    status);
      /* When accessing the root dir of some remote drives (observed with
	 OS X shares), the FILE_ATTRIBUTE_REPARSE_POINT flag is set, but
	 the followup call to NtFsControlFile(FSCTL_GET_REPARSE_POINT)
	 returns with STATUS_NOT_A_REPARSE_POINT.  That's quite buggy, but
	 we cope here with this scenario by not setting an error code. */
      if (status == STATUS_NOT_A_REPARSE_POINT)
	return 0;
      return -EIO;
    }
  if (rp->ReparseTag == IO_REPARSE_TAG_SYMLINK)
    {
      /* Windows evaluates native symlink literally.  If a remote symlink
	 points to, say, C:\foo, it will be handled as if the target is the
	 local file C:\foo.  That comes in handy since that's how symlinks
	 are treated under POSIX as well. */
      RtlInitCountedUnicodeString (psymbuf,
		(PWCHAR)((PBYTE) rp->SymbolicLinkReparseBuffer.PathBuffer
			 + rp->SymbolicLinkReparseBuffer.SubstituteNameOffset),
		rp->SymbolicLinkReparseBuffer.SubstituteNameLength);
      if ((rp->SymbolicLinkReparseBuffer.Flags & SYMLINK_FLAG_RELATIVE) ||
          check_reparse_point_string (psymbuf))
	return PATH_SYMLINK | PATH_REP;
    }
  else if (!remote && rp->ReparseTag == IO_REPARSE_TAG_MOUNT_POINT)
    {
      /* Don't handle junctions on remote filesystems as symlinks.  This type
	 of reparse point is handled transparently by the OS so that the
	 target of the junction is the remote directory it is supposed to
	 point to.  If we handle it as symlink, it will be mistreated as
	 pointing to a dir on the local system. */
      RtlInitCountedUnicodeString (psymbuf,
		  (PWCHAR)((PBYTE) rp->MountPointReparseBuffer.PathBuffer
			   + rp->MountPointReparseBuffer.SubstituteNameOffset),
		  rp->MountPointReparseBuffer.SubstituteNameLength);
      if (RtlEqualUnicodePathPrefix (psymbuf, &ro_u_volume, TRUE))
	{
	  /* Volume mount point.  Not treated as symlink. The return
	     value -EPERM is a hint for the caller to treat this as a
	     volume mount point. */
	  return -EPERM;
	}
      if (check_reparse_point_string (psymbuf))
	return PATH_SYMLINK | PATH_REP;
    }
  else if (!remote && rp->ReparseTag == IO_REPARSE_TAG_APPEXECLINK)
    {
      /* App execution aliases are commonly used by Windows Store apps. */
      PREPARSE_APPEXECLINK_BUFFER rpl = (PREPARSE_APPEXECLINK_BUFFER) rp;
      WCHAR *buf = rpl->AppExecLinkReparseBuffer.Strings;
      DWORD size = rp->ReparseDataLength / sizeof (WCHAR), n;

      /* It seems that app execution aliases have a payload of four
	 NUL-separated wide string: package id, entry point, executable
	 and application type. We're interested in the executable. */
      for (int i = 0; i < 3 && size > 0; i++)
	{
	  n = wcsnlen (buf, size - 1);
	  if (i == 2 && n > 0 && n < size)
	    {
	      RtlInitCountedUnicodeString (psymbuf, buf, n * sizeof (WCHAR));
	      return PATH_SYMLINK | PATH_REP;
	    }
	  if (i == 2)
	    break;
	  buf += n + 1;
	  size -= n + 1;
	}
    }
  else if (rp->ReparseTag == IO_REPARSE_TAG_LX_SYMLINK)
    {
      /* WSL symlink.  Problem: We have to convert the path to UTF-16 for
	 the caller.  Reparse points are 16K max.  The buffer given to rp
	 is 32K.  So there's enough trailing space in the buffer to convert
	 to UTF-16 and let psymbuf point to it. */
      PREPARSE_LX_SYMLINK_BUFFER rpl = (PREPARSE_LX_SYMLINK_BUFFER) rp;
      char *path_buf = rpl->LxSymlinkReparseBuffer.PathBuffer;
      DWORD path_len = rpl->ReparseDataLength - sizeof (DWORD);
      bool full_path = false;
      const size_t drv_prefix_len = strlen ("/mnt");
      PBYTE utf16_ptr;
      PWCHAR utf16_buf;
      int utf16_bufsize;

      /* 0-terminate path_buf for easier testing. */
      path_buf[path_len] = '\0';
      if (path_prefix_p ("/mnt", path_buf, drv_prefix_len, false))
	{
	  size_t len = strlen (path_buf);

	  if (len <= drv_prefix_len + 1)
	    {
	      /* /mnt or /mnt/.  Replace with cygdrive prefix. */
	      stpcpy (path_buf, mount_table->cygdrive);
	      path_len = mount_table->cygdrive_len;
	      if (len == drv_prefix_len)
		{
		  path_buf[mount_table->cygdrive_len - 1] = '\0';
		  --path_len;
		}
	      rp->ReparseDataLength = path_len + sizeof (DWORD);
	    }
	  else if (islower (path_buf[drv_prefix_len + 1])
		   && (path_len == drv_prefix_len + 2
		       || path_buf[drv_prefix_len + 2] == '/'))
	    {
	      /* Skip forward to the slash leading the drive letter.
		 That leaves room for adding the colon. */
	      path_buf += drv_prefix_len;
	      path_len -= drv_prefix_len;
	      full_path = true;
	    }
	}
      /* Compute buffer for path converted to UTF-16. */
      utf16_ptr = (PBYTE) rpl + sizeof (REPARSE_LX_SYMLINK_BUFFER)
		  + rp->ReparseDataLength;
      /* Skip \0-termination added above. */
      ++utf16_ptr;
      /* Make sure pointer is aligned */
      while ((intptr_t) utf16_ptr % sizeof (WCHAR))
	++utf16_ptr;
      utf16_buf = (PWCHAR) utf16_ptr;
      utf16_bufsize = NT_MAX_PATH - (utf16_buf - (PWCHAR) rpl);
      /* Now convert path to UTF-16. */
      utf16_bufsize = MultiByteToWideChar (CP_UTF8, 0, path_buf, path_len,
					  utf16_buf, utf16_bufsize);
      if (utf16_bufsize)
	{
	  if (full_path)
	    {
	      utf16_buf[0] = utf16_buf[1];	/* Move drive letter to front */
	      utf16_buf[1] = L':';		/* Add colon */
	    }
	  RtlInitCountedUnicodeString (psymbuf, utf16_buf,
				       utf16_bufsize * sizeof (WCHAR));
	  return PATH_SYMLINK | PATH_REP | PATH_REP_NOAPI;
	}
      return -EIO;
    }
  else if (rp->ReparseTag == IO_REPARSE_TAG_CYGUNIX)
    {
      PREPARSE_GUID_DATA_BUFFER rgp = (PREPARSE_GUID_DATA_BUFFER) rp;

      if (memcmp (CYGWIN_SOCKET_GUID, &rgp->ReparseGuid, sizeof (GUID)) == 0)
#ifdef __WITH_AF_UNIX
	return PATH_SOCKET | PATH_REP | PATH_REP_NOAPI;
#else
        /* Recognize this as a reparse point but not as a socket.  */
        return PATH_REP | PATH_REP_NOAPI;
#endif
    }
  else if (rp->ReparseTag == IO_REPARSE_TAG_AF_UNIX)
    /* Native Windows AF_UNIX socket; recognize this as a reparse
       point but not as a socket. */
    return PATH_REP;
  return 0;
}

int
symlink_info::check_reparse_point (HANDLE h, bool remote)
{
  tmp_pathbuf tp;
  PREPARSE_DATA_BUFFER rp = (PREPARSE_DATA_BUFFER) tp.c_get ();
  UNICODE_STRING symbuf;
  char srcbuf[SYMLINK_MAX + 7];

  int ret = check_reparse_point_target (h, remote, rp, &symbuf);
  if (ret <= 0)
    {
      if (ret == -EIO)
	{
	  set_error (EIO);
	  return 0;
	}
      /* Maybe it's a reparse point, but it's certainly not one we recognize.
	 Drop REPARSE attribute so we don't try to use the flag accidentally.
	 It's just some arbitrary file or directory for us. */
      fileattr &= ~FILE_ATTRIBUTE_REPARSE_POINT;
      return ret;
    }
  /* ret is > 0, so it's a known reparse point, path in symbuf. */
  path_flags |= ret;
  if (ret & PATH_SYMLINK)
    {
      sys_wcstombs (srcbuf, SYMLINK_MAX + 7, symbuf.Buffer,
		    symbuf.Length / sizeof (WCHAR));
      /* A symlink is never a directory. */
      fileattr &= ~FILE_ATTRIBUTE_DIRECTORY;
      return posixify (srcbuf);
    }
  else
    return 0;
}

int
symlink_info::check_nfs_symlink (HANDLE h)
{
  tmp_pathbuf tp;
  NTSTATUS status;
  IO_STATUS_BLOCK io;
  struct {
    FILE_GET_EA_INFORMATION fgei;
    char buf[sizeof (NFS_SYML_TARGET)];
  } fgei_buf;
  PFILE_FULL_EA_INFORMATION pffei;
  int res = 0;

  /* To find out if the file is a symlink and to get the symlink target,
     try to fetch the NfsSymlinkTargetName EA. */
  fgei_buf.fgei.NextEntryOffset = 0;
  fgei_buf.fgei.EaNameLength = sizeof (NFS_SYML_TARGET) - 1;
  stpcpy (fgei_buf.fgei.EaName, NFS_SYML_TARGET);
  pffei = (PFILE_FULL_EA_INFORMATION) tp.w_get ();
  status = NtQueryEaFile (h, &io, pffei, NT_MAX_PATH * sizeof (WCHAR), TRUE,
			  &fgei_buf.fgei, sizeof fgei_buf, NULL, TRUE);
  if (NT_SUCCESS (status) && pffei->EaValueLength > 0)
    {
      PWCHAR spath = (PWCHAR)
		     (pffei->EaName + pffei->EaNameLength + 1);
      res = sys_wcstombs (contents, SYMLINK_MAX + 1,
			  spath, pffei->EaValueLength);
      path_flags |= PATH_SYMLINK;
    }
  return res;
}

int
symlink_info::posixify (char *srcbuf)
{
  /* The definition for a path in a native symlink is a bit weird.  The Flags
     value seem to contain 0 for absolute paths (stored as NT native path)
     and 1 for relative paths.  Relative paths are paths not starting with a
     drive letter.  These are not converted to NT native, but stored as
     given.  A path starting with a single backslash is relative to the
     current drive thus a "relative" value (Flags == 1).
     Funny enough it's possible to store paths with slashes instead of
     backslashes, but they are evaluated incorrectly by subsequent Windows
     calls like CreateFile (ERROR_INVALID_NAME).  So, what we do here is to
     take paths starting with slashes at face value, evaluating them as
     Cygwin specific POSIX paths.
     A path starting with two slashes(!) or backslashes is converted into an
     NT UNC path.  Unfortunately, in contrast to POSIX rules, paths starting
     with three or more (back)slashes are also converted into UNC paths,
     just incorrectly sticking to one redundant leading backslash.  We go
     along with this behaviour to avoid scenarios in which native tools access
     other files than Cygwin.
     The above rules are used exactly the same way on Cygwin specific symlinks
     (sysfiles and shortcuts) to eliminate non-POSIX paths in the output. */

  /* Eliminate native NT prefixes. */
  if (srcbuf[0] == '\\' && !strncmp (srcbuf + 1, "??\\", 3))
    {
      srcbuf += 4;
      if (srcbuf[1] != ':') /* native UNC path */
	*(srcbuf += 2) = '\\';
    }
  if (isdrive (srcbuf))
    mount_table->conv_to_posix_path (srcbuf, contents, 0);
  else if (srcbuf[0] == '\\')
    {
      if (srcbuf[1] == '\\') /* UNC path */
	slashify (srcbuf, contents, 0);
      else /* Paths starting with \ are current drive relative. */
	{
	  char cvtbuf[SYMLINK_MAX + 1];

	  stpcpy (cvtbuf + cygheap->cwd.get_drive (cvtbuf), srcbuf);
	  mount_table->conv_to_posix_path (cvtbuf, contents, 0);
	}
    }
  else /* Everything else is taken as is. */
    slashify (srcbuf, contents, 0);
  return strlen (contents);
}

enum
{
  SCAN_BEG,
  SCAN_LNK,
  SCAN_HASLNK,
  SCAN_JUSTCHECK,
  SCAN_JUSTCHECKTHIS, /* Never try to append a suffix. */
  SCAN_APPENDLNK,
  SCAN_EXTRALNK,
  SCAN_DONE,
};

class suffix_scan
{
  const suffix_info *suffixes, *suffixes_start;
  int nextstate;
  char *eopath;
  size_t namelen;
public:
  const char *path;
  char *has (const char *, const suffix_info *);
  int next ();
  int lnk_match () {return nextstate >= SCAN_APPENDLNK;}
  size_t name_len () {return namelen;}
};

char *
suffix_scan::has (const char *in_path, const suffix_info *in_suffixes)
{
  nextstate = SCAN_BEG;
  suffixes = suffixes_start = in_suffixes;

  const char *fname = strrchr (in_path, '\\');
  fname = fname ? fname + 1 : in_path;
  char *ext_here = strrchr (fname, '.');
  path = in_path;
  eopath = strchr (path, '\0');

  if (!ext_here)
    goto noext;

  if (suffixes)
    {
      /* Check if the extension matches a known extension */
      for (const suffix_info *ex = in_suffixes; ex->name != NULL; ex++)
	if (ascii_strcasematch (ext_here, ex->name))
	  {
	    nextstate = SCAN_JUSTCHECK;
	    suffixes = NULL;	/* Has an extension so don't scan for one. */
	    goto done;
	  }
    }

  /* Didn't match.  Use last resort -- .lnk. */
  if (ascii_strcasematch (ext_here, ".lnk"))
    {
      nextstate = SCAN_HASLNK;
      suffixes = NULL;
    }

 noext:
  ext_here = eopath;

 done:
  namelen = eopath - fname;
  /* Avoid attaching suffixes if the resulting filename would be invalid.
     For performance reasons we don't check the length of a suffix, since
     we know that all suffixes are 4 chars in length.

     FIXME: This is not really correct.  A fully functional test should
            work on wide character paths.  This would probably also speed
	    up symlink_info::check. */
  if (namelen > NAME_MAX - 4)
    {
      nextstate = SCAN_JUSTCHECKTHIS;
      suffixes = NULL;
    }
  return ext_here;
}

int
suffix_scan::next ()
{
  for (;;)
    {
      if (!suffixes)
	switch (nextstate)
	  {
	  case SCAN_BEG:
	    suffixes = suffixes_start;
	    if (!suffixes)
	      {
		nextstate = SCAN_LNK;
		return 1;
	      }
	    nextstate = SCAN_EXTRALNK;
	    /* fall through to suffix checking below */
	    break;
	  case SCAN_HASLNK:
	    nextstate = SCAN_APPENDLNK;	/* Skip SCAN_BEG */
	    return 1;
	  case SCAN_EXTRALNK:
	    nextstate = SCAN_DONE;
	    *eopath = '\0';
	    return 0;
	  case SCAN_JUSTCHECK:
	    nextstate = SCAN_LNK;
	    return 1;
	  case SCAN_JUSTCHECKTHIS:
	    nextstate = SCAN_DONE;
	    return 1;
	  case SCAN_LNK:
	  case SCAN_APPENDLNK:
	    nextstate = SCAN_DONE;
	    if (namelen + (*eopath ? 8 : 4) > NAME_MAX)
	      {
		*eopath = '\0';
		return 0;
	      }
	    strcat (eopath, ".lnk");
	    return 1;
	  default:
	    *eopath = '\0';
	    return 0;
	  }

      while (suffixes && suffixes->name)
	if (nextstate == SCAN_EXTRALNK
	    && (!suffixes->addon || namelen > NAME_MAX - 8))
	  suffixes++;
	else
	  {
	    strcpy (eopath, suffixes->name);
	    if (nextstate == SCAN_EXTRALNK)
	      strcat (eopath, ".lnk");
	    suffixes++;
	    return 1;
	  }
      suffixes = NULL;
    }
}

bool
symlink_info::set_error (int in_errno)
{
  bool res;
  if (!(pc_flags & PC_NO_ACCESS_CHECK)
	|| in_errno == ENAMETOOLONG || in_errno == EIO)
    {
      error = in_errno;
      res = true;
    }
  else if (in_errno == ENOENT)
    res = true;
  else
    {
      fileattr = FILE_ATTRIBUTE_NORMAL;
      res = false;
    }
  return res;
}

bool
symlink_info::parse_device (const char *contents)
{
  char *endptr;
  _major_t mymajor;
  _major_t myminor;
  __mode_t mymode;

  mymajor = strtol (contents += 2, &endptr, 16);
  if (endptr == contents)
    return isdevice = false;

  contents = endptr;
  myminor = strtol (++contents, &endptr, 16);
  if (endptr == contents)
    return isdevice = false;

  contents = endptr;
  mymode = strtol (++contents, &endptr, 16);
  if (endptr == contents)
    return isdevice = false;

  if ((mymode & S_IFMT) == S_IFIFO)
    {
      mymajor = _major (FH_FIFO);
      myminor = _minor (FH_FIFO);
    }

  major = mymajor;
  minor = myminor;
  mode = mymode;
  return isdevice = true;
}

/* Probably we have a virtual drive input path and the resulting full path
   starts with the substitution.  Retrieve the target path of the virtual
   drive and try to revert what GetFinalPathNameByHandleW did to the
   drive letter. */
static bool
revert_virtual_drive (PUNICODE_STRING upath, PUNICODE_STRING fpath,
		      bool is_remote, ULONG ci_flag)
{
  /* Get the drive's target path. */
  WCHAR drive[3] = {(WCHAR) towupper (upath->Buffer[4]), L':', L'\0'};
  WCHAR target[MAX_PATH];
  UNICODE_STRING tpath;
  WCHAR *p;

  DWORD remlen = QueryDosDeviceW (drive, target, MAX_PATH);
  if (remlen < 3)
    return false;
  remlen -= 2; /* Two L'\0' */

  if (target[remlen - 1] == L'\\')
    remlen--;
  RtlInitCountedUnicodeString (&tpath, target, remlen * sizeof (WCHAR));

  const USHORT uncp_len = is_remote ? ro_u_uncp.Length / sizeof (WCHAR) - 1 : 0;

  if (is_remote)
    {
      /* target path starts with \??\UNC\. */
      if (RtlEqualUnicodePathPrefix (&tpath, &ro_u_uncp, TRUE))
	{
	  remlen -= uncp_len;
	  p = target + uncp_len;
	}
      /* target path starts with \Device\<redirector>. */
      else if ((p = wcschr (target, L';'))
	       && p + 3 < target + remlen
	       && wcsncmp (p + 1, drive, 2) == 0
	       && (p = wcschr (p + 3, L'\\')))
	remlen -= p - target;
      else
	return false;
      if (wcsncasecmp (fpath->Buffer + uncp_len, p, remlen))
	return false;
    }
  else if (!RtlEqualUnicodePathPrefix (fpath, &tpath, TRUE))
    return false;
  /* Replace fpath with source drive letter and append reminder of
     final path after skipping target path */
  fpath->Buffer[4] = drive[0]; /* Drive letter */
  fpath->Buffer[5] = L':';
  WCHAR *to = fpath->Buffer + 6; /* Next to L':' */
  WCHAR *from = fpath->Buffer + uncp_len + remlen;
  memmove (to, from, (wcslen (from) + 1) * sizeof (WCHAR));
  fpath->Length -= (from - to) * sizeof (WCHAR);
  if (RtlEqualUnicodeString (upath, fpath, !!ci_flag))
    return false;
  return true;
}

/* Check if PATH is a symlink.  PATH must be a valid Win32 path name.

   If PATH is a symlink, put the value of the symlink--the file to
   which it points--into CONTENTS.

   Set PATH_SYMLINK if PATH is a symlink.

   If PATH is a symlink, return the length stored into CONTENTS.  If
   the inner components of PATH contain native symlinks or junctions,
   or if the drive is a virtual drive, compare PATH with the result
   returned by GetFinalPathNameByHandleA.  If they differ, store the
   final path in CONTENTS and return the negative of its length.  In
   all other cases, return 0.  */

int
symlink_info::check (char *path, const suffix_info *suffixes, fs_info &fs,
		     path_conv_handle &conv_hdl)
{
  int res;
  HANDLE h;
  NTSTATUS status;
  UNICODE_STRING upath;
  OBJECT_ATTRIBUTES attr;
  IO_STATUS_BLOCK io;
  suffix_scan suffix;

  const ULONG ci_flag = cygwin_shared->obcaseinsensitive
			|| (mount_flags & MOUNT_NOPOSIX)
			? OBJ_CASE_INSENSITIVE : 0;
  /* TODO: Temporarily do all char->UNICODE conversion here.  This should
     already be slightly faster than using Ascii functions. */
  tmp_pathbuf tp;
  tp.u_get (&upath);
  InitializeObjectAttributes (&attr, &upath, ci_flag, NULL, NULL);

  /* This label is used in case we encounter a FS which only handles
     DOS paths.  See below. */
  bool restarted = false;
restart:

  h = NULL;
  res = 0;
  contents[0] = '\0';
  issymlink = true;
  isdevice = false;
  major = 0;
  minor = 0;
  mode = 0;
  // mount_flags is an incoming value set in path_conv */
  path_flags = 0;

  PVOID eabuf = &nfs_aol_ffei;
  ULONG easize = sizeof nfs_aol_ffei;

  ext_here = suffix.has (path, suffixes);
  extn = ext_here - path;
  bool had_ext = !!*ext_here;

  /* If the filename is too long, don't even try. */
  if (suffix.name_len () > NAME_MAX)
    {
      set_error (ENAMETOOLONG);
      goto file_not_symlink;
    }

  while (suffix.next ())
    {
      res = 0;
      error = 0;
      get_nt_native_path (suffix.path, upath, mount_flags & MOUNT_DOS);
      if (h)
	{
	  NtClose (h);
	  h = NULL;
	}
      /* The EA given to NtCreateFile allows to get a handle to a symlink on
	 an NFS share, rather than getting a handle to the target of the
	 symlink (which would spoil the task of this method quite a bit).
	 Fortunately it's ignored on most other file systems so we don't have
	 to special case NFS too much. */
      status = NtCreateFile (&h,
			     READ_CONTROL | FILE_READ_ATTRIBUTES | FILE_READ_EA,
			     &attr, &io, NULL, 0, FILE_SHARE_VALID_FLAGS,
			     FILE_OPEN,
			     FILE_OPEN_REPARSE_POINT
			     | FILE_OPEN_FOR_BACKUP_INTENT,
			     eabuf, easize);
      debug_printf ("%y = NtCreateFile (%S)", status, &upath);
      /* No right to access EAs or EAs not supported? */
      if (!NT_SUCCESS (status)
	  && (status == STATUS_ACCESS_DENIED
	      || status == STATUS_EAS_NOT_SUPPORTED
	      || status == STATUS_NOT_SUPPORTED
	      || status == STATUS_INVALID_NETWORK_RESPONSE
	      /* Or a bug in Samba 3.2.x (x <= 7) when accessing a share's
		 root dir which has EAs enabled? */
	      || status == STATUS_INVALID_PARAMETER))
	{
	  /* If EAs are not supported, there's no sense to check them again
	     with suffixes attached.  So we set eabuf/easize to 0 here once. */
	  if (status == STATUS_EAS_NOT_SUPPORTED
	      || status == STATUS_NOT_SUPPORTED)
	    {
	      eabuf = NULL;
	      easize = 0;
	    }
	  status = NtOpenFile (&h, READ_CONTROL | FILE_READ_ATTRIBUTES,
			       &attr, &io, FILE_SHARE_VALID_FLAGS,
			       FILE_OPEN_REPARSE_POINT
			       | FILE_OPEN_FOR_BACKUP_INTENT);
	  debug_printf ("%y = NtOpenFile (no-EAs %S)", status, &upath);
	}
      if (status == STATUS_OBJECT_NAME_NOT_FOUND)
	{
	  /* There are filesystems out in the wild (Netapp, NWFS, and others)
	     which are uncapable of generating pathnames outside the Win32
	     rules.  That means, filenames on these FSes must not have a
	     leading space or trailing dots and spaces.  This code snippet
	     manages them.  I really hope it's streamlined enough not to
	     slow down normal operation.  This extra check only kicks in if
	     we encountered a STATUS_OBJECT_NAME_NOT_FOUND *and* we didn't
	     already attach a suffix. */
	  if (!restarted && !*ext_here && ext_here[-1] != '\\'
	      && !(mount_flags & MOUNT_DOS))
	    {
	      /* Check for trailing dot or space or leading space in
		 last component. */
	      char *p = ext_here - 1;
	      if (*p != '.' && *p != ' ')
		{
		  while (*--p != '\\')
		    assert(p >= path);
		  if (*++p != ' ')
		    p = NULL;
		}
	      if (p)
		{
		  /* If so, check if file resides on one of the known broken
		     FSes only supporting filenames following DOS rules. */
		  fs.update (&upath, NULL);
		  if (fs.has_dos_filenames_only ())
		    {
		      /* If so, try again.  Since we now know the FS, the
			 filenames will be tweaked to follow DOS rules via the
			 third parameter in the call to get_nt_native_path. */
		      mount_flags |= MOUNT_DOS;
		      restarted = true;
		      goto restart;
		    }
		}
	    }
	}
      else if (status == STATUS_NETWORK_OPEN_RESTRICTION
	       || status == STATUS_SYMLINK_CLASS_DISABLED)
	{
	  /* These status codes are returned if you try to open a native
	     symlink and the usage of this kind of symlink is forbidden
	     (see fsutil).  Since we can't open them at all, not even for
	     stat purposes, we have to return a POSIX error code which is
	     at least a bit helpful.

	     Additionally Windows 8 introduces a bug in NFS: If you have
	     a symlink to a directory, with symlinks underneath, resolving
	     the second level of symlinks fails if remote->remote symlinks
	     are disabled in fsutil.  Unfortunately that's the default. */
	  set_error (ELOOP);
	  break;
	}

      if (NT_SUCCESS (status)
	  /* Check file system while we're having the file open anyway.
	     This speeds up path_conv noticably (~10%). */
	  && (fs.inited () || fs.update (&upath, h)))
	{
	  status = conv_hdl.get_finfo (h, fs.is_nfs ());
	  if (NT_SUCCESS (status))
	    fileattr = conv_hdl.get_dosattr (fs.is_nfs ());
	}
      if (!NT_SUCCESS (status))
	{
	  debug_printf ("%y = NtQueryInformationFile (%S)", status, &upath);
	  fileattr = INVALID_FILE_ATTRIBUTES;

	  /* One of the inner path components is invalid, or the path contains
	     invalid characters.  Bail out with ENOENT.

	     STATUS_IO_REPARSE_TAG_NOT_HANDLED is returned when trying to
	     traversing a WSL symlink.  For all practical purposes it's
	     equivalent to traversing SYSTEM- or LNK-type symlink returning
	     STATUS_OBJECT_PATH_NOT_FOUND.

	     Note that additional STATUS_OBJECT_PATH_INVALID and
	     STATUS_OBJECT_PATH_SYNTAX_BAD status codes exist.  The first one
	     is seemingly not generated by NtQueryInformationFile, the latter
	     is only generated if the path is no absolute path within the
	     NT name space, which should not happen and would point to an
	     error in get_nt_native_path.  Both status codes are deliberately
	     not tested here unless proved necessary. */
	  if (status == STATUS_OBJECT_PATH_NOT_FOUND
	      || status == STATUS_IO_REPARSE_TAG_NOT_HANDLED
	      || status == STATUS_OBJECT_NAME_INVALID
	      || status == STATUS_BAD_NETWORK_PATH
	      || status == STATUS_BAD_NETWORK_NAME
	      || status == STATUS_NO_MEDIA_IN_DEVICE)
	    {
	      set_error (ENOENT);
	      if (ext_tacked_on && !had_ext)
		{
		  *ext_here = '\0';
		  ext_tacked_on = false;
		  ext_here = NULL;
		  extn = 0;
		}
	      goto file_not_symlink;
	    }
	  if (status != STATUS_OBJECT_NAME_NOT_FOUND
	      && status != STATUS_NO_SUCH_FILE) /* ENOENT on NFS or 9x share */
	    {
	      /* The file exists, but the user can't access it for one reason
		 or the other.  To get the file attributes we try to access the
		 information by opening the parent directory and getting the
		 file attributes using a matching NtQueryDirectoryFile call. */
	      UNICODE_STRING dirname, basename;
	      OBJECT_ATTRIBUTES dattr;
	      HANDLE dir;
	      struct {
		FILE_ID_BOTH_DIR_INFORMATION fdi;
		WCHAR dummy_buf[NAME_MAX + 1];
	      } fdi_buf;

	      RtlSplitUnicodePath (&upath, &dirname, &basename);
	      InitializeObjectAttributes (&dattr, &dirname, ci_flag,
					  NULL, NULL);
	      status = NtOpenFile (&dir, SYNCHRONIZE | FILE_LIST_DIRECTORY,
				   &dattr, &io, FILE_SHARE_VALID_FLAGS,
				   FILE_SYNCHRONOUS_IO_NONALERT
				   | FILE_OPEN_FOR_BACKUP_INTENT
				   | FILE_DIRECTORY_FILE);
	      if (!NT_SUCCESS (status))
		{
		  debug_printf ("%y = NtOpenFile(%S)", status, &dirname);
		  /* There's a special case if the file is itself the root
		     of a drive which is not accessible by the current user.
		     This case is only recognized by the length of the
		     basename part.  If it's 0, the incoming file is the
		     root of a drive.  So we at least know it's a directory. */
		  if (basename.Length)
		    fileattr = FILE_ATTRIBUTE_DIRECTORY;
		  else
		    {
		      fileattr = 0;
		      set_error (geterrno_from_nt_status (status));
		    }
		}
	      else
		{
		  status = NtQueryDirectoryFile (dir, NULL, NULL, NULL, &io,
						 &fdi_buf, sizeof fdi_buf,
						 FileIdBothDirectoryInformation,
						 TRUE, &basename, TRUE);
		  /* Take the opportunity to check file system while we're
		     having the handle to the parent dir. */
		  fs.update (&upath, dir);
		  NtClose (dir);
		  if (!NT_SUCCESS (status))
		    {
		      debug_printf ("%y = NtQueryDirectoryFile(%S)",
				    status, &dirname);
		      if (status == STATUS_NO_SUCH_FILE)
			{
			  /* This can happen when trying to access files
			     which match DOS device names on SMB shares.
			     NtOpenFile failed with STATUS_ACCESS_DENIED,
			     but the NtQueryDirectoryFile tells us the
			     file doesn't exist.  We're suspicious in this
			     case and retry with the next suffix instead of
			     just giving up. */
			  set_error (ENOENT);
			  continue;
			}
		      fileattr = 0;
		    }
		  else
		    {
		      PFILE_ALL_INFORMATION pfai = conv_hdl.fai ();

		      fileattr = fdi_buf.fdi.FileAttributes;
		      memcpy (&pfai->BasicInformation.CreationTime,
			      &fdi_buf.fdi.CreationTime,
			      4 * sizeof (LARGE_INTEGER));
		      pfai->BasicInformation.FileAttributes = fileattr;
		      pfai->StandardInformation.AllocationSize.QuadPart
			= fdi_buf.fdi.AllocationSize.QuadPart;
		      pfai->StandardInformation.EndOfFile.QuadPart
			= fdi_buf.fdi.EndOfFile.QuadPart;
		      pfai->StandardInformation.NumberOfLinks = 1;
		      pfai->InternalInformation.IndexNumber.QuadPart
			= fdi_buf.fdi.FileId.QuadPart;
		    }
		}
	      ext_tacked_on = !!*ext_here;
	      goto file_not_symlink;
	    }
	  set_error (ENOENT);
	  continue;
	}

      ext_tacked_on = !!*ext_here;
      /* Don't allow to returns directories with appended suffix.  If we found
	 a directory with a suffix which has been appended here, then this
	 directory doesn't match the request.  So, just do as usual if file
	 hasn't been found. */
      if (ext_tacked_on && !had_ext && (fileattr & FILE_ATTRIBUTE_DIRECTORY))
	{
	  fileattr = INVALID_FILE_ATTRIBUTES;
	  set_error (ENOENT);
	  continue;
	}

      /* Consider the situation where a virtual drive points to a native
         symlink.  Opening the virtual drive with FILE_OPEN_REPARSE_POINT
	 actually opens the symlink.  If this symlink points to another
	 directory using a relative path, symlink evaluation goes totally
	 awry.  We never want a virtual drive evaluated as symlink. */
      if (upath.Length <= 14)
	  goto file_not_symlink;

      /* Reparse points are potentially symlinks.  This check must be
	 performed before checking the SYSTEM attribute for sysfile
	 symlinks, since reparse points can have this flag set, too. */
      if ((fileattr & FILE_ATTRIBUTE_REPARSE_POINT))
	{
	  res = check_reparse_point (h, fs.is_remote_drive ());
	  if (res > 0)
	    {
	      /* A symlink is never a directory. */
	      conv_hdl.fai ()->BasicInformation.FileAttributes
		&= ~FILE_ATTRIBUTE_DIRECTORY;
	      break;
	    }
	  else if (res == 0 && (path_flags & PATH_REP))
	    /* Known reparse point but not a symlink. */
	    goto file_not_symlink;
	  else
	    {
	      /* Volume moint point or unrecognized reparse point type.
		 Make sure the open handle is not used in later stat calls.
		 The handle has been opened with the FILE_OPEN_REPARSE_POINT
		 flag, so it's a handle to the reparse point, not a handle
		 to the volumes root dir. */
	      pc_flags &= ~PC_KEEP_HANDLE;
	      /* Volume mount point:  The filesystem information for the top
		 level directory should be for the volume top level directory,
		 rather than for the reparse point itself.  So we fetch the
		 filesystem information again, but with a NULL handle.
		 This does what we want because fs_info::update opens the
		 handle without FILE_OPEN_REPARSE_POINT. */
	      if (res < 0)
		fs.update (&upath, NULL);
	    }
	}

      /* Windows shortcuts are potentially treated as symlinks.  Valid Cygwin
	 & U/WIN shortcuts are R/O, but definitely not directories. */
      else if ((fileattr & (FILE_ATTRIBUTE_READONLY | FILE_ATTRIBUTE_DIRECTORY))
	  == FILE_ATTRIBUTE_READONLY && suffix.lnk_match ())
	{
	  HANDLE sym_h;

	  status = NtOpenFile (&sym_h, SYNCHRONIZE | GENERIC_READ, &attr, &io,
			       FILE_SHARE_VALID_FLAGS,
			       FILE_OPEN_FOR_BACKUP_INTENT
			       | FILE_SYNCHRONOUS_IO_NONALERT);
	  if (!NT_SUCCESS (status))
	    res = 0;
	  else
	    {
	      res = check_shortcut (sym_h);
	      NtClose (sym_h);
	    }
	  if (!res)
	    {
	      /* If searching for `foo' and then finding a `foo.lnk' which
		 is no shortcut, return the same as if file not found. */
	      if (ext_tacked_on)
		{
		  fileattr = INVALID_FILE_ATTRIBUTES;
		  set_error (ENOENT);
		  continue;
		}
	    }
	  else if (contents[0] != ':' || contents[1] != '\\'
		   || !parse_device (contents))
	    break;
	}

      /* If searching for `foo' and then finding a `foo.lnk' which is
	 no shortcut, return the same as if file not found. */
      else if (suffix.lnk_match () && ext_tacked_on)
	{
	  fileattr = INVALID_FILE_ATTRIBUTES;
	  set_error (ENOENT);
	  continue;
	}

      /* This is the old Cygwin method creating symlinks.  A symlink will
	 have the `system' file attribute.  Only files can be symlinks
	 (which can be symlinks to directories). */
      else if ((fileattr & (FILE_ATTRIBUTE_SYSTEM | FILE_ATTRIBUTE_DIRECTORY))
	       == FILE_ATTRIBUTE_SYSTEM)
	{
	  HANDLE sym_h;

	  status = NtOpenFile (&sym_h, SYNCHRONIZE | GENERIC_READ, &attr, &io,
			       FILE_SHARE_VALID_FLAGS,
			       FILE_OPEN_FOR_BACKUP_INTENT
			       | FILE_SYNCHRONOUS_IO_NONALERT);

	  if (!NT_SUCCESS (status))
	    res = 0;
	  else
	    {
	      res = check_sysfile (sym_h);
	      NtClose (sym_h);
	    }
	  if (res)
	    break;
	}

      /* If the file is on an NFS share and could be opened with extended
	 attributes, check if it's a symlink.  Only files can be symlinks
	 (which can be symlinks to directories). */
      else if (fs.is_nfs () && (conv_hdl.nfsattr ()->type & 7) == NF3LNK)
	{
	  res = check_nfs_symlink (h);
	  if (res)
	    break;
	}

      /* Check if the inner path components contain native symlinks or
	 junctions, or if the drive is a virtual drive.  Compare incoming
	 path with path returned by GetFinalPathNameByHandleA.  If they
	 differ, return the final path as symlink content and set symlen
	 to a negative value.  This forces path_conv::check to restart
	 symlink evaluation with the new path. */
      if ((pc_flags & (PC_SYM_FOLLOW | PC_SYM_NOFOLLOW_REP)) == PC_SYM_FOLLOW)
	{
	  PWCHAR fpbuf = tp.w_get ();
	  DWORD ret;

	  ret = GetFinalPathNameByHandleW (h, fpbuf, NT_MAX_PATH, 0);
	  if (ret)
	    {
	      UNICODE_STRING fpath;

	      /* If incoming path has no trailing backslash, but final path
		 has one, drop trailing backslash from final path so the
		 below string comparison has a chance to succeed.
		 On the contrary, if incoming path has trailing backslash,
		 but final path does not have one, add trailing backslash
		 to the final path. */
	      if (upath.Buffer[(upath.Length - 1) / sizeof (WCHAR)] != L'\\'
		  && fpbuf[ret - 1] == L'\\')
                fpbuf[--ret] = L'\0';
	      if (upath.Buffer[(upath.Length - 1) / sizeof (WCHAR)] == L'\\'
		  && fpbuf[ret - 1] != L'\\' && ret < NT_MAX_PATH - 1)
		{
		  fpbuf[ret++] = L'\\';
		  fpbuf[ret] = L'\0';
		}
	      fpbuf[1] = L'?';	/* \\?\ --> \??\ */
	      RtlInitCountedUnicodeString (&fpath, fpbuf, ret * sizeof (WCHAR));
	      if (!RtlEqualUnicodeString (&upath, &fpath, !!ci_flag))
	        {
		  /* If the incoming path is a local drive letter path... */
		  if (!RtlEqualUnicodePathPrefix (&upath, &ro_u_uncp, TRUE))
		    {
		      /* ...and the final path is an UNC path, revert to the
			 drive letter path syntax. */
		      if (RtlEqualUnicodePathPrefix (&fpath, &ro_u_uncp, TRUE))
			{
			  if (!revert_virtual_drive (&upath, &fpath, true,
						     ci_flag))
			    goto file_not_symlink;
			}
		      /* ...otherwise, if the final path changes the drive
			 letter, let revert_virtual_drive check for a
			 virtual drive and revert that. */
		      else if (upath.Buffer[5] == L':'
			       && (WCHAR) towupper (upath.Buffer[4])
				  != (WCHAR) towupper (fpath.Buffer[4]))
			{
			  if (!revert_virtual_drive (&upath, &fpath, false,
						     ci_flag))
			    goto file_not_symlink;
			}
		    }
		  issymlink = true;
		  /* upath.Buffer is big enough and unused from this point on.
		     Reuse it here, avoiding yet another buffer allocation. */
		  char *nfpath = (char *) upath.Buffer;
		  sys_wcstombs (nfpath, NT_MAX_PATH, fpbuf);
		  /* For final paths differing in inner path components return
		     length as negative value.  This informs path_conv::check
		     to skip realpath handling on the last path component. */
		  res = -posixify (nfpath);
		  break;
	        }
	    }
	}

    /* Normal file. */
    file_not_symlink:
      issymlink = false;
      syscall_printf ("%s", isdevice ? "is a device" : "not a symlink");
      res = 0;
      break;
    }

  if (h)
    {
      if (pc_flags & PC_KEEP_HANDLE)
	conv_hdl.set (h);
      else
	NtClose (h);
    }

  syscall_printf ("%d = symlink.check(%s, %p) (mount_flags %y, path_flags %y)",
		  res, suffix.path, contents, mount_flags, path_flags);
  return res;
}

/* "path" is the path in a virtual symlink.  Set a symlink_info struct from
   that and proceed with further path checking afterwards. */
int
symlink_info::set (char *path)
{
  strcpy (contents, path);
  mount_flags = 0;
  path_flags = PATH_SYMLINK;
  fileattr = FILE_ATTRIBUTE_NORMAL;
  error = 0;
  issymlink = true;
  isdevice = false;
  ext_tacked_on = false;
  ext_here = NULL;
  extn = major = minor = mode = 0;
  return strlen (path);
}

/* readlink system call */

extern "C" ssize_t
readlink (const char *__restrict path, char *__restrict buf, size_t buflen)
{
  if (buflen < 0)
    {
      set_errno (ENAMETOOLONG);
      return -1;
    }

  path_conv pathbuf (path, PC_SYM_CONTENTS, stat_suffixes);

  if (pathbuf.error)
    {
      set_errno (pathbuf.error);
      syscall_printf ("-1 = readlink (%s, %p, %lu)", path, buf, buflen);
      return -1;
    }

  if (!pathbuf.exists ())
    {
      set_errno (ENOENT);
      return -1;
    }

  if (!pathbuf.issymlink ())
    {
      if (pathbuf.exists ())
	set_errno (EINVAL);
      return -1;
    }

  size_t pathbuf_len = strlen (pathbuf.get_win32 ());
  ssize_t len = MIN (buflen, pathbuf_len);
  memcpy (buf, pathbuf.get_win32 (), len);

  /* errno set by symlink.check if error */
  return len;
}

/* Some programs rely on st_dev/st_ino being unique for each file.
   Hash the path name and hope for the best.  The hash arg is not
   always initialized to zero since readdir needs to compute the
   dirent ino_t based on a combination of the hash of the directory
   done during the opendir call and the hash or the filename within
   the directory.  FIXME: Not bullet-proof. */
/* Cygwin internal */
ino_t
hash_path_name (ino_t hash, PUNICODE_STRING name)
{
  if (name->Length == 0)
    return hash;

  /* Build up hash. Name is already normalized */
  USHORT len = name->Length / sizeof (WCHAR);
  for (USHORT idx = 0; idx < len; ++idx)
    hash = RtlUpcaseUnicodeChar (name->Buffer[idx])
	   + (hash << 6) + (hash << 16) - hash;
  return hash;
}

ino_t
hash_path_name (ino_t hash, PCWSTR name)
{
  UNICODE_STRING uname;
  RtlInitUnicodeString (&uname, name);
  return hash_path_name (hash, &uname);
}

ino_t
hash_path_name (ino_t hash, const char *name)
{
  UNICODE_STRING uname;
  tmp_pathbuf tp;

  tp.u_get (&uname);
  sys_mbstouni (&uname, HEAP_NOTHEAP, name);
  ino_t ret = hash_path_name (hash, &uname);
  return ret;
}

extern "C" char *
getcwd (char *buf, size_t ulen)
{
  char* res = NULL;

  __try
    {
      if (ulen == 0 && buf)
	set_errno (EINVAL);
      else
	res = cygheap->cwd.get (buf, 1, 1, ulen);
    }
  __except (EFAULT) {}
  __endtry
  return res;
}

/* getwd: Legacy. */
extern "C" char *
getwd (char *buf)
{
  return getcwd (buf, PATH_MAX + 1);  /*Per SuSv3!*/
}

extern "C" char *
get_current_dir_name (void)
{
  const char *pwd = getenv ("PWD");
  char *cwd = getcwd (NULL, 0);
  struct stat pwdbuf, cwdbuf;

  if (pwd && strcmp (pwd, cwd) != 0
      && stat (pwd, &pwdbuf) == 0
      && stat (cwd, &cwdbuf) == 0
      && pwdbuf.st_dev == cwdbuf.st_dev
      && pwdbuf.st_ino == cwdbuf.st_ino)
    {
      cwd = (char *) realloc (cwd, strlen (pwd) + 1);
      strcpy (cwd, pwd);
    }

  return cwd;
}

/* chdir: POSIX 5.2.1.1 */
extern "C" int
chdir (const char *in_dir)
{
  int res = -1;

  __try
    {
      if (!*in_dir)
	{
	  set_errno (ENOENT);
	  __leave;
	}

      syscall_printf ("dir '%s'", in_dir);

      /* Convert path.  PC_NONULLEMPTY ensures that we don't check for
	 NULL/empty/invalid again. */
      path_conv path (in_dir, PC_SYM_FOLLOW | PC_POSIX | PC_NONULLEMPTY);
      if (path.error)
	{
	  set_errno (path.error);
	  syscall_printf ("-1 = chdir (%s)", in_dir);
	  __leave;
	}

      const char *posix_cwd = NULL;
      dev_t devn = path.get_device ();
      if (!path.exists ())
	set_errno (ENOENT);
      else if (!path.isdir ())
	set_errno (ENOTDIR);
      else if (!isvirtual_dev (devn))
	{
	  /* The sequence chdir("xx"); chdir(".."); must be a noop if xx
	     is not a symlink. This is exploited by find.exe.
	     The posix_cwd is just path.get_posix ().
	     In other cases we let cwd.set obtain the Posix path through
	     the mount table. */
	  if (!isdrive (path.get_posix ()))
	    posix_cwd = path.get_posix ();
	  res = 0;
	}
      else
       {
	 posix_cwd = path.get_posix ();
	 res = 0;
       }

      if (!res)
	res = cygheap->cwd.set (&path, posix_cwd);

      /* Note that we're accessing cwd.posix without a lock here.
	 I didn't think it was worth locking just for strace. */
      syscall_printf ("%R = chdir() cygheap->cwd.posix '%s' native '%S'", res,
		      cygheap->cwd.get_posix (), path.get_nt_native_path ());
    }
  __except (EFAULT)
    {
      res = -1;
    }
  __endtry
  return res;
}

extern "C" int
fchdir (int fd)
{
  int res;
  cygheap_fdget cfd (fd);
  if (cfd >= 0)
    res = chdir (cfd->get_name ());
  else
    res = -1;

  syscall_printf ("%R = fchdir(%d)", res, fd);
  return res;
}

/******************** Exported Path Routines *********************/

/* Cover functions to the path conversion routines.
   These are exported to the world as cygwin_foo by cygwin.din.  */

#define return_with_errno(x) \
  do {\
    int err = (x);\
    if (!err)\
     return 0;\
    set_errno (err);\
    return -1;\
  } while (0)

extern "C" ssize_t
cygwin_conv_path (cygwin_conv_path_t what, const void *from, void *to,
		  size_t size)
{
  tmp_pathbuf tp;
  path_conv p;
  size_t lsiz = 0;
  char *buf = NULL;
  PWCHAR path = NULL;
  int error = 0;
  int how = what & CCP_CONVFLAGS_MASK;
  what &= CCP_CONVTYPE_MASK;
  int ret = -1;

  __try
    {
      if (!from)
	{
	  set_errno (EINVAL);
	  __leave;
	}

      switch (what)
	{
	case CCP_POSIX_TO_WIN_A:
	  {
	    p.check ((const char *) from,
		     PC_POSIX | PC_SYM_FOLLOW | PC_SYM_NOFOLLOW_REP
		     | PC_NO_ACCESS_CHECK
		     | ((how & CCP_RELATIVE) ? PC_NOFULL : 0), stat_suffixes);
	    if (p.error)
	      {
	        set_errno (p.error);
		__leave;
	      }
	    PUNICODE_STRING up = p.get_nt_native_path ();
	    buf = tp.c_get ();
	    sys_wcstombs (buf, NT_MAX_PATH,
			  up->Buffer, up->Length / sizeof (WCHAR));
	    /* Convert native path to standard DOS path. */
	    if (!strncmp (buf, "\\??\\", 4))
	      {
		buf += 4;
		if (buf[1] != ':') /* native UNC path */
		  *(buf += 2) = '\\';
	      }
	    else if (*buf == '\\')
	      {
		/* Device name points to somewhere else in the NT namespace.
		   Use GLOBALROOT prefix to convert to Win32 path. */
		char *p = buf + sys_wcstombs (buf, NT_MAX_PATH,
					      ro_u_globalroot.Buffer,
					      ro_u_globalroot.Length
					      / sizeof (WCHAR));
		sys_wcstombs (p, NT_MAX_PATH - (p - buf),
			      up->Buffer, up->Length / sizeof (WCHAR));
	      }
	    lsiz = strlen (buf) + 1;
	    /* TODO: Incoming "." is a special case which leads to a trailing
	       backslash ".\\" in the Win32 path.  That's a result of the
	       conversion in normalize_posix_path.  This should not occur
	       so the below code is just a band-aid. */
	    if ((how & CCP_RELATIVE) && !strcmp ((const char *) from, ".")
		&& !strcmp (buf, ".\\"))
	      {
		lsiz = 2;
		buf[1] = '\0';
	      }
	  }
	  break;
	case CCP_POSIX_TO_WIN_W:
	  p.check ((const char *) from,
		   PC_POSIX | PC_SYM_FOLLOW | PC_SYM_NOFOLLOW_REP
		   | PC_NO_ACCESS_CHECK
		   | ((how & CCP_RELATIVE) ? PC_NOFULL : 0), stat_suffixes);
	  if (p.error)
	    {
	      set_errno (p.error);
	      __leave;
	    }
	  /* Relative Windows paths are always restricted to MAX_PATH chars. */
	  if ((how & CCP_RELATIVE) && !isabspath (p.get_win32 ())
	      && sys_mbstowcs (NULL, 0, p.get_win32 ()) > MAX_PATH)
	    {
	      /* Recreate as absolute path. */
	      p.check ((const char *) from, PC_POSIX | PC_SYM_FOLLOW
					    | PC_NO_ACCESS_CHECK);
	      if (p.error)
		{
		  set_errno (p.error);
		  __leave;
		}
	    }
	  lsiz = p.get_wide_win32_path_len () + 1;
	  path = p.get_nt_native_path ()->Buffer;

	  /* Convert native path to standard DOS path. */
	  if (!wcsncmp (path, L"\\??\\", 4))
	    {
	      path[1] = L'\\';

	      /* Drop long path prefix for short pathnames.  Unfortunately there's
		 quite a bunch of Win32 functions, especially in user32.dll,
		 apparently, which don't grok long path names at all, not even
		 in the UNICODE API. */
	      if ((path[5] == L':' && lsiz <= MAX_PATH + 4)
		  || (!wcsncmp (path + 4, L"UNC\\", 4) && lsiz <= MAX_PATH + 6))
		{
		  path += 4;
		  lsiz -= 4;
		  if (path[1] != L':')
		    {
		      *(path += 2) = '\\';
		      lsiz -= 2;
		    }
		}
	    }
	  else if (*path == L'\\')
	    {
	      /* Device name points to somewhere else in the NT namespace.
		 Use GLOBALROOT prefix to convert to Win32 path. */
	      to = (void *) wcpcpy ((wchar_t *) to, ro_u_globalroot.Buffer);
	      lsiz += ro_u_globalroot.Length / sizeof (WCHAR);
	    }
	  /* TODO: Same ".\\" band-aid as in CCP_POSIX_TO_WIN_A case. */
	  if ((how & CCP_RELATIVE) && !strcmp ((const char *) from, ".")
	      && !wcscmp (path, L".\\"))
	    {
	      lsiz = 2;
	      path[1] = L'\0';
	    }
	  lsiz *= sizeof (WCHAR);
	  break;
	case CCP_WIN_A_TO_POSIX:
	  buf = tp.c_get ();
	  error = mount_table->conv_to_posix_path ((const char *) from, buf,
						   how | __CCP_APP_SLASH);
	  if (error)
	    {
	      set_errno (p.error);
	      __leave;
	    }
	  lsiz = strlen (buf) + 1;
	  break;
	case CCP_WIN_W_TO_POSIX:
	  buf = tp.c_get ();
	  error = mount_table->conv_to_posix_path ((const PWCHAR) from, buf,
						   how | __CCP_APP_SLASH);
	  if (error)
	    {
	      set_errno (error);
	      __leave;
	    }
	  lsiz = strlen (buf) + 1;
	  break;
	default:
	  set_errno (EINVAL);
	  __leave;
	}
      if (!size)
	{
	  ret = lsiz;
	  __leave;
	}
      if (size < lsiz)
	{
	  set_errno (ENOSPC);
	  __leave;
	}
      switch (what)
	{
	case CCP_POSIX_TO_WIN_A:
	case CCP_WIN_A_TO_POSIX:
	case CCP_WIN_W_TO_POSIX:
	  stpcpy ((char *) to, buf);
	  break;
	case CCP_POSIX_TO_WIN_W:
	  wcpcpy ((PWCHAR) to, path);
	  break;
	}
      ret = 0;
    }
  __except (EFAULT) {}
  __endtry
  return ret;
}

extern "C" void *
cygwin_create_path (cygwin_conv_path_t what, const void *from)
{
  void *to;
  ssize_t size = cygwin_conv_path (what, from, NULL, 0);
  if (size <= 0)
    to = NULL;
  else if (!(to = malloc (size)))
    to = NULL;
  if (cygwin_conv_path (what, from, to, size) == -1)
    {
      free (to);
      to = NULL;
    }
  return to;
}

/* The realpath function is required by POSIX:2008.  */

extern "C" char *
realpath (const char *__restrict path, char *__restrict resolved)
{
  tmp_pathbuf tp;
  char *tpath;

  /* Make sure the right errno is returned if path is NULL. */
  if (!path)
    {
      set_errno (EINVAL);
      return NULL;
    }

  /* Guard reading from a potentially invalid path and writing to a
     potentially invalid resolved. */
  __try
    {
      /* Win32 drive letter paths and, generally, any path starting with a
	 backslash, have to be converted to a POSIX path first, because
	 path_conv leaves the incoming path untouched except for converting
	 backslashes to forward slashes.  This also covers '\\?\ and '\??\'
	 path prefixes. */
      if (isdrive (path) || path[0] == '\\')
	{
	  tpath = tp.c_get ();
	  mount_table->conv_to_posix_path (path, tpath, 0);
	}
      else
	tpath = (char *) path;

      path_conv real_path (tpath, PC_SYM_FOLLOW | PC_POSIX, stat_suffixes);


      /* POSIX 2008 requires malloc'ing if resolved is NULL, and states
	 that using non-NULL resolved is asking for portability
	 problems.  */

      if (!real_path.error && real_path.exists ())
	{
	  if (!resolved)
	    {
	      resolved = (char *)
			 malloc (strlen (real_path.get_posix ()) + 1);
	      if (!resolved)
		return NULL;
	    }
	  strcpy (resolved, real_path.get_posix ());
	  return resolved;
	}

      /* FIXME: on error, Linux puts the name of the path
	 component which could not be resolved into RESOLVED, but POSIX
	 does not require this.  */
      if (resolved)
	resolved[0] = '\0';
      set_errno (real_path.error ?: ENOENT);
    }
  __except (EFAULT) {}
  __endtry
  return NULL;
}

/* Linux provides this extension.  Since the only portable use of
   realpath requires a NULL second argument, we might as well have a
   one-argument wrapper.  */
extern "C" char *
canonicalize_file_name (const char *path)
{
  return realpath (path, NULL);
}

/* Return non-zero if path is a POSIX path list.
   This is exported to the world as cygwin_foo by cygwin.din.

DOCTOOL-START
<sect1 id="add-func-cygwin-posix-path-list-p">
  <para>Rather than use a mode to say what the "proper" path list
  format is, we allow any, and give apps the tools they need to
  convert between the two.  If a ';' is present in the path list it's
  a Win32 path list.  Otherwise, if the first path begins with
  [letter]: (in which case it can be the only element since if it
  wasn't a ';' would be present) it's a Win32 path list.  Otherwise,
  it's a POSIX path list.</para>
</sect1>
DOCTOOL-END
  */

extern "C" int
cygwin_posix_path_list_p (const char *path)
{
  int posix_p = !(strchr (path, ';') || isdrive (path));
  return posix_p;
}

/* These are used for apps that need to convert env vars like PATH back and
   forth.  The conversion is a two step process.  First, an upper bound on the
   size of the buffer needed is computed.  Then the conversion is done.  This
   allows the caller to use alloca if it wants.  */

static int
conv_path_list_buf_size (const char *path_list, bool to_posix)
{
  int i, num_elms, max_mount_path_len, size;
  const char *p;

  path_conv pc(".", PC_POSIX);
  /* The theory is that an upper bound is
     current_size + (num_elms * max_mount_path_len)  */
  /* FIXME: This method is questionable in the long run. */

  unsigned nrel;
  char delim = to_posix ? ';' : ':';
  for (p = path_list, num_elms = nrel = 0; p; num_elms++)
    {
      if (!isabspath (p))
	nrel++;
      p = strchr (++p, delim);
    }

  /* 7: strlen ("//c") + slop, a conservative initial value */
  for (max_mount_path_len = sizeof ("/cygdrive/X"), i = 0;
       i < mount_table->nmounts; i++)
    {
      int mount_len = (to_posix
		       ? mount_table->mount[i].posix_pathlen
		       : mount_table->mount[i].native_pathlen);
      if (max_mount_path_len < mount_len)
	max_mount_path_len = mount_len;
    }

  /* 100: slop */
  size = strlen (path_list)
    + (num_elms * max_mount_path_len)
    + (nrel * strlen (to_posix ? pc.get_posix () : pc.get_win32 ()))
    + 100;

  return size;
}

extern "C" ssize_t
env_PATH_to_posix (const void *win32, void *posix, size_t size)
{
  return_with_errno (conv_path_list ((const char *) win32, (char *) posix,
				     size, ENV_CVT));
}

extern "C" ssize_t
cygwin_conv_path_list (cygwin_conv_path_t what, const void *from, void *to,
		       size_t size)
{
  int ret;
  char *winp = NULL;
  void *orig_to = NULL;
  tmp_pathbuf tp;

  switch (what & CCP_CONVTYPE_MASK)
    {
    case CCP_WIN_W_TO_POSIX:
      if (!sys_wcstombs_alloc (&winp, HEAP_NOTHEAP, (const wchar_t *) from,
			       (size_t) -1))
	return -1;
      what = (what & ~CCP_CONVTYPE_MASK) | CCP_WIN_A_TO_POSIX;
      from = (const void *) winp;
      break;
    case CCP_POSIX_TO_WIN_W:
      if (size == 0)
	return conv_path_list_buf_size ((const char *) from, 0)
	       * sizeof (WCHAR);
      what = (what & ~CCP_CONVTYPE_MASK) | CCP_POSIX_TO_WIN_A;
      orig_to = to;
      to = (void *) tp.w_get ();
      size = 65536;
      break;
    }
  switch (what & CCP_CONVTYPE_MASK)
    {
    case CCP_WIN_A_TO_POSIX:
    case CCP_POSIX_TO_WIN_A:
      if (size == 0)
	return conv_path_list_buf_size ((const char *) from,
					what == CCP_WIN_A_TO_POSIX);
      ret = conv_path_list ((const char *) from, (char *) to, size, what);
      /* Free winp buffer in case of CCP_WIN_W_TO_POSIX. */
      if (winp)
	free (winp);
      /* Convert to WCHAR in case of CCP_POSIX_TO_WIN_W. */
      if (orig_to)
	sys_mbstowcs ((wchar_t *) orig_to, size / sizeof (WCHAR),
		      (const char *) to, (size_t) -1);
      return_with_errno (ret);
      break;
    default:
      break;
    }
  set_errno (EINVAL);
  return -1;
}

/* cygwin_split_path: Split a path into directory and file name parts.
   Buffers DIR and FILE are assumed to be big enough.

   Examples (path -> `dir' / `file'):
   / -> `/' / `'
   "" -> `.' / `'
   . -> `.' / `.' (FIXME: should this be `.' / `'?)
   .. -> `.' / `..' (FIXME: should this be `..' / `'?)
   foo -> `.' / `foo'
   foo/bar -> `foo' / `bar'
   foo/bar/ -> `foo' / `bar'
   /foo -> `/' / `foo'
   /foo/bar -> `/foo' / `bar'
   c: -> `c:/' / `'
   c:/ -> `c:/' / `'
   c:foo -> `c:/' / `foo'
   c:/foo -> `c:/' / `foo'
 */

extern "C" void
cygwin_split_path (const char *path, char *dir, char *file)
{
  int dir_started_p = 0;

  /* Deal with drives.
     Remember that c:foo <==> c:/foo.  */
  if (isdrive (path))
    {
      *dir++ = *path++;
      *dir++ = *path++;
      *dir++ = '/';
      if (!*path)
	{
	  *dir = 0;
	  *file = 0;
	  return;
	}
      if (isdirsep (*path))
	++path;
      dir_started_p = 1;
    }

  /* Determine if there are trailing slashes and "delete" them if present.
     We pretend as if they don't exist.  */
  const char *end = path + strlen (path);
  /* path + 1: keep leading slash.  */
  while (end > path + 1 && isdirsep (end[-1]))
    --end;

  /* At this point, END points to one beyond the last character
     (with trailing slashes "deleted").  */

  /* Point LAST_SLASH at the last slash (duh...).  */
  const char *last_slash;
  for (last_slash = end - 1; last_slash >= path; --last_slash)
    if (isdirsep (*last_slash))
      break;

  if (last_slash == path)
    {
      *dir++ = '/';
      *dir = 0;
    }
  else if (last_slash > path)
    {
      memcpy (dir, path, last_slash - path);
      dir[last_slash - path] = 0;
    }
  else
    {
      if (dir_started_p)
	; /* nothing to do */
      else
	*dir++ = '.';
      *dir = 0;
    }

  memcpy (file, last_slash + 1, end - last_slash - 1);
  file[end - last_slash - 1] = 0;
}

/*****************************************************************************/

/* The find_fast_cwd_pointer function and parts of the
   cwdstuff::override_win32_cwd method are based on code using the
   following license:

   Copyright 2010 John Carey. All rights reserved.

   Redistribution and use in source and binary forms, with or without
   modification, are permitted provided that the following conditions
   are met:

      1. Redistributions of source code must retain the above
      copyright notice, this list of conditions and the following
      disclaimer.

      2. Redistributions in binary form must reproduce the above
      copyright notice, this list of conditions and the following
      disclaimer in the documentation and/or other materials provided
      with the distribution.

   THIS SOFTWARE IS PROVIDED BY JOHN CAREY ``AS IS'' AND ANY EXPRESS
   OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
   WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
   ARE DISCLAIMED. IN NO EVENT SHALL JOHN CAREY OR CONTRIBUTORS BE
   LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
   CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
   OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
   BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
   LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
   (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
   USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
   DAMAGE. */

void
fcwd_access_t::CopyPath (UNICODE_STRING &target)
{
  /* Copy the Path contents over into the UNICODE_STRING referenced by
     target.  This is used to set the CurrentDirectoryName in the
     user parameter block. */
  target = Path;
}

void
fcwd_access_t::Free (PVOID heap)
{
  /* Decrement the reference count.  If it's down to 0, free
     structure from heap. */
  if (InterlockedDecrement (&ReferenceCount) == 0)
    {
      /* The handle on init is always a fresh one, not the handle inherited
	 from the parent process.  We always have to close it here.
	 Note: The handle could be NULL, if we cd'ed into a virtual dir. */
      HANDLE h = DirectoryHandle;
      if (h)
	NtClose (h);
      RtlFreeHeap (heap, 0, this);
    }
}

void
fcwd_access_t::FillIn (HANDLE dir, PUNICODE_STRING name,
		       ULONG old_dismount_count)
{
  /* Fill in all values into this FAST_CWD structure. */
  DirectoryHandle = dir;
  ReferenceCount = 1;
  OldDismountCount = old_dismount_count;
  /* The fcwd structure stores the device characteristics of the
     volume holding the dir.  RtlGetCurrentDirectory_U checks
     if the FILE_REMOVABLE_MEDIA flag is set and, if so, checks if
     the volume is still the same as the one used when opening
     the directory handle.
     We don't call NtQueryVolumeInformationFile for the \\?\PIPE,
     though.  It just returns STATUS_INVALID_HANDLE anyway. */
  FSCharacteristics = 0;
  if (name != &ro_u_pipedir)
    {
      IO_STATUS_BLOCK io;
      FILE_FS_DEVICE_INFORMATION ffdi;
      if (NT_SUCCESS (NtQueryVolumeInformationFile (dir, &io, &ffdi,
		      sizeof ffdi, FileFsDeviceInformation)))
	FSCharacteristics = ffdi.Characteristics;
    }
  RtlInitEmptyUnicodeString (&Path, Buffer, name->MaximumLength);
  RtlCopyUnicodeString (&Path, name);
  if (Path.Buffer[Path.Length / sizeof (WCHAR) - 1] != L'\\')
    {
      Path.Buffer[Path.Length / sizeof (WCHAR)] = L'\\';
      Path.Length += sizeof (WCHAR);
    }
}

void
fcwd_access_t::SetDirHandleFromBufferPointer (PWCHAR buf_p, HANDLE dir)
{
  /* Input: The buffer pointer as it's stored in the user parameter block
     and a directory handle.
     This function computes the address to the FAST_CWD structure based
     on the version and overwrites the directory handle.  It is only
     used if we couldn't figure out the address of fast_cwd_ptr. */
  fcwd_access_t *f_cwd;
  f_cwd = (fcwd_access_t *)
	  ((PBYTE) buf_p - __builtin_offsetof (fcwd_access_t, Buffer));
  f_cwd->DirectoryHandle = dir;
}

/* This function scans the code in ntdll.dll to find the address of the
   global variable used to access the CWD.  While the pointer is global,
   it's not exported from the DLL, unfortunately.  Therefore we have to
   use some knowledge to figure out the address. */

#define peek32(x)	(*(int32_t *)(x))

static fcwd_access_t **
find_fast_cwd_pointer ()
{
  /* Fetch entry points of relevant functions in ntdll.dll. */
  HMODULE ntdll = GetModuleHandle ("ntdll.dll");
  if (!ntdll)
    return NULL;
  const uint8_t *get_dir = (const uint8_t *)
			   GetProcAddress (ntdll, "RtlGetCurrentDirectory_U");
  const uint8_t *ent_crit = (const uint8_t *)
			    GetProcAddress (ntdll, "RtlEnterCriticalSection");
  if (!get_dir || !ent_crit)
    return NULL;
  /* Search first relative call instruction in RtlGetCurrentDirectory_U. */
  const uint8_t *rcall = (const uint8_t *) memchr (get_dir, 0xe8, 80);
  if (!rcall)
    return NULL;
  /* Fetch offset from instruction and compute address of called function.
     This function actually fetches the current FAST_CWD instance and
     performs some other actions, not important to us. */
  const uint8_t *use_cwd = rcall + 5 + peek32 (rcall + 1);
  /* Next we search for the locking mechanism and perform a sanity check.
     On Pre-Windows 8 we basically look for the RtlEnterCriticalSection call.
     Windows 8 does not call RtlEnterCriticalSection.  The code manipulates
     the FastPebLock manually, probably because RtlEnterCriticalSection has
     been converted to an inline function.  Either way, we test if the code
     uses the FastPebLock. */
  const uint8_t *movrbx;
  const uint8_t *lock = (const uint8_t *)
                        memmem ((const char *) use_cwd, 80,
                                "\xf0\x0f\xba\x35", 4);
  if (lock)
    {
      /* The lock instruction tweaks the LockCount member, which is not at
	 the start of the PRTL_CRITICAL_SECTION structure.  So we have to
	 subtract the offset of LockCount to get the real address. */
      PRTL_CRITICAL_SECTION lockaddr =
        (PRTL_CRITICAL_SECTION) (lock + 9 + peek32 (lock + 4)
                                 - offsetof (RTL_CRITICAL_SECTION, LockCount));
      /* Test if lock address is FastPebLock. */
      if (lockaddr != NtCurrentTeb ()->Peb->FastPebLock)
        return NULL;
      /* Search `mov rel(%rip),%rbx'.  This is the instruction fetching the
         address of the current fcwd_access_t pointer, and it should be pretty
	 near to the locking stuff. */
      movrbx = (const uint8_t *) memmem ((const char *) lock, 40,
                                         "\x48\x8b\x1d", 3);
    }
  else
    {
      /* Usually the callq RtlEnterCriticalSection follows right after
	 fetching the lock address. */
      int call_rtl_offset = 7;
      /* Search `lea rel(%rip),%rcx'.  This loads the address of the lock into
         %rcx for the subsequent RtlEnterCriticalSection call. */
      lock = (const uint8_t *) memmem ((const char *) use_cwd, 80,
                                       "\x48\x8d\x0d", 3);
      if (!lock)
	{
	  /* Windows 8.1 Preview calls `lea rel(rip),%r12' then some unrelated
	     or, then `mov %r12,%rcx', then `callq RtlEnterCriticalSection'. */
	  lock = (const uint8_t *) memmem ((const char *) use_cwd, 80,
					   "\x4c\x8d\x25", 3);
	  if (!lock)
	    return NULL;
	  call_rtl_offset = 14;
	}
      PRTL_CRITICAL_SECTION lockaddr =
        (PRTL_CRITICAL_SECTION) (lock + 7 + peek32 (lock + 3));
      /* Test if lock address is FastPebLock. */
      if (lockaddr != NtCurrentTeb ()->Peb->FastPebLock)
        return NULL;
      /* Next is the `callq RtlEnterCriticalSection'. */
      lock += call_rtl_offset;
      if (lock[0] != 0xe8)
        return NULL;
      const uint8_t *call_addr = (const uint8_t *)
                                 (lock + 5 + peek32 (lock + 1));
      if (call_addr != ent_crit)
        return NULL;
      /* In contrast to the above Windows 8 code, we don't have to search
	 for the `mov rel(%rip),%rbx' instruction.  It follows right after
	 the call to RtlEnterCriticalSection. */
      movrbx = lock + 5;
    }
  if (!movrbx)
    return NULL;
  /* Check that the next instruction tests if the fetched value is NULL. */
  const uint8_t *testrbx = (const uint8_t *)
			   memmem (movrbx + 7, 3, "\x48\x85\xdb", 3);
  if (!testrbx)
    return NULL;
  /* Compute address of the fcwd_access_t ** pointer. */
  return (fcwd_access_t **) (testrbx + peek32 (movrbx + 3));
}

static fcwd_access_t **
find_fast_cwd ()
{
  /* Fetch the pointer but don't set the global fast_cwd_ptr yet.  First
     we have to make sure we know the version of the FAST_CWD structure
     used on the system. */
  fcwd_access_t **f_cwd_ptr = find_fast_cwd_pointer ();
  if (!f_cwd_ptr)
    {
      bool warn = 1;
      USHORT emulated, hosted;

      /* Check if we're running in WOW64 on ARM64 emulating AMD64.  Skip
	 warning as long as there's no solution for finding the FAST_CWD
	 pointer on that system. */
      if (IsWow64Process2 (GetCurrentProcess (), &emulated, &hosted)
	  && hosted == IMAGE_FILE_MACHINE_ARM64)
	warn = 0;

      if (warn)
	small_printf ("Cygwin WARNING:\n"
"  Couldn't compute FAST_CWD pointer.  This typically occurs if you're using\n"
"  an older Cygwin version on a newer Windows.  Please update to the latest\n"
"  available Cygwin version from https://cygwin.com/.  If the problem persists,\n"
"  please see https://cygwin.com/problems.html\n\n");
    }
  /* Eventually, after we set the version as well, set fast_cwd_ptr. */
  return f_cwd_ptr;
}

void
cwdstuff::override_win32_cwd (bool init, ULONG old_dismount_count)
{
  HANDLE h = NULL;

  PEB &peb = *NtCurrentTeb ()->Peb;
  UNICODE_STRING &upp_cwd_str = peb.ProcessParameters->CurrentDirectoryName;
  HANDLE &upp_cwd_hdl = peb.ProcessParameters->CurrentDirectoryHandle;
  PUNICODE_STRING win32_cwd_ptr = error ? &ro_u_pipedir : &win32;

  if (fast_cwd_ptr == (fcwd_access_t **) -1)
    fast_cwd_ptr = find_fast_cwd ();
  if (fast_cwd_ptr)
    {
      /* If we got a valid value for fast_cwd_ptr, we can simply replace
	 the RtlSetCurrentDirectory_U function entirely. */
      PVOID heap = peb.ProcessHeap;
      /* First allocate a new fcwd_access_t structure on the heap. */
      fcwd_access_t *f_cwd = (fcwd_access_t *)
			RtlAllocateHeap (heap, 0,
					 sizeof (fcwd_access_t)
					 + win32_cwd_ptr->MaximumLength);
      if (!f_cwd)
	{
	  debug_printf ("RtlAllocateHeap failed");
	  return;
	}
      /* Fill in the values. */
      f_cwd->FillIn (dir, win32_cwd_ptr, old_dismount_count);
      /* Use PEB lock when switching fast_cwd_ptr to the new FAST_CWD
	 structure and writing the CWD to the user process parameter
	 block.  This is equivalent to calling RtlAcquirePebLock/
	 RtlReleasePebLock, but without having to go through the FS
	 selector again. */
      RtlEnterCriticalSection (peb.FastPebLock);
      fcwd_access_t *old_cwd = *fast_cwd_ptr;
      *fast_cwd_ptr = f_cwd;
      f_cwd->CopyPath (upp_cwd_str);
      upp_cwd_hdl = dir;
      RtlLeaveCriticalSection (peb.FastPebLock);
      if (old_cwd)
	old_cwd->Free (heap);
    }
  else
    {
      /* Fallback if we failed to find the fast_cwd_ptr value:

	 - Call RtlSetCurrentDirectory_U.
	 - Compute new FAST_CWD struct address from buffer pointer in the
	   user process parameter block.
	 - Replace the directory handle in the struct with our own handle.
	 - Close the original handle.  RtlSetCurrentDirectory_U already
	   closed our former dir handle -> no handle leak.

	 Guard the entire operation with FastPebLock to avoid races
	 accessing the PEB and FAST_CWD struct.

	 Unfortunately this method is still prone to a directory usage
	 race condition:

	 - The directory is locked against deletion or renaming between the
	   RtlSetCurrentDirectory_U and the subsequent NtClose call. */
      if (unlikely (upp_cwd_hdl == NULL) && init)
	return;
      RtlEnterCriticalSection (peb.FastPebLock);
      if (!init)
	{
	  NTSTATUS status =
	    RtlSetCurrentDirectory_U (win32_cwd_ptr);
	  if (!NT_SUCCESS (status))
	    {
	      RtlLeaveCriticalSection (peb.FastPebLock);
	      debug_printf ("RtlSetCurrentDirectory_U(%S) failed, %y",
			    win32_cwd_ptr);
	      return;
	    }
	}
      fcwd_access_t::SetDirHandleFromBufferPointer(upp_cwd_str.Buffer, dir);
      h = upp_cwd_hdl;
      upp_cwd_hdl = dir;
      RtlLeaveCriticalSection (peb.FastPebLock);
      /* The handle on init is always a fresh one, not the handle inherited
	 from the parent process.  We always have to close it here. */
      NtClose (h);
    }
}

/* Initialize cwdstuff */
void
cwdstuff::init ()
{
  /* Cygwin processes inherit the cwd from their parent.  If the win32 path
     buffer is not NULL, the cwd struct is already set up, and we only
     have to override the Win32 CWD with ours. */
  if (win32.Buffer)
    override_win32_cwd (true, SharedUserData.DismountCount);
  else
    {
      /* Initialize fast_cwd stuff. */
      fast_cwd_ptr = (fcwd_access_t **) -1;
      /* Initially re-open the cwd to allow POSIX semantics. */
      set (NULL, NULL);
    }
}

/* Chdir and fill out the elements of a cwdstuff struct. */
int
cwdstuff::set (path_conv *nat_cwd, const char *posix_cwd)
{
  NTSTATUS status;
  UNICODE_STRING upath;
  OBJECT_ATTRIBUTES attr;
  PEB &peb = *NtCurrentTeb ()->Peb;
  bool virtual_path = false;
  bool unc_path = false;
  bool inaccessible_path = false;

  /* Here are the problems with using SetCurrentDirectory.  Just skip this
     comment if you don't like whining.

     - SetCurrentDirectory only supports paths of up to MAX_PATH - 1 chars,
       including a trailing backslash.  That's an absolute restriction, even
       in the UNICODE API.

     - SetCurrentDirectory fails for directories with strict permissions even
       for processes with the SE_BACKUP_NAME privilege enabled.  The reason
       is apparently that SetCurrentDirectory calls NtOpenFile without the
       FILE_OPEN_FOR_BACKUP_INTENT flag set.

     - SetCurrentDirectory does not support case-sensitivity.

     - Unlinking a cwd fails because SetCurrentDirectory seems to open
       directories so that deleting the directory is disallowed.

     - SetCurrentDirectory can naturally not work on virtual Cygwin paths
       like /proc or /cygdrive.

     Nevertheless, doing entirely without SetCurrentDirectory is not really
     feasible, because it breaks too many mixed applications using the Win32
     API.

     Therefore we handle the CWD all by ourselves and just keep the Win32
     CWD in sync.  However, to avoid surprising behaviour in the Win32 API
     when we are in a CWD which is inaccessible as Win32 CWD, we set the
     Win32 CWD to a "weird" directory in which all relative filesystem-related
     calls fail. */

  if (nat_cwd)
    {
      upath = *nat_cwd->get_nt_native_path ();
      if (nat_cwd->isspecial ())
	{
	  virtual_path = true;
	  /* But allow starting of native apps from /dev if /dev actually
	     exists on disk. */
	  if (isdev_dev (nat_cwd->dev))
	    {
	      FILE_BASIC_INFORMATION fbi;

	      InitializeObjectAttributes (&attr, &upath,
					  OBJ_CASE_INSENSITIVE | OBJ_INHERIT,
					  NULL, NULL);
	      status = NtQueryAttributesFile (&attr, &fbi);
	      if (status != STATUS_OBJECT_NAME_NOT_FOUND
		  && status != STATUS_OBJECT_PATH_NOT_FOUND)
		virtual_path = false;
	    }
	}
    }

  acquire_write ();

  /* Memorize old DismountCount before opening the dir.  This value is
     stored in the FAST_CWD structure.  It would be simpler to fetch the
     old DismountCount in override_win32_cwd, but Windows also fetches
     it before opening the directory handle.  It's not quite clear if
     that's really required, but since we don't know the side effects of
     this action, we better follow Windows' lead. */
  ULONG old_dismount_count = SharedUserData.DismountCount;
  /* Open a directory handle with FILE_OPEN_FOR_BACKUP_INTENT and with all
     sharing flags set.  The handle is right now used in exceptions.cc only,
     but that might change in future. */
  HANDLE h = NULL;
  if (!virtual_path)
    {
      IO_STATUS_BLOCK io;

      if (!nat_cwd)
	{
	  /* On init, just reopen Win32 CWD with desired access flags.
	     We can access the PEB without lock, because no other thread
	     can change the CWD.  However, there's a chance that the handle
	     is NULL, even though CurrentDirectoryName isn't so we have to
	     be careful. */
	  if (!peb.ProcessParameters->CurrentDirectoryHandle)
	    {
	      InitializeObjectAttributes (&attr,
			    &peb.ProcessParameters->CurrentDirectoryName,
			    OBJ_CASE_INSENSITIVE | OBJ_INHERIT, NULL, NULL);
	    }
	  else
	    {
	      RtlInitUnicodeString (&upath, L"");
	      InitializeObjectAttributes (&attr,
			    &upath, OBJ_CASE_INSENSITIVE | OBJ_INHERIT,
			    peb.ProcessParameters->CurrentDirectoryHandle,
			    NULL);
	    }
	}
      else
	InitializeObjectAttributes (&attr, &upath,
			nat_cwd->objcaseinsensitive () | OBJ_INHERIT,
			NULL, NULL);
      /* First try without FILE_OPEN_FOR_BACKUP_INTENT, to find out if the
	 directory is valid for Win32 apps.  And, no, we can't just call
	 SetCurrentDirectory here, since that would potentially break
	 case-sensitivity. */
      status = NtOpenFile (&h, SYNCHRONIZE | FILE_TRAVERSE, &attr, &io,
			   FILE_SHARE_VALID_FLAGS,
			   FILE_DIRECTORY_FILE
			   | FILE_SYNCHRONOUS_IO_NONALERT);
      if (status == STATUS_ACCESS_DENIED)
	{
	  status = NtOpenFile (&h, SYNCHRONIZE | FILE_TRAVERSE, &attr, &io,
			       FILE_SHARE_VALID_FLAGS,
			       FILE_DIRECTORY_FILE
			       | FILE_SYNCHRONOUS_IO_NONALERT
			       | FILE_OPEN_FOR_BACKUP_INTENT);
	  inaccessible_path = true;
	}
      if (!NT_SUCCESS (status))
	{
	  /* Called from chdir?  Just fail. */
	  if (nat_cwd)
	    {
	      release_write ();
	      __seterrno_from_nt_status (status);
	      return -1;
	    }
	  /* Otherwise we're in init and posix hasn't been set yet.  Try to
	     duplicate the handle instead.  If that fails, too, set dir to NULL
	     and carry on.  This will at least set posix to some valid path at
	     process startup, and subsequent getcwd calls don't EFAULT. */
	  debug_printf ("WARNING: Can't reopen CWD %y '%S', status %y",
			peb.ProcessParameters->CurrentDirectoryHandle,
			&peb.ProcessParameters->CurrentDirectoryName,
			status);
	  if (!peb.ProcessParameters->CurrentDirectoryHandle
	      || !DuplicateHandle (GetCurrentProcess (),
			peb.ProcessParameters->CurrentDirectoryHandle,
			GetCurrentProcess (), &h, 0, TRUE, 0))
	    {
	      release_write ();
	      if (peb.ProcessParameters->CurrentDirectoryHandle)
		debug_printf ("...and DuplicateHandle failed with %E.");
	      dir = NULL;
	    }
	}
    }
  /* Set new handle.  Note that we simply overwrite the old handle here
     without closing it.  The handle is also used as Win32 CWD handle in
     the user parameter block, and it will be closed in override_win32_cwd,
     if required. */
  dir = h;

  if (!nat_cwd)
    {
      /* On init, just fetch the Win32 dir from the PEB.  We can access
	 the PEB without lock, because no other thread can change the CWD
	 at that time. */
      PUNICODE_STRING pdir = &peb.ProcessParameters->CurrentDirectoryName;
      RtlInitEmptyUnicodeString (&win32,
				 (PWCHAR) crealloc_abort (win32.Buffer,
							  pdir->Length
							  + sizeof (WCHAR)),
				 pdir->Length + sizeof (WCHAR));
      RtlCopyUnicodeString (&win32, pdir);

      PWSTR eoBuffer = win32.Buffer + (win32.Length / sizeof (WCHAR));
      /* Remove trailing slash if one exists. */
      if ((eoBuffer - win32.Buffer) > 3 && eoBuffer[-1] == L'\\')
	win32.Length -= sizeof (WCHAR);
      if (eoBuffer[0] == L'\\')
	unc_path = true;

      posix_cwd = NULL;
    }
  else
    {
      if (!virtual_path) /* don't mangle virtual path. */
	{
	  /* Convert into Win32 path and compute length. */
	  if (upath.Buffer[1] == L'?')
	    {
	      upath.Buffer += 4;
	      upath.Length -= 4 * sizeof (WCHAR);
	      if (upath.Buffer[1] != L':')
		{
		  /* UNC path */
		  upath.Buffer += 2;
		  upath.Length -= 2 * sizeof (WCHAR);
		  unc_path = true;
		}
	    }
	  else
	    {
	      /* Path via native NT namespace.  Prepend GLOBALROOT prefix
		 to create a valid Win32 path. */
	      PWCHAR buf = (PWCHAR) alloca (upath.Length
					    + ro_u_globalroot.Length
					    + sizeof (WCHAR));
	      wcpcpy (wcpcpy (buf, ro_u_globalroot.Buffer), upath.Buffer);
	      upath.Buffer = buf;
	      upath.Length += ro_u_globalroot.Length;
	    }
	  PWSTR eoBuffer = upath.Buffer + (upath.Length / sizeof (WCHAR));
	  /* Remove trailing slash if one exists. */
	  if ((eoBuffer - upath.Buffer) > 3 && eoBuffer[-1] == L'\\')
	    upath.Length -= sizeof (WCHAR);
	}
      RtlInitEmptyUnicodeString (&win32,
				 (PWCHAR) crealloc_abort (win32.Buffer,
							  upath.Length
							  + sizeof (WCHAR)),
				 upath.Length + sizeof (WCHAR));
      RtlCopyUnicodeString (&win32, &upath);
      if (unc_path)
	win32.Buffer[0] = L'\\';
    }
  /* Make sure it's NUL-terminated. */
  win32.Buffer[win32.Length / sizeof (WCHAR)] = L'\0';

  /* Set drive_length, used in path conversion, and error code, used in
     spawn_guts to decide whether a native Win32 app can be started or not. */
  if (virtual_path)
    {
      drive_length = 0;
      error = ENOTDIR;
    }
  else
    {
      if (!unc_path)
	drive_length = 2;
      else
	{
	  PWCHAR ptr = wcschr (win32.Buffer + 2, L'\\');
	  if (ptr)
	    ptr = wcschr (ptr + 1, L'\\');
	  if (ptr)
	    drive_length = ptr - win32.Buffer;
	  else
	    drive_length = win32.Length / sizeof (WCHAR);
	}
      if (inaccessible_path)
	error = EACCES;
      else if (win32.Length > (MAX_PATH - 2) * sizeof (WCHAR))
	error = ENAMETOOLONG;
      else
	error = 0;
    }
  /* Keep the Win32 CWD in sync.  Don't check for error, other than for
     strace output.  Try to keep overhead low. */
  override_win32_cwd (!nat_cwd, old_dismount_count);

  /* Eventually, create POSIX path if it's not set on entry. */
  tmp_pathbuf tp;
  if (!posix_cwd)
    {
      posix_cwd = (const char *) tp.c_get ();
      mount_table->conv_to_posix_path (win32.Buffer, (char *) posix_cwd, 0);
    }
  posix = (char *) crealloc_abort (posix, strlen (posix_cwd) + 1);
  stpcpy (posix, posix_cwd);

  release_write ();
  return 0;
}

const char *
cwdstuff::get_error_desc () const
{
  switch (cygheap->cwd.get_error ())
    {
    case EACCES:
      return "has restricted permissions which render it\n"
	     "inaccessible as Win32 working directory";
    case ENOTDIR:
      return "is a virtual Cygwin directory which does\n"
	     "not exist for a native Windows application";
    case ENAMETOOLONG:
      return "has a path longer than allowed for a\n"
	     "Win32 working directory";
    default:
      break;
    }
  /* That shouldn't occur, unless we defined a new error code
     in cwdstuff::set. */
  return "is not accessible for some unknown reason";
}

/* Store incoming wchar_t path as current posix cwd.  This is called from
   setlocale so that the cwd is always stored in the right charset. */
void
cwdstuff::reset_posix (wchar_t *w_cwd)
{
  size_t len = sys_wcstombs (NULL, (size_t) -1, w_cwd);
  posix = (char *) crealloc_abort (posix, len + 1);
  sys_wcstombs (posix, len + 1, w_cwd);
}

char *
cwdstuff::get (char *buf, int need_posix, int with_chroot, unsigned ulen)
{
  tmp_pathbuf tp;

  errno = 0;
  if (ulen)
    /* nothing */;
  else if (buf == NULL)
    ulen = (unsigned) -1;
  else
    {
      set_errno (EINVAL);
      goto out;
    }

  acquire_read ();

  char *tocopy;
  if (!need_posix)
    {
      tocopy = tp.c_get ();
      sys_wcstombs (tocopy, NT_MAX_PATH, win32.Buffer,
		    win32.Length / sizeof (WCHAR));
    }
  else
    tocopy = posix;

  debug_printf ("posix %s", posix);
  if (strlen (tocopy) >= ulen)
    {
      set_errno (ERANGE);
      buf = NULL;
    }
  else
    {
      if (!buf)
	buf = (char *) malloc (strlen (tocopy) + 1);
      strcpy (buf, tocopy);
      if (!buf[0])	/* Should only happen when chroot */
	strcpy (buf, "/");
    }

  release_read ();

out:
  syscall_printf ("(%s) = cwdstuff::get (%p, %u, %d, %d), errno %d",
		  buf, buf, ulen, need_posix, with_chroot, errno);
  return buf;
}

/* No need to be reentrant or thread-safe according to SUSv3.
   / and \\ are treated equally.  Leading drive specifiers are
   kept intact as far as it makes sense.  Everything else is
   POSIX compatible. */
extern "C" char *
basename (char *path)
{
  static char buf[4];
  char *c, *d, *bs = path;

  if (!path || !*path)
    return strcpy (buf, ".");
  if (isalpha (path[0]) && path[1] == ':')
    bs += 2;
  else if (strspn (path, "/\\") > 1)
    ++bs;
  c = strrchr (bs, '/');
  if ((d = strrchr (c ?: bs, '\\')) > c)
    c = d;
  if (c)
    {
      /* Trailing (back)slashes are eliminated. */
      while (c && c > bs && c[1] == '\0')
	{
	  *c = '\0';
	  c = strrchr (bs, '/');
	  if ((d = strrchr (c ?: bs, '\\')) > c)
	    c = d;
	}
      if (c && (c > bs || c[1]))
	return c + 1;
    }
  else if (!bs[0])
    {
      stpncpy (buf, path, bs - path);
      stpcpy (buf + (bs - path), ".");
      return buf;
    }
  return path;
}

/* The differences with the POSIX version above:
   - declared in <string.h> (instead of <libgen.h>);
   - the argument is never modified, and therefore is marked const;
   - the empty string is returned if path is an empty string, "/", or ends
     with a trailing slash. */
extern "C" char *
__gnu_basename (const char *path)
{
  static char buf[1];
  char *c, *d, *bs = (char *)path;

  if (!path || !*path)
    return strcpy (buf, "");
  if (isalpha (path[0]) && path[1] == ':')
    bs += 2;
  else if (strspn (path, "/\\") > 1)
    ++bs;
  c = strrchr (bs, '/');
  if ((d = strrchr (c ?: bs, '\\')) > c)
    c = d;
  if (c)
    return c + 1;
  else if (!bs[0])
    return strcpy (buf, "");
  return (char *)path;
}

/* No need to be reentrant or thread-safe according to SUSv3.
   / and \\ are treated equally.  Leading drive specifiers and
   leading double (back)slashes are kept intact as far as it
   makes sense.  Everything else is POSIX compatible. */
extern "C" char *
dirname (char *path)
{
  static char buf[4];
  char *c, *d, *bs = path;

  if (!path || !*path)
    return strcpy (buf, ".");
  if (isalpha (path[0]) && path[1] == ':')
    bs += 2;
  else if (strspn (path, "/\\") > 1)
    ++bs;
  c = strrchr (bs, '/');
  if ((d = strrchr (c ?: bs, '\\')) > c)
    c = d;
  if (c)
    {
      /* Trailing (back)slashes are eliminated. */
      while (c && c > bs && c[1] == '\0')
	{
	  *c = '\0';
	  c = strrchr (bs, '/');
	  if ((d = strrchr (c ?: bs, '\\')) > c)
	    c = d;
	}
      if (!c)
	strcpy (bs, ".");
      else if (c > bs)
	{
	  /* More trailing (back)slashes are eliminated. */
	  while (c > bs && (*c == '/' || *c == '\\'))
	    *c-- = '\0';
	}
      else
	c[1] = '\0';
    }
  else
    {
      stpncpy (buf, path, bs - path);
      stpcpy (buf + (bs - path), ".");
      return buf;
    }
  return path;
}
