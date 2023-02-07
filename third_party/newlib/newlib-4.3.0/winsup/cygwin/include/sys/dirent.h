/* Posix dirent.h for WIN32.

   This software is a copyrighted work licensed under the terms of the
   Cygwin license.  Please consult the file "CYGWIN_LICENSE" for
   details. */

/* Including this file should not require any Windows headers.  */

#ifndef _SYS_DIRENT_H
#define _SYS_DIRENT_H

#include <sys/cdefs.h>
#include <sys/types.h>
#include <limits.h>

#define __DIRENT_VERSION	2

#define _DIRENT_HAVE_D_TYPE
struct dirent
{
  uint32_t __d_version;			/* Used internally */
  ino_t d_ino;
  unsigned char d_type;
  unsigned char __d_unused1[3];
  __uint32_t __d_internal1;
  char d_name[NAME_MAX + 1];
};

#define d_fileno d_ino			/* BSD compatible definition */

#define __DIRENT_COOKIE 0xcdcd8484

typedef struct __DIR
{
  /* This is first to set alignment in non _LIBC case.  */
  unsigned long __d_cookie;
  struct dirent *__d_dirent;
  char *__d_dirname;			/* directory name with trailing '*' */
  __int32_t __d_position;			/* used by telldir/seekdir */
  int __d_fd;
  uintptr_t __d_internal;
  void *__handle;
  void *__fh;
  unsigned __flags;
} DIR;

#if __BSD_VISIBLE
#ifdef _DIRENT_HAVE_D_TYPE
/* File types for `d_type'.  */
enum
{
  DT_UNKNOWN = 0,
# define DT_UNKNOWN     DT_UNKNOWN
  DT_FIFO = 1,
# define DT_FIFO        DT_FIFO
  DT_CHR = 2,
# define DT_CHR         DT_CHR
  DT_DIR = 4,
# define DT_DIR         DT_DIR
  DT_BLK = 6,
# define DT_BLK         DT_BLK
  DT_REG = 8,
# define DT_REG         DT_REG
  DT_LNK = 10,
# define DT_LNK         DT_LNK
  DT_SOCK = 12,
# define DT_SOCK        DT_SOCK
  DT_WHT = 14
# define DT_WHT         DT_WHT
};

/* Convert between stat structure types and directory types.  */
# define IFTODT(mode)		(((mode) & 0170000) >> 12)
# define DTTOIF(dirtype)        ((dirtype) << 12)
#endif /* _DIRENT_HAVE_D_TYPE */
#endif /* __BSD_VISIBLE */
#endif /*_SYS_DIRENT_H*/
