/* path.h

This file is part of Cygwin.

This software is a copyrighted work licensed under the terms of the
Cygwin license.  Please consult the file "CYGWIN_LICENSE" for
details. */

#ifndef _PATH_H_
#define _PATH_H_

struct mnt_t
{
  char *native;
  char *posix;
  unsigned flags;
};

char *cygpath (const char *s, ...);
char *cygpath_rel (const char *cwd, const char *s, ...);
bool is_exe (HANDLE);
bool is_symlink (HANDLE);
bool readlink (HANDLE, char *, size_t);
int get_word (HANDLE, int);
int get_dword (HANDLE, int);
bool from_fstab_line (mnt_t *m, char *line, bool user);

extern mnt_t mount_table[255];
extern int max_mount_entry;

#ifndef SYMLINK_MAX
#define SYMLINK_MAX 4095  /* PATH_MAX - 1 */
#endif

DWORD testsuite_getcwd (DWORD nBufferLength, LPSTR lpBuffer);
void testsuite_read_mounts (void);

#endif
