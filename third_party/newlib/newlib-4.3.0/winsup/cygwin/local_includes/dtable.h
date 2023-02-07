/* dtable.h: fd table definition.

This file is part of Cygwin.

This software is a copyrighted work licensed under the terms of the
Cygwin license.  Please consult the file "CYGWIN_LICENSE" for
details. */

#pragma once

/* Initial and increment values for cygwin's fd table */
#define NOFILE_INCR    32

#include "thread.h"
#include "sync.h"

class suffix_info;

#define BFH_OPTS (PC_NULLEMPTY | PC_FULL | PC_POSIX)
class dtable
{
  fhandler_base **fds;
  fhandler_base **archetypes;
  unsigned narchetypes;
  unsigned farchetype;
  static const int initial_archetype_size = 8;
  size_t first_fd_for_open;
  int cnt_need_fixup_before;
public:
  size_t size;

  dtable () : archetypes (NULL), narchetypes (0), farchetype (0), first_fd_for_open(3), cnt_need_fixup_before(0) {}
  void init () {first_fd_for_open = 3;}

  void dec_need_fixup_before ()
    { if (cnt_need_fixup_before > 0) --cnt_need_fixup_before; }
  void inc_need_fixup_before ()
    { cnt_need_fixup_before++; }
  bool need_fixup_before ()
    { return cnt_need_fixup_before > 0; }

  void move_fd (int, int);
  int vfork_child_dup ();
  void vfork_parent_restore ();
  void vfork_child_fixup ();
  fhandler_base *dup_worker (fhandler_base *oldfh, int flags);
  int extend (size_t, size_t);
  void fixup_after_fork (HANDLE);
  void fixup_close (size_t, fhandler_base *);

  inline int not_open (int fd)
  {
    lock ();
    int res = fd < 0 || fd >= (int) size || fds[fd] == NULL;
    unlock ();
    return res;
  }
  int find_unused_handle (size_t start);
  int find_unused_handle () { return find_unused_handle (first_fd_for_open);}
  void release (int fd);
  void init_std_file_from_handle (int fd, HANDLE handle);
  int dup3 (int oldfd, int newfd, int flags);
  void fixup_after_exec ();
  inline fhandler_base *&operator [](int fd) const { return fds[fd]; }
  bool select_read (int fd, select_stuff *);
  bool select_write (int fd, select_stuff *);
  bool select_except (int fd, select_stuff *);
  operator fhandler_base **() {return fds;}
  void stdio_init ();
  void get_debugger_info ();
  void set_file_pointers_for_exec ();
  fhandler_base *find_archetype (device& dev);
  fhandler_base **add_archetype ();
  void delete_archetype (fhandler_base *);
  void fixup_before_exec (DWORD win_proc_id);
  void fixup_before_fork (DWORD win_proc_id);
  void lock () {lock_process::locker.acquire ();}
  void unlock () {lock_process::locker.release ();}
};

fhandler_base *build_fh_dev (const device&, const char * = NULL);
fhandler_base *build_fh_name (const char *, unsigned = 0, suffix_info * = NULL);
fhandler_base *build_fh_pc (path_conv& pc);

void dtable_init ();
void stdio_init ();
extern dtable fdtab;

extern "C" int getfdtabsize ();
extern "C" void setfdtabsize (int);
