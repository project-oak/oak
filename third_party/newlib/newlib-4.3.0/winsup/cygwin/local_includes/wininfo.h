/* wininfo.h: main Cygwin header file.

This file is part of Cygwin.

This software is a copyrighted work licensed under the terms of the
Cygwin license.  Please consult the file "CYGWIN_LICENSE" for
details. */

class muto;
class wininfo
{
  HWND hwnd;
  static muto _lock;
public:
  operator HWND ();
  int process (HWND, UINT, WPARAM, LPARAM);
  void lock ();
  void release ();
  DWORD winthread ();
};

extern wininfo winmsg;
