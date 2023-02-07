/* crt0.h: header file for crt0.

This file is part of Cygwin.

This software is a copyrighted work licensed under the terms of the
Cygwin license.  Please consult the file "CYGWIN_LICENSE" for
details. */

#ifdef __cplusplus
extern "C" {
#endif

#include "winlean.h"
struct per_process;
typedef int (*MainFunc) (int argc, char *argv[], char **env);
int _cygwin_crt0_common (MainFunc, struct per_process *);
PVOID dll_dllcrt0 (HMODULE, struct per_process *);

#ifdef __cplusplus
}
#endif
