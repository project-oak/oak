/* stdlib.h

This file is part of Cygwin.

This software is a copyrighted work licensed under the terms of the
Cygwin license.  Please consult the file "CYGWIN_LICENSE" for
details. */

#ifndef _CYGWIN_STDLIB_H
#define _CYGWIN_STDLIB_H

#include <sys/cdefs.h>
#include <cygwin/wait.h>

#ifdef __cplusplus
extern "C"
{
#endif

const char *getprogname (void);
void	setprogname (const char *);

#if __GNU_VISIBLE
char *canonicalize_file_name (const char *);
#endif
#if __BSD_VISIBLE || __POSIX_VISIBLE >= 200112
int unsetenv (const char *);
#endif
#if __MISC_VISIBLE
int clearenv (void);
#endif
#if __XSI_VISIBLE
char *ptsname (int);
int grantpt (int);
int unlockpt (int);
#endif
#if __GNU_VISIBLE
int ptsname_r(int, char *, size_t);
int getpt (void);
#endif

#if __XSI_VISIBLE >= 600
int posix_openpt (int);
#endif

#ifdef _LIBC
#define unsetenv UNUSED_unsetenv
#define _unsetenv_r UNUSED__unsetenv_r
#endif

extern void *memalign (size_t, size_t);
#if __BSD_VISIBLE || (__XSI_VISIBLE >= 4 && __POSIX_VISIBLE < 200112)
extern void *valloc (size_t);
#endif

#undef _malloc_r
#define _malloc_r(r, s) malloc (s)
#undef _free_r
#define _free_r(r, p) free (p)
#undef _realloc_r
#define _realloc_r(r, p, s) realloc (p, s)
#undef _calloc_r
#define _calloc_r(r, s1, s2) calloc (s1, s2);
#undef _memalign_r
#define _memalign_r(r, s1, s2) memalign (s1, s2);
#undef _mallinfo_r
#define _mallinfo_r(r) mallinfo ()
#undef _malloc_stats_r
#define _malloc_stats_r(r) malloc_stats ()
#undef _mallopt_r
#define _mallopt_r(i1, i2) mallopt (i1, i2)
#undef _malloc_usable_size_r
#define _malloc_usable_size_r(r, p) malloc_usable_size (p)
#undef _valloc_r
#define _valloc_r(r, s) valloc (s)
#undef _pvalloc_r
#define _pvalloc_r(r, s) pvalloc (s)
#undef _malloc_trim_r
#define _malloc_trim_r(r, s) malloc_trim (s)
#undef _mstats_r
#define _mstats_r(r, p) mstats (p)

#if __BSD_VISIBLE
int getloadavg(double loadavg[], int nelem);
#endif

#ifdef __cplusplus
}
#endif
#endif /*_CYGWIN_STDLIB_H*/
