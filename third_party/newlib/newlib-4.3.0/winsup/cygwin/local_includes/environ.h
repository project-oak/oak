/* environ.h: Declarations for environ manipulation

This file is part of Cygwin.

This software is a copyrighted work licensed under the terms of the
Cygwin license.  Please consult the file "CYGWIN_LICENSE" for
details. */

/* Initialize the environment */
void environ_init (char **, int);

/* The structure below is used to control conversion to/from posix-style
   file specs.  Currently, only PATH and HOME are converted, but PATH
   needs to use a "convert path list" function while HOME needs a simple
   "convert to posix/win32".  */
struct win_env
  {
    const char *name;
    size_t namelen;
    char *posix;
    char *native;
    ssize_t (*toposix) (const void *, void *, size_t);
    ssize_t (*towin32) (const void *, void *, size_t);
    bool immediate;
    void add_cache (const char *in_posix, const char *in_native = NULL);
    const char * get_native () const {return native ? native + namelen : NULL;}
    const char * get_posix () const {return posix ? posix : NULL;}
    struct win_env& operator = (struct win_env& x);
    void reset () {native = posix = NULL;}
    ~win_env ();
  };

win_env *getwinenv (const char *name, const char *posix = NULL, win_env * = NULL);
char *getwinenveq (const char *name, size_t len, int);

char **build_env (const char * const *envp, PWCHAR &envblock,
			  int &envc, bool need_envblock, HANDLE new_token);

char **win32env_to_cygenv (PWCHAR rawenv, bool posify);

#define ENV_CVT -1
