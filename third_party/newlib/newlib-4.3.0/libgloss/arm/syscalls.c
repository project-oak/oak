/* Support files for GNU libc.  Files in the system namespace go here.
   Files in the C namespace (ie those that do not start with an
   underscore) go in .c.  */

#include <_ansi.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/fcntl.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <sys/time.h>
#include <sys/times.h>
#include <errno.h>
#include <reent.h>
#include <unistd.h>
#include <sys/wait.h>
#include "swi.h"

/* Forward prototypes.  */
int	_system		(const char *);
int	_rename		(const char *, const char *);
int	_isatty		(int);
clock_t _times		(struct tms *);
int	_gettimeofday	(struct timeval *, void *);
int	_unlink		(const char *);
int	_link		(const char *, const char *);
int	_stat		(const char *, struct stat *);
int	_fstat		(int, struct stat *);
int	_swistat	(int fd, struct stat * st);
void *	_sbrk		(ptrdiff_t);
pid_t	_getpid		(void);
int	_close		(int);
clock_t	_clock		(void);
int	_swiclose	(int);
int	_open		(const char *, int, ...);
int	_swiopen	(const char *, int);
int	_write		(int, const void *, size_t);
int	_swiwrite	(int, const void *, size_t);
_off_t	_lseek		(int, _off_t, int);
_off_t	_swilseek	(int, _off_t, int);
int	_read		(int, void *, size_t);
int	_swiread	(int, void *, size_t);
void	initialise_monitor_handles (void);

static int	checkerror	(int);
static int	error		(int);
static int	get_errno	(void);

/* Semihosting utilities.  */
static void initialise_semihosting_exts (void);

/* Struct used to keep track of the file position, just so we
   can implement fseek(fh,x,SEEK_CUR).  */
struct fdent
{
  int handle;
  int pos;
};

#define MAX_OPEN_FILES 20

/* User file descriptors (fd) are integer indexes into 
   the openfiles[] array. Error checking is done by using
   findslot(). 

   This openfiles array is manipulated directly by only 
   these 5 functions:

	findslot() - Translate entry.
	newslot() - Find empty entry.
	initilise_monitor_handles() - Initialize entries.
	_swiopen() - Initialize entry.
	_close() - Handle stdout == stderr case.

   Every other function must use findslot().  */

static struct fdent openfiles [MAX_OPEN_FILES];

static struct fdent* 	findslot	(int);
static int		newslot		(void);

/* Register name faking - works in collusion with the linker.  */
register char * stack_ptr asm ("sp");


/* following is copied from libc/stdio/local.h to check std streams */
extern void   __sinit (struct _reent *);
#define CHECK_INIT(ptr) \
  do						\
    {						\
      if ((ptr) && !(ptr)->__cleanup)		\
	__sinit (ptr);				\
    }						\
  while (0)

static int monitor_stdin;
static int monitor_stdout;
static int monitor_stderr;

static int supports_ext_exit_extended = -1;
static int supports_ext_stdout_stderr = -1;

/* Return a pointer to the structure associated with
   the user file descriptor fd. */ 
static struct fdent*
findslot (int fd)
{
  CHECK_INIT(_REENT);

  /* User file descriptor is out of range. */
  if ((unsigned int)fd >= MAX_OPEN_FILES)
    return NULL;

  /* User file descriptor is open? */
  if (openfiles[fd].handle == -1)
    return NULL;

  /* Valid. */
  return &openfiles[fd];
}

/* Return the next lowest numbered free file 
   structure, or -1 if we can't find one. */ 
static int
newslot (void)
{
  int i;

  for (i = 0; i < MAX_OPEN_FILES; i++)
    if (openfiles[i].handle == -1)
      break;

  if (i == MAX_OPEN_FILES)
    return -1;

  return i;
}

void
initialise_monitor_handles (void)
{
  int i;
  
  /* Open the standard file descriptors by opening the special
   * teletype device, ":tt", read-only to obtain a descriptor for
   * standard input and write-only to obtain a descriptor for standard
   * output. Finally, open ":tt" in append mode to obtain a descriptor
   * for standard error. Since this is a write mode, most kernels will
   * probably return the same value as for standard output, but the
   * kernel can differentiate the two using the mode flag and return a
   * different descriptor for standard error.
   */

#ifdef ARM_RDI_MONITOR
  int volatile block[3];

  block[0] = (int) ":tt";
  block[2] = 3;     /* length of filename */
  block[1] = 0;     /* mode "r" */
  monitor_stdin = do_AngelSWI (AngelSWI_Reason_Open, (void *) block);

  for (i = 0; i < MAX_OPEN_FILES; i ++)
    openfiles[i].handle = -1;

  if (_has_ext_stdout_stderr ())
  {
    block[0] = (int) ":tt";
    block[2] = 3;     /* length of filename */
    block[1] = 4;     /* mode "w" */
    monitor_stdout = do_AngelSWI (AngelSWI_Reason_Open, (void *) block);

    block[0] = (int) ":tt";
    block[2] = 3;     /* length of filename */
    block[1] = 8;     /* mode "a" */
    monitor_stderr = do_AngelSWI (AngelSWI_Reason_Open, (void *) block);
  }
#else
  int fh;
  const char * name;

  name = ":tt";
  asm ("mov r0,%2; mov r1, #0; swi %a1; mov %0, r0"
       : "=r"(fh)
       : "i" (SWI_Open),"r"(name)
       : "r0","r1");
  monitor_stdin = fh;

  if (_has_ext_stdout_stderr ())
  {
    name = ":tt";
    asm ("mov r0,%2; mov r1, #4; swi %a1; mov %0, r0"
	 : "=r"(fh)
	 : "i" (SWI_Open),"r"(name)
	 : "r0","r1");
    monitor_stdout = fh;

    name = ":tt";
    asm ("mov r0,%2; mov r1, #8; swi %a1; mov %0, r0"
	 : "=r"(fh)
	 : "i" (SWI_Open),"r"(name)
	 : "r0","r1");
    monitor_stderr = fh;
  }
#endif

  /* If we failed to open stderr, redirect to stdout. */
  if (monitor_stderr == -1)
    monitor_stderr = monitor_stdout;

  openfiles[0].handle = monitor_stdin;
  openfiles[0].pos = 0;

  if (_has_ext_stdout_stderr ())
  {
    openfiles[1].handle = monitor_stdout;
    openfiles[1].pos = 0;
    openfiles[2].handle = monitor_stderr;
    openfiles[2].pos = 0;
  }
}

int
_has_ext_exit_extended (void)
{
  if (supports_ext_exit_extended < 0)
  {
    initialise_semihosting_exts ();
  }

  return supports_ext_exit_extended;
}

int
_has_ext_stdout_stderr (void)
{
  if (supports_ext_stdout_stderr < 0)
  {
    initialise_semihosting_exts ();
  }

  return supports_ext_stdout_stderr;
}

static void
initialise_semihosting_exts (void)
{
  supports_ext_exit_extended = 0;
  supports_ext_stdout_stderr = 1;

#if SEMIHOST_V2
  char features[1];
  if (_get_semihosting_exts (features, 0, 1) > 0)
  {
     supports_ext_exit_extended
       = features[0] & (1 << SH_EXT_EXIT_EXTENDED_BITNUM);
     supports_ext_stdout_stderr
       = features[0] & (1 << SH_EXT_STDOUT_STDERR_BITNUM);
  }
#endif
}

int
_get_semihosting_exts (char* features, int offset, int num)
{
  int len;
  struct fdent *pfd;
  int fd = _open (":semihosting-features", O_RDONLY);
  memset (features, 0, num);

  if (fd == -1)
  {
    return -1;
  }

  pfd = findslot (fd);

#ifdef ARM_RDI_MONITOR
  len = checkerror (do_AngelSWI (AngelSWI_Reason_FLen, &pfd->handle));
#else
  asm ("mov r0,%2; swi %a1; mov %0, r0"
       : "=r"(len)
       : "i" (SWI_Flen),"r"(pfd->handle)
       : "r0");
#endif

  if (len < NUM_SHFB_MAGIC
      || num > (len - NUM_SHFB_MAGIC))
  {
     _close (fd);
     return -1;
  }

  char buffer[NUM_SHFB_MAGIC];
  int n_read = _read (fd, buffer, NUM_SHFB_MAGIC);

  if (n_read < NUM_SHFB_MAGIC
      || buffer[0] != SHFB_MAGIC_0
      || buffer[1] != SHFB_MAGIC_1
      || buffer[2] != SHFB_MAGIC_2
      || buffer[3] != SHFB_MAGIC_3)
  {
     _close (fd);
     return -1;
  }

  if (_lseek (fd, offset, SEEK_CUR) < 0)
  {
     _close (fd);
     return -1;
  }

  n_read = _read (fd, features, num);

  _close (fd);

  return checkerror (n_read);
}

static int
get_errno (void)
{
#ifdef ARM_RDI_MONITOR
  return do_AngelSWI (AngelSWI_Reason_Errno, NULL);
#else
  register int r0 asm("r0");
  asm ("swi %a1" : "=r"(r0) : "i" (SWI_GetErrno));
  return r0;
#endif
}

/* Set errno and return result. */
static int
error (int result)
{
  errno = get_errno ();
  return result;
}

/* Check the return and set errno appropriately. */
static int
checkerror (int result)
{
  if (result == -1)
    return error (-1);
  return result;
}

/* fh, is a valid internal file handle.
   ptr, is a null terminated string.
   len, is the length in bytes to read. 
   Returns the number of bytes *not* written. */
int
_swiread (int fh, void * ptr, size_t len)
{
#ifdef ARM_RDI_MONITOR
  int block[3];

  block[0] = fh;
  block[1] = (int) ptr;
  block[2] = (int) len;

  return checkerror (do_AngelSWI (AngelSWI_Reason_Read, block));
#else
  register int r0 asm("r0");
  register int r1 asm("r1");
  register int r2 asm("r2");
  r0 = fh;
  r1 = (int) ptr;
  r2 = (int) len;
  asm ("swi %a4"
       : "=r" (r0)
       : "0"(r0), "r"(r1), "r"(r2), "i"(SWI_Read));
  return checkerror (r0);
#endif
}

/* fd, is a valid user file handle.
   Translates the return of _swiread into
   bytes read. */
int __attribute__((weak))
_read (int fd, void * ptr, size_t len)
{
  int res;
  struct fdent *pfd;

  pfd = findslot (fd);
  if (pfd == NULL)
    {
      errno = EBADF;
      return -1;
    }

  res = _swiread (pfd->handle, ptr, len);

  if (res == -1)
    return res;

  pfd->pos += len - res;

  /* res == len is not an error, 
     at least if we want feof() to work.  */
  return len - res;
}

/* fd, is a user file descriptor. */
off_t
_swilseek (int fd, off_t ptr, int dir)
{
  off_t res;
  struct fdent *pfd;

  /* Valid file descriptor? */
  pfd = findslot (fd);
  if (pfd == NULL)
    {
      errno = EBADF;
      return -1;
    }

  /* Valid whence? */
  if ((dir != SEEK_CUR)
      && (dir != SEEK_SET)
      && (dir != SEEK_END))
    {
      errno = EINVAL;
      return -1;
    }

  /* Convert SEEK_CUR to SEEK_SET */
  if (dir == SEEK_CUR)
    {
      ptr = pfd->pos + ptr;
      /* The resulting file offset would be negative. */
      if (ptr < 0)
        {
          errno = EINVAL;
          if ((pfd->pos > 0) && (ptr > 0))
            errno = EOVERFLOW;
          return -1;
        }
      dir = SEEK_SET;
    }

#ifdef ARM_RDI_MONITOR
  int block[2];
  if (dir == SEEK_END)
    {
      block[0] = pfd->handle;
      res = checkerror (do_AngelSWI (AngelSWI_Reason_FLen, block));
      if (res == -1)
        return -1;
      ptr += res;
    }

  /* This code only does absolute seeks.  */
  block[0] = pfd->handle;
  block[1] = (int) ptr;
  res = checkerror (do_AngelSWI (AngelSWI_Reason_Seek, block));
#else
  if (dir == SEEK_END)
    {
      asm ("mov r0, %2; swi %a1; mov %0, r0"
	   : "=r" (res)
	   : "i" (SWI_Flen), "r" (pfd->handle)
	   : "r0");
      checkerror (res);
      if (res == -1)
        return -1;
      ptr += res;
    }

  /* This code only does absolute seeks.  */
  asm ("mov r0, %2; mov r1, %3; swi %a1; mov %0, r0"
       : "=r" (res)
       : "i" (SWI_Seek), "r" (pfd->handle), "r" (ptr)
       : "r0", "r1");
  checkerror (res);
#endif
  /* At this point ptr is the current file position. */
  if (res >= 0)
    {
      pfd->pos = ptr;
      return ptr;
    }
  else
    return -1;
}

off_t
_lseek (int fd, off_t ptr, int dir)
{
  return _swilseek (fd, ptr, dir);
}

/* fh, is a valid internal file handle.
   Returns the number of bytes *not* written. */
int
_swiwrite (int fh, const void * ptr, size_t len)
{
#ifdef ARM_RDI_MONITOR
  int block[3];

  block[0] = fh;
  block[1] = (int) ptr;
  block[2] = (int) len;

  return checkerror (do_AngelSWI (AngelSWI_Reason_Write, block));
#else
  register int r0 asm("r0");
  register int r1 asm("r1");
  register int r2 asm("r2");
  r0 = fh;
  r1 = (int)ptr;
  r2 = len;
  asm ("swi %a4"
       : "=r" (r0)
       : "0"(r0), "r"(r1), "r"(r2), "i"(SWI_Write));
  return checkerror (r0);
#endif
}

/* fd, is a user file descriptor. */
int __attribute__((weak))
_write (int fd, const void * ptr, size_t len)
{
  int res;
  struct fdent *pfd;

  pfd = findslot (fd);
  if (pfd == NULL)
    {
      errno = EBADF;
      return -1;
    }

  res = _swiwrite (pfd->handle, ptr,len);

  /* Clearly an error. */
  if (res < 0)
    return -1;

  pfd->pos += len - res;

  /* We wrote 0 bytes? 
     Retrieve errno just in case. */
  if ((len - res) == 0)
    return error (0);
  
  return (len - res);
}

int
_swiopen (const char * path, int flags)
{
  int aflags = 0, fh;
#ifdef ARM_RDI_MONITOR
  int block[3];
#endif
  
  int fd = newslot ();

  if (fd == -1)
    {
      errno = EMFILE;
      return -1;
    }
  
  /* It is an error to open a file that already exists. */
  if ((flags & O_CREAT) 
      && (flags & O_EXCL))
    {
      struct stat st;
      int res;
      res = _stat (path, &st);
      if (res != -1)
        {
	  errno = EEXIST;
	  return -1;
        }
    }

  /* The flags are Unix-style, so we need to convert them.  */
#ifdef O_BINARY
  if (flags & O_BINARY)
    aflags |= 1;
#endif
  
  /* In O_RDONLY we expect aflags == 0. */

  if (flags & O_RDWR) 
    aflags |= 2;

  if ((flags & O_CREAT)
      || (flags & O_TRUNC)
      || (flags & O_WRONLY))
    aflags |= 4;

  if (flags & O_APPEND)
    {
      aflags &= ~4; /* Can't ask for w AND a; means just 'a'.  */
      aflags |= 8;
    }

#ifdef ARM_RDI_MONITOR
  block[0] = (int) path;
  block[2] = strlen (path);
  block[1] = aflags;

  fh = do_AngelSWI (AngelSWI_Reason_Open, block);

#else
  asm ("mov r0,%2; mov r1, %3; swi %a1; mov %0, r0"
       : "=r"(fh)
       : "i" (SWI_Open),"r"(path),"r"(aflags)
       : "r0","r1");
#endif

  /* Return a user file descriptor or an error. */
  if (fh >= 0)
    {
      openfiles[fd].handle = fh;
      openfiles[fd].pos = 0;
      return fd;
    }
  else
    return error (fh);
}

int
_open (const char * path, int flags, ...)
{
  return _swiopen (path, flags);
}

/* fh, is a valid internal file handle. */
int
_swiclose (int fh)
{
#ifdef ARM_RDI_MONITOR
  return checkerror (do_AngelSWI (AngelSWI_Reason_Close, &fh));
#else
  register int r0 asm("r0");
  r0 = fh;
  asm ("swi %a2" 
       : "=r"(r0) 
       : "0"(r0), "i" (SWI_Close));
  return checkerror (r0);
#endif
}

/* fd, is a user file descriptor. */
int
_close (int fd)
{
  int res;
  struct fdent *pfd;

  pfd = findslot (fd);
  if (pfd == NULL)
    {
      errno = EBADF;
      return -1;
    }

  /* Handle stderr == stdout. */
  if ((fd == 1 || fd == 2)
      && (openfiles[1].handle == openfiles[2].handle))
    {
      pfd->handle = -1;
      return 0;
    }

  /* Attempt to close the handle. */
  res = _swiclose (pfd->handle);

  /* Reclaim handle? */
  if (res == 0)
    pfd->handle = -1;

  return res;
}

pid_t __attribute__((weak))
_getpid (void)
{
  return (pid_t)1;
}

/* Heap limit returned from SYS_HEAPINFO Angel semihost call.  */
uint __heap_limit = 0xcafedead;

void * __attribute__((weak))
_sbrk (ptrdiff_t incr)
{
  extern char   end asm ("end"); /* Defined by the linker.  */
  static char * heap_end;
  char *        prev_heap_end;

  if (heap_end == NULL)
    heap_end = & end;

  prev_heap_end = heap_end;

  if ((heap_end + incr > stack_ptr)
      /* Honour heap limit if it's valid.  */
      || (__heap_limit != 0xcafedead && heap_end + incr > (char *)__heap_limit))
    {
      /* Some of the libstdc++-v3 tests rely upon detecting
	 out of memory errors, so do not abort here.  */
#if 0
      extern void abort (void);

      _write (1, "_sbrk: Heap and stack collision\n", 32);

      abort ();
#else
      errno = ENOMEM;
      return (void *) -1;
#endif
    }

  heap_end += incr;

  return (void *) prev_heap_end;
}

int 
_swistat (int fd, struct stat * st)
{
  struct fdent *pfd;
  int res;

  pfd = findslot (fd);
  if (pfd == NULL)
    {
      errno = EBADF;
      return -1;
    }

  /* Always assume a character device,
     with 1024 byte blocks. */
  st->st_mode |= S_IFCHR;
  st->st_blksize = 1024;
#ifdef ARM_RDI_MONITOR
  res = checkerror (do_AngelSWI (AngelSWI_Reason_FLen, &pfd->handle));
#else
  asm ("mov r0, %2; swi %a1; mov %0, r0"
       : "=r" (res)
       : "i" (SWI_Flen), "r" (pfd->handle)
       : "r0");
  checkerror (res);
#endif
  if (res == -1)
    return -1;
  /* Return the file size. */
  st->st_size = res;
  return 0;
}

int __attribute__((weak))
_fstat (int fd, struct stat * st)
{
  memset (st, 0, sizeof (* st));
  return _swistat (fd, st);
}

int __attribute__((weak))
_stat (const char *fname, struct stat *st)
{
  int fd, res;
  memset (st, 0, sizeof (* st));
  /* The best we can do is try to open the file readonly.  If it exists,
     then we can guess a few things about it.  */
  if ((fd = _open (fname, O_RDONLY)) == -1)
    return -1;
  st->st_mode |= S_IFREG | S_IREAD;
  res = _swistat (fd, st);
  /* Not interested in the error.  */
  _close (fd); 
  return res;
}

int __attribute__((weak))
_link (const char *__path1 __attribute__ ((unused)), const char *__path2 __attribute__ ((unused)))
{
  errno = ENOSYS;
  return -1;
}

int
_unlink (const char *path)
{
  int res;
#ifdef ARM_RDI_MONITOR
  int block[2];
  block[0] = (int)path;
  block[1] = strlen(path);
  res = do_AngelSWI (AngelSWI_Reason_Remove, block);
#else
  register int r0 asm("r0");
  r0 = (int)path;
  asm ("swi %a2" 
       : "=r"(r0)
       : "0"(r0), "i" (SWI_Remove));
  res = r0;
#endif
  if (res == -1) 
    return error (res);
  return 0;
}

int
_gettimeofday (struct timeval * tp, void * tzvp)
{
  struct timezone *tzp = tzvp;
  if (tp)
    {
    /* Ask the host for the seconds since the Unix epoch.  */
#ifdef ARM_RDI_MONITOR
      tp->tv_sec = do_AngelSWI (AngelSWI_Reason_Time,NULL);
#else
      {
        int value;
        asm ("swi %a1; mov %0, r0" : "=r" (value): "i" (SWI_Time) : "r0");
        tp->tv_sec = value;
      }
#endif
      tp->tv_usec = 0;
    }

  /* Return fixed data for the timezone.  */
  if (tzp)
    {
      tzp->tz_minuteswest = 0;
      tzp->tz_dsttime = 0;
    }

  return 0;
}

/* Return a clock that ticks at 100Hz.  */
clock_t 
_clock (void)
{
  clock_t timeval;

#ifdef ARM_RDI_MONITOR
  timeval = do_AngelSWI (AngelSWI_Reason_Clock,NULL);
#else
  asm ("swi %a1; mov %0, r0" : "=r" (timeval): "i" (SWI_Clock) : "r0");
#endif
  return timeval;
}

/* Return a clock that ticks at 100Hz.  */
clock_t
_times (struct tms * tp)
{
  clock_t timeval = _clock();

  if (tp)
    {
      tp->tms_utime  = timeval;	/* user time */
      tp->tms_stime  = 0;	/* system time */
      tp->tms_cutime = 0;	/* user time, children */
      tp->tms_cstime = 0;	/* system time, children */
    }

  return timeval;
};


int
_isatty (int fd)
{
  struct fdent *pfd;
  int tty;

  pfd = findslot (fd);
  if (pfd == NULL)
    {
      errno = EBADF;
      return 0;
    }

#ifdef ARM_RDI_MONITOR
  tty = do_AngelSWI (AngelSWI_Reason_IsTTY, &pfd->handle);
#else
  register int r0 asm("r0");
  r0 = pfd->handle;
  asm ("swi %a2"
       : "=r" (r0)
       : "0"(r0), "i" (SWI_IsTTY));
  tty = r0;
#endif

  if (tty == 1)
    return 1;
  errno = get_errno ();
  return 0;
}

int
_system (const char *s)
{
#ifdef ARM_RDI_MONITOR
  int block[2];
  int e;

  /* Hmmm.  The ARM debug interface specification doesn't say whether
     SYS_SYSTEM does the right thing with a null argument, or assign any
     meaning to its return value.  Try to do something reasonable....  */
  if (!s)
    return 1;  /* maybe there is a shell available? we can hope. :-P */
  block[0] = (int)s;
  block[1] = strlen (s);
  e = checkerror (do_AngelSWI (AngelSWI_Reason_System, block));
  if ((e >= 0) && (e < 256))
    {
      /* We have to convert e, an exit status to the encoded status of
         the command.  To avoid hard coding the exit status, we simply
	 loop until we find the right position.  */
      int exit_code;

      for (exit_code = e; e && WEXITSTATUS (e) != exit_code; e <<= 1)
	continue;
    }
  return e;
#else
  register int r0 asm("r0");
  r0 = (int)s;
  asm ("swi %a2" 
       : "=r" (r0)
       : "0"(r0), "i" (SWI_CLI));
  return checkerror (r0);
#endif
}

int
_rename (const char * oldpath, const char * newpath)
{
#ifdef ARM_RDI_MONITOR
  int block[4];
  block[0] = (int)oldpath;
  block[1] = strlen(oldpath);
  block[2] = (int)newpath;
  block[3] = strlen(newpath);
  return checkerror (do_AngelSWI (AngelSWI_Reason_Rename, block)) ? -1 : 0;
#else
  register int r0 asm("r0");
  register int r1 asm("r1");
  r0 = (int)oldpath;
  r1 = (int)newpath;
  asm ("swi %a3" 
       : "=r" (r0)
       : "0" (r0), "r" (r1), "i" (SWI_Rename));
  return checkerror (r0);
#endif
}
