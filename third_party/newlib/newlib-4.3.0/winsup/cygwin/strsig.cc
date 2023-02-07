/* strsig.cc

This file is part of Cygwin.

This software is a copyrighted work licensed under the terms of the
Cygwin license.  Please consult the file "CYGWIN_LICENSE" for
details. */

#include "winsup.h"
#include <cygtls.h>
#include <stdio.h>
#include <string.h>
#include <sys/uio.h>

struct sigdesc
{
  int n;
  const char *name;
  const char *str;
};

#define __signals \
  _s(SIGHUP, "Hangup"),				/*  1 */ \
  _s(SIGINT, "Interrupt"),			/*  2 */ \
  _s(SIGQUIT, "Quit"),				/*  3 */ \
  _s(SIGILL, "Illegal instruction"),		/*  4 */ \
  _s(SIGTRAP, "Trace/breakpoint trap"),		/*  5 */ \
  _s2(SIGABRT, "Aborted",			/*  6 */ \
      SIGIOT, "Aborted"),				 \
  _s(SIGEMT, "EMT instruction"),		/*  7 */ \
  _s(SIGFPE, "Floating point exception"),	/*  8 */ \
  _s(SIGKILL, "Killed"),			/*  9 */ \
  _s(SIGBUS, "Bus error"),			/* 10 */ \
  _s(SIGSEGV, "Segmentation fault"),		/* 11 */ \
  _s(SIGSYS, "Bad system call"),		/* 12 */ \
  _s(SIGPIPE, "Broken pipe"),			/* 13 */ \
  _s(SIGALRM, "Alarm clock"),			/* 14 */ \
  _s(SIGTERM, "Terminated"),			/* 15 */ \
  _s(SIGURG, "Urgent I/O condition"),		/* 16 */ \
  _s(SIGSTOP, "Stopped (signal)"),		/* 17 */ \
  _s(SIGTSTP, "Stopped"),			/* 18 */ \
  _s(SIGCONT, "Continued"),			/* 19 */ \
  _s2(SIGCHLD, "Child exited",			/* 20 */ \
      SIGCLD, "Child exited"),				 \
  _s(SIGTTIN, "Stopped (tty input)"),		/* 21 */ \
  _s(SIGTTOU, "Stopped (tty output)"),		/* 22 */ \
  _s2(SIGIO, "I/O possible",			/* 23 */ \
      SIGPOLL, "I/O possible"),				 \
  _s(SIGXCPU, "CPU time limit exceeded"),	/* 24 */ \
  _s(SIGXFSZ, "File size limit exceeded"),	/* 25 */ \
  _s(SIGVTALRM, "Virtual timer expired"),	/* 26 */ \
  _s(SIGPROF, "Profiling timer expired"),	/* 27 */ \
  _s(SIGWINCH, "Window changed"),		/* 28 */ \
  _s2(SIGPWR, "Power failure",			/* 29 */ \
      SIGLOST, "Resource lost"),			 \
  _s(SIGUSR1, "User defined signal 1"),		/* 30 */ \
  _s(SIGUSR2, "User defined signal 2"),		/* 31 */ \
  _s(SIGRTMIN, "Real-time signal 0"),		/* 32 */ \
  _s(SIGRTMIN + 1, "Real-time signal 1"),	/* 33 */ \
  _s(SIGRTMIN + 2, "Real-time signal 2"),	/* 34 */ \
  _s(SIGRTMIN + 3, "Real-time signal 3"),	/* 35 */ \
  _s(SIGRTMIN + 4, "Real-time signal 4"),	/* 36 */ \
  _s(SIGRTMIN + 5, "Real-time signal 5"),	/* 37 */ \
  _s(SIGRTMIN + 6, "Real-time signal 6"),	/* 38 */ \
  _s(SIGRTMIN + 7, "Real-time signal 7"),	/* 39 */ \
  _s(SIGRTMIN + 8, "Real-time signal 8"),	/* 40 */ \
  _s(SIGRTMIN + 9, "Real-time signal 9"),	/* 41 */ \
  _s(SIGRTMIN + 10, "Real-time signal 10"),	/* 42 */ \
  _s(SIGRTMIN + 11, "Real-time signal 11"),	/* 43 */ \
  _s(SIGRTMIN + 12, "Real-time signal 12"),	/* 44 */ \
  _s(SIGRTMIN + 13, "Real-time signal 13"),	/* 45 */ \
  _s(SIGRTMIN + 14, "Real-time signal 14"),	/* 46 */ \
  _s(SIGRTMIN + 15, "Real-time signal 15"),	/* 47 */ \
  _s(SIGRTMIN + 16, "Real-time signal 16"),	/* 48 */ \
  _s(SIGRTMIN + 17, "Real-time signal 17"),	/* 49 */ \
  _s(SIGRTMIN + 18, "Real-time signal 18"),	/* 50 */ \
  _s(SIGRTMIN + 19, "Real-time signal 19"),	/* 51 */ \
  _s(SIGRTMIN + 20, "Real-time signal 20"),	/* 52 */ \
  _s(SIGRTMIN + 21, "Real-time signal 21"),	/* 53 */ \
  _s(SIGRTMIN + 22, "Real-time signal 22"),	/* 54 */ \
  _s(SIGRTMIN + 23, "Real-time signal 23"),	/* 55 */ \
  _s(SIGRTMIN + 24, "Real-time signal 24"),	/* 56 */ \
  _s(SIGRTMIN + 25, "Real-time signal 25"),	/* 57 */ \
  _s(SIGRTMIN + 26, "Real-time signal 26"),	/* 58 */ \
  _s(SIGRTMIN + 27, "Real-time signal 27"),	/* 59 */ \
  _s(SIGRTMIN + 28, "Real-time signal 28"),	/* 60 */ \
  _s(SIGRTMIN + 29, "Real-time signal 29"),	/* 61 */ \
  _s(SIGRTMIN + 30, "Real-time signal 30"),	/* 62 */ \
  _s(SIGRTMIN + 31, "Real-time signal 31"),	/* 63 */ \
  _s(SIGRTMAX, "Real-time signal 32")		/* 64 */

#define _s(n, s) #n
#define _s2(n, s, n1, s1) #n
const char *sys_sigabbrev[] =
{
  NULL,
  __signals
};

#undef _s
#undef _s2
#define _s(n, s) s
#define _s2(n, s, n1, s1) s
const char *sys_siglist[] =
{
  NULL,
  __signals
};

#undef _s
#undef _s2
#define _s(n, s) {n, #n, s}
#define _s2(n, s, n1, s1) {n, #n, s}, {n, #n1, #s1}
static const sigdesc siglist[] =
{
  __signals,
  {0, NULL, NULL}
};

extern "C" char *
strsignal (int signo)
{
  const char *sigstring = "Unknown signal %d";
  for (int i = 0; siglist[i].n; i++)
    if (siglist[i].n == signo)
      {
	sigstring = siglist[i].str;
	break;
      }
  __small_sprintf (_my_tls.locals.signamebuf, sigstring, signo);
  return _my_tls.locals.signamebuf;
}

extern "C" int
strtosigno (const char *name)
{
  for (int i = 0; siglist[i].n; i++)
    if (strcmp (siglist[i].name, name) == 0)
      return siglist[i].n;
  return 0;
}

#define ADD(str) \
{ \
  v->iov_base = (void *)(str); \
  v->iov_len = strlen ((char *)v->iov_base); \
  v ++; \
  iov_cnt ++; \
}

extern "C" void
psiginfo (const siginfo_t *info, const char *s)
{
  struct iovec iov[5];
  struct iovec *v = iov;
  int iov_cnt = 0;
  char buf[64];

  if (s != NULL && *s != '\0')
    {
      ADD (s);
      ADD (": ");
    }

  ADD (strsignal (info->si_signo));

  if (info->si_signo > 0 && info->si_signo < _NSIG)
    {
      switch (info->si_signo)
	{
	  case SIGILL:
	  case SIGBUS:
	  case SIGFPE:
	  case SIGSEGV:
	    snprintf (buf, sizeof(buf),
		      " (%d [%p])", info->si_code, info->si_addr);
	    break;
	  case SIGCHLD:
	    snprintf (buf, sizeof(buf),
		      " (%d %d %d %u)", info->si_code, info->si_pid,
		     info->si_status, info->si_uid);
	    break;
/* FIXME: implement si_band
	  case SIGPOLL:
	    fprintf (stderr, " (%d %ld)", info->si_code, info->si_band);
	    break;
*/
	  default:
	    snprintf (buf, sizeof(buf),
		      " (%d %d %u)", info->si_code, info->si_pid,
		      info->si_uid);
	}
      ADD (buf);
    }

#ifdef __SCLE
  ADD ((stderr->_flags & __SCLE) ? "\r\n" : "\n");
#else
  ADD ("\n");
#endif

  fflush (stderr);
  writev (fileno (stderr), iov, iov_cnt);
}
