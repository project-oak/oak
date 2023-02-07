/* cygtls.h

This software is a copyrighted work licensed under the terms of the
Cygwin license.  Please consult the file "CYGWIN_LICENSE" for
details. */

#pragma once

#include <signal.h>
#include <pwd.h>
#include <grp.h>
#include <time.h>
#define _NOMNTENT_FUNCS
#include <mntent.h>
#undef _NOMNTENT_FUNCS
#include <setjmp.h>
#include <ucontext.h>

#define CYGTLS_INITIALIZED 0xc763173f

#ifndef CYG_MAX_PATH
# define CYG_MAX_PATH 260
#endif

#ifndef UNLEN
# define UNLEN 256
#endif

#define TLS_STACK_SIZE 256

#include "cygthread.h"

#define TP_NUM_C_BUFS 50
#define TP_NUM_W_BUFS 50

#ifdef CYGTLS_HANDLE
#include "thread.h"
#endif

#pragma pack(push,8)

/* Defined here to support auto rebuild of tlsoffsets.h. */
class tls_pathbuf
{
  /* Make sure that c_cnt and w_cnt are always the first two members of this
     class, and never change the size (32 bit), unless you also change the
     mov statements in sigbe! */
  union
    {
      struct
	{
	  uint32_t c_cnt;
	  uint32_t w_cnt;
	};
      uint64_t _counters;
    };
  HANDLE tls_heap;
  char  *c_buf[TP_NUM_C_BUFS];
  WCHAR *w_buf[TP_NUM_W_BUFS];

public:
  void clear () { memset (this, 0, sizeof *this); }
  void create ();
  void destroy ();
  friend class tmp_pathbuf;
  friend class san;
};

class unionent
{
public:
  char *name;
  char **list;
  short port_proto_addrtype;
  short h_len;
  union
  {
    char *s_proto;
    char **h_addr_list;
  };
  enum struct_type
  {
    t_hostent, t_protoent, t_servent
  };
};

struct _local_storage
{
  /* passwd.cc */
  char pass[_PASSWORD_LEN];

  /* dlfcn.cc */
  int dl_error;
  char dl_buffer[256];

  /* path.cc */
  struct mntent mntbuf;
  int iteration;
  unsigned available_drives;
  char mnt_type[80];
  char mnt_opts[80];
  char mnt_fsname[CYG_MAX_PATH];
  char mnt_dir[CYG_MAX_PATH];

  /* select.cc */
  struct {
    HANDLE  sockevt;
    int     max_w4;
    LONG   *ser_num;			// note: malloced
    HANDLE *w4;				// note: malloced
  } select;

  /* strerror errno.cc */
  char strerror_buf[sizeof ("Unknown error -2147483648")];
  char strerror_r_buf[sizeof ("Unknown error -2147483648")];

  /* times.cc */
  char timezone_buf[20];

  /* strsig.cc */
  char signamebuf[sizeof ("Unknown signal 4294967295   ")];

  /* net.cc */
  char *ntoa_buf;			// note: malloced
  unionent *hostent_buf;		// note: malloced
  unionent *protoent_buf;		// note: malloced
  unionent *servent_buf;		// note: malloced

  /* cygthread.cc */
  char unknown_thread_name[30];

  /* syscalls.cc */
  int setmode_file;
  int setmode_mode;

  /* thread.cc */
  HANDLE cw_timer;

  tls_pathbuf pathbufs;
  char ttybuf[32];
};

typedef struct struct_waitq
{
  int pid;
  int options;
  int status;
  HANDLE ev;
  void *rusage;			/* pointer to potential rusage */
  struct struct_waitq *next;
  HANDLE thread_ev;
} waitq;

/* Changes to the below structure may require acompanying changes to the
   gawk parser in the shell script 'gentls_offsets' */

extern "C" int __sjfault (jmp_buf);
extern "C" int __ljfault (jmp_buf, int);

typedef uintptr_t __tlsstack_t;

class _cygtls
{
public: /* Do NOT remove this public: line, it's a marker for gentls_offsets. */
  /* offsetoff (class _cygtls, local_clib) *must* be 0. */
  struct _reent local_clib;
  struct _local_storage locals;
  /**/
  void (*func) (int, siginfo_t *, void *);
  int saved_errno;
  int sa_flags;
  sigset_t oldmask;
  sigset_t deltamask;
  int *errno_addr;
  sigset_t sigmask;
  sigset_t sigwait_mask;
  stack_t altstack;
  siginfo_t *sigwait_info;
  HANDLE signal_arrived;
  bool will_wait_for_signal;
#if 0
  long __align;			/* Needed to align context to 16 byte. */
#endif
  /* context MUST be aligned to 16 byte, otherwise RtlCaptureContext fails.
     If you prepend cygtls members here, make sure context stays 16 byte
     aligned. The gentls_offsets script checks for that now and fails
     if the alignment is wrong. */
  ucontext_t context;
  DWORD thread_id;
  siginfo_t infodata;
  struct pthread *tid;
  class cygthread *_ctinfo;
  class san *andreas;
  waitq wq;
  int sig;
  unsigned incyg;
  unsigned spinning;
  unsigned stacklock;
  __tlsstack_t *stackptr;
  __tlsstack_t stack[TLS_STACK_SIZE];
  unsigned initialized;

public: /* Do NOT remove this public: line, it's a marker for gentls_offsets. */
  void init_thread (void *, DWORD (*) (void *, void *));
  static void call (DWORD (*) (void *, void *), void *);
  void remove (DWORD);
  void push (__tlsstack_t addr) {*stackptr++ = (__tlsstack_t) addr;}
  __tlsstack_t pop ();
  __tlsstack_t retaddr () {return stackptr[-1];}
  bool isinitialized () const
  {
    return initialized == CYGTLS_INITIALIZED;
  }
  bool interrupt_now (CONTEXT *, siginfo_t&, void *, struct sigaction&);
  void interrupt_setup (siginfo_t&, void *, struct sigaction&);

  bool inside_kernel (CONTEXT *);
  void signal_debugger (siginfo_t&);

#ifdef CYGTLS_HANDLE
  operator HANDLE () const {return tid ? tid->win32_obj_id : NULL;}
#endif
  int call_signal_handler ();
  void remove_wq (DWORD);
  void fixup_after_fork ();
  void lock ();
  void unlock ();
  bool locked ();
  HANDLE get_signal_arrived (bool wait_for_lock = true)
  {
    if (!signal_arrived)
      {
	if (wait_for_lock)
	  lock ();
	if (!signal_arrived)
	  signal_arrived = CreateEvent (NULL, false, false, NULL);
	if (wait_for_lock)
	  unlock ();
      }
    return signal_arrived;
  }
  void wait_signal_arrived (bool setit, HANDLE& h)
  {
    if (!setit)
      will_wait_for_signal = false;
    else
      {
	h = get_signal_arrived ();
	will_wait_for_signal = true;
      }
  }
  void set_signal_arrived ()
  {
    SetEvent (get_signal_arrived (false));
  }
  void reset_signal_arrived ()
  {
    if (signal_arrived)
      ResetEvent (signal_arrived);
  }
  void unwait_signal_arrived ()
  {
    will_wait_for_signal = false;
  }
  void handle_SIGCONT ();
  static void cleanup_early(struct _reent *);
private:
  void call2 (DWORD (*) (void *, void *), void *, void *);
  void remove_pending_sigs ();
};
#pragma pack(pop)

#include "cygerrno.h"
#include "ntdll.h"

#define _my_tls (*((_cygtls *) ((PBYTE) NtCurrentTeb()->Tib.StackBase \
		                - __CYGTLS_PADSIZE__)))
extern _cygtls *_main_tls;
extern _cygtls *_sig_tls;

class san
{
  san *_clemente;
  uint64_t _cnt;
public:
  DWORD64 ret;
  DWORD64 frame;

  san (PVOID _ret) __attribute__ ((always_inline))
  {
    _clemente = _my_tls.andreas;
    _my_tls.andreas = this;
    _cnt = _my_tls.locals.pathbufs._counters;
    /* myfault_altstack_handler needs the current stack pointer and the
       address of the _except block to restore the context correctly.
       See comment preceeding myfault_altstack_handler in exception.cc. */
    ret = (DWORD64) _ret;
    __asm__ volatile ("movq %%rsp,%0": "=o" (frame));
  }
  ~san () __attribute__ ((always_inline))
  {
    _my_tls.andreas = _clemente;
  }
  /* This is the first thing called in the __except handler.  The attribute
     "returns_twice" makes sure that GCC disregards any register value set
     earlier in the function, so this call serves as a register barrier. */
  void leave () __attribute__ ((returns_twice));
};

/* Exception handling macros. This is a handmade SEH try/except. */
#define __mem_barrier	__asm__ __volatile__ ("" ::: "memory")
#define __try \
  { \
    __label__ __l_try, __l_except, __l_endtry; \
    __mem_barrier; \
    san __sebastian (&&__l_except); \
    __asm__ goto ("\n" \
      "  .seh_handler _ZN9exception7myfaultEP17_EXCEPTION_RECORDPvP8_CONTEXTP19_DISPATCHER_CONTEXT, @except						\n" \
      "  .seh_handlerdata						\n" \
      "  .long 1							\n" \
      "  .rva %l[__l_try],%l[__l_endtry],%l[__l_except],%l[__l_except]	\n" \
      "  .seh_code							\n" \
      : : : : __l_try, __l_endtry, __l_except); \
    { \
      __l_try: \
	__mem_barrier;

#define __leave	\
      goto __l_endtry

#define __except(__errno) \
      goto __l_endtry; \
    } \
    { \
      __l_except: \
	__mem_barrier; \
	__sebastian.leave (); \
	if (__errno) \
	  set_errno (__errno);

#define __endtry \
    } \
    __l_endtry: \
      __mem_barrier; \
  }

class wait_signal_arrived
{
public:
  wait_signal_arrived (bool setit, HANDLE& h) { _my_tls.wait_signal_arrived (setit, h); }
  wait_signal_arrived (HANDLE& h) { _my_tls.wait_signal_arrived (true, h); }

  operator int () const {return _my_tls.will_wait_for_signal;}
  /* Do not reset the signal_arrived event just because we leave the scope of
     this wait_signal_arrived object.  This may lead to all sorts of races.
     The only method actually resetting the signal_arrived event is
     _cygtls::call_signal_handler. */
  ~wait_signal_arrived () { _my_tls.unwait_signal_arrived (); }
};
/*gentls_offsets*/
