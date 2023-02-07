/* sem.cc: XSI IPC interface for Cygwin.

This file is part of Cygwin.

This software is a copyrighted work licensed under the terms of the
Cygwin license.  Please consult the file "CYGWIN_LICENSE" for
details. */

#include "winsup.h"
#include <unistd.h>

#include "sigproc.h"

#include "cygserver_sem.h"
#include "cygtls.h"

/*
 * client_request_sem Constructors
 */

client_request_sem::client_request_sem (int semid,
					int semnum,
					int cmd,
					union semun *arg)
  : client_request (CYGSERVER_REQUEST_SEM, &_parameters, sizeof (_parameters))
{
  _parameters.in.semop = SEMOP_semctl;
  ipc_set_proc_info (_parameters.in.ipcblk);

   _parameters.in.ctlargs.semid = semid;
   _parameters.in.ctlargs.semnum = semnum;
   _parameters.in.ctlargs.cmd = cmd;
   _parameters.in.ctlargs.arg = arg;

  msglen (sizeof (_parameters.in));
}

client_request_sem::client_request_sem (key_t key,
					int nsems,
					int semflg)
  : client_request (CYGSERVER_REQUEST_SEM, &_parameters, sizeof (_parameters))
{
  _parameters.in.semop = SEMOP_semget;
  ipc_set_proc_info (_parameters.in.ipcblk);

  _parameters.in.getargs.key = key;
  _parameters.in.getargs.nsems = nsems;
  _parameters.in.getargs.semflg = semflg;

  msglen (sizeof (_parameters.in));
}

client_request_sem::client_request_sem (int semid,
					struct sembuf *sops,
					size_t nsops)
  : client_request (CYGSERVER_REQUEST_SEM, &_parameters, sizeof (_parameters))
{
  _parameters.in.semop = SEMOP_semop;
  ipc_set_proc_info (_parameters.in.ipcblk);

  _parameters.in.opargs.semid = semid;
  _parameters.in.opargs.sops = sops;
  _parameters.in.opargs.nsops = nsops;

  msglen (sizeof (_parameters.in));
}

/*
 * XSI semaphore API.  These are exported by the DLL.
 */

extern "C" int
semctl (int semid, int semnum, int cmd, ...)
{
  union semun arg = {0};
  if (cmd == IPC_STAT || cmd == IPC_SET || cmd == IPC_INFO || cmd == SEM_INFO
      || cmd == GETALL || cmd == SETALL || cmd == SETVAL)
    {
      va_list ap;
      va_start (ap, cmd);
      arg = va_arg (ap, union semun);
      va_end (ap);
    }
  syscall_printf ("semctl (semid = %d, semnum = %d, cmd = %d, arg = %p)",
		  semid, semnum, cmd, arg.buf);
  __try
    {
      client_request_sem request (semid, semnum, cmd, &arg);
      if (request.make_request () == -1 || request.retval () == -1)
	{
	  syscall_printf ("-1 [%d] = semctl ()", request.error_code ());
	  set_errno (request.error_code ());
	  __leave;
	}
      return request.retval ();
    }
  __except (EFAULT) {}
  __endtry
  return -1;
}

extern "C" int
semget (key_t key, int nsems, int semflg)
{
  syscall_printf ("semget (key = %U, nsems = %d, semflg = %y)",
		  key, nsems, semflg);
  client_request_sem request (key, nsems, semflg);
  if (request.make_request () == -1 || request.retval () == -1)
    {
      syscall_printf ("-1 [%d] = semget ()", request.error_code ());
      set_errno (request.error_code ());
      return -1;
    }
  return request.retval ();
}

extern "C" int
semop (int semid, struct sembuf *sops, size_t nsops)
{
  syscall_printf ("semop (semid = %d, sops = %p, nsops = %ld)",
		  semid, sops, nsops);
  __try
    {
      client_request_sem request (semid, sops, nsops);
      if (request.make_request () == -1 || request.retval () == -1)
	{
	  syscall_printf ("-1 [%d] = semop ()", request.error_code ());
	  set_errno (request.error_code ());
	  __leave;
	}
      return request.retval ();
    }
  __except (EFAULT) {}
  __endtry
  return -1;
}
