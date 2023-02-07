/* sched.cc: scheduler interface for Cygwin

   Written by Robert Collins <rbtcollins@hotmail.com>

   This file is part of Cygwin.

   This software is a copyrighted work licensed under the terms of the
   Cygwin license.  Please consult the file "CYGWIN_LICENSE" for
   details. */

#include "winsup.h"
#include "miscfuncs.h"
#include "cygerrno.h"
#include "pinfo.h"
#include "clock.h"
/* for getpid */
#include <unistd.h>
#include <sys/param.h>
#include "registry.h"

/* Win32 priority to UNIX priority Mapping. */

extern "C"
{

/* We support prio values from 1 to 32.  This is marginally in line with Linux
   (1 - 99) and matches the POSIX requirement to support at least 32 priority
   values. */

/* max priority for policy */
int
sched_get_priority_max (int policy)
{
  switch (policy)
    {
    case SCHED_FIFO:
    case SCHED_RR:
    case SCHED_OTHER:
      return 32;
    }
  set_errno (EINVAL);
  return -1;
}

/* min priority for policy */
int
sched_get_priority_min (int policy)
{
  switch (policy)
    {
    case SCHED_FIFO:
    case SCHED_RR:
    case SCHED_OTHER:
      return 1;
    }
  set_errno (EINVAL);
  return -1;
}

/* Check a scheduler parameter struct for valid settings */
bool
valid_sched_parameters (const struct sched_param *param)
{
  return param->sched_priority >= 1 && param->sched_priority <= 32;
}

/* get sched params for process

   Note, we're never returning EPERM, always ESRCH. This is by design.
   Walking the pid values is a known hole in some OSes. */
int
sched_getparam (pid_t pid, struct sched_param *param)
{
  pid_t localpid;
  if (!param || pid < 0)
    {
      set_errno (EINVAL);
      return -1;
    }

  localpid = pid ? pid : getpid ();

  DWORD pclass;
  HANDLE process;
  pinfo p (localpid);

  /* get the class */
  if (!p)
    {
      set_errno (ESRCH);
      return -1;
    }
  process = OpenProcess (PROCESS_QUERY_LIMITED_INFORMATION, FALSE,
			 p->dwProcessId);
  if (!process)
    {
      set_errno (ESRCH);
      return -1;
    }
  pclass = GetPriorityClass (process);
  CloseHandle (process);
  if (!pclass)
    {
      set_errno (ESRCH);
      return -1;
    }
  /* calculate the unix priority. */
  switch (pclass)
    {
    case IDLE_PRIORITY_CLASS:
      param->sched_priority = 3;
      break;
    case BELOW_NORMAL_PRIORITY_CLASS:
      param->sched_priority = 9;
      break;
    case NORMAL_PRIORITY_CLASS:
    default:
      param->sched_priority = 15;
      break;
    case ABOVE_NORMAL_PRIORITY_CLASS:
      param->sched_priority = 21;
      break;
    case HIGH_PRIORITY_CLASS:
      param->sched_priority = 27;
      break;
    case REALTIME_PRIORITY_CLASS:
      param->sched_priority = 32;
      break;
    }

  return 0;
}

/* get the scheduler for pid

   All process's on WIN32 run with SCHED_FIFO.  So we just give an answer.
   (WIN32 uses a multi queue FIFO).
*/
int
sched_getscheduler (pid_t pid)
{
  if (pid < 0)
    return ESRCH;
  else
    return SCHED_FIFO;
}

/* get the time quantum for pid */
int
sched_rr_get_interval (pid_t pid, struct timespec *interval)
{
  static const char quantable[2][2][3] =
    {{{12, 24, 36}, { 6, 12, 18}},
     {{36, 36, 36}, {18, 18, 18}}};
  /* FIXME: Clocktickinterval can be 15 ms for multi-processor system. */
  static const int clocktickinterval = 10;
  static const int quantapertick = 3;

  HWND forwin;
  DWORD forprocid;
  DWORD vfindex, slindex, qindex, prisep;
  long nsec;

  forwin = GetForegroundWindow ();
  if (!forwin)
    GetWindowThreadProcessId (forwin, &forprocid);
  else
    forprocid = 0;

  reg_key reg (HKEY_LOCAL_MACHINE, KEY_READ, L"SYSTEM", L"CurrentControlSet",
	       L"Control", L"PriorityControl", NULL);
  if (reg.error ())
    {
      set_errno (ESRCH);
      return -1;
    }
  prisep = reg.get_dword (L"Win32PrioritySeparation", 2);
  pinfo pi (pid ? pid : myself->pid);
  if (!pi)
    {
      set_errno (ESRCH);
      return -1;
    }

  if (pi->dwProcessId == forprocid)
    {
      qindex = prisep & 3;
      qindex = qindex == 3 ? 2 : qindex;
    }
  else
    qindex = 0;
  vfindex = ((prisep >> 2) & 3) % 3;
  if (vfindex == 0)
    vfindex = wincap.is_server () || (prisep & 3) == 0 ? 1 : 0;
  else
    vfindex -= 1;
  slindex = ((prisep >> 4) & 3) % 3;
  if (slindex == 0)
    slindex = wincap.is_server () ? 1 : 0;
  else
    slindex -= 1;

  nsec = quantable[vfindex][slindex][qindex] / quantapertick
	 * clocktickinterval * (NSPERSEC / MSPERSEC);
  interval->tv_sec = nsec / NSPERSEC;
  interval->tv_nsec = nsec % NSPERSEC;

  return 0;
}

/* set the scheduling parameters */
int
sched_setparam (pid_t pid, const struct sched_param *param)
{
  pid_t localpid;
  int pri;
  DWORD pclass;
  HANDLE process;

  if (!param || pid < 0)
    {
      set_errno (EINVAL);
      return -1;
    }

  if (!valid_sched_parameters (param))
    {
      set_errno (EINVAL);
      return -1;
    }

  pri = param->sched_priority;

  /* calculate our desired priority class.  We only reserve a small area
     (31/32) for realtime priority. */
  if (pri <= 6)
    pclass = IDLE_PRIORITY_CLASS;
  else if (pri <= 12)
    pclass = BELOW_NORMAL_PRIORITY_CLASS;
  else if (pri <= 18)
    pclass = NORMAL_PRIORITY_CLASS;
  else if (pri <= 24)
    pclass = ABOVE_NORMAL_PRIORITY_CLASS;
  else if (pri <= 30)
    pclass = HIGH_PRIORITY_CLASS;
  else
    pclass = REALTIME_PRIORITY_CLASS;

  localpid = pid ? pid : getpid ();

  pinfo p (localpid);

  /* set the class */

  if (!p)
    {
      set_errno (ESRCH);
      return -1;
    }
  process = OpenProcess (PROCESS_SET_INFORMATION, FALSE, p->dwProcessId);
  if (!process)
    {
      set_errno (ESRCH);
      return -1;
    }
  if (!SetPriorityClass (process, pclass))
    {
      CloseHandle (process);
      set_errno (EPERM);
      return -1;
    }
  CloseHandle (process);

  return 0;
}

/* POSIX thread priorities loosely compare to Windows thread base priorities.

   Base priority is a function of process priority class and thread priority.
   https://msdn.microsoft.com/en-us/library/windows/desktop/ms685100%28v=vs.85%29.aspx

   Note 1:

     We deliberately handle the REALTIME prority class the same as the HIGH
     priority class.  Realtime has it's own range from 16 to 31 so half the
     arena is reserved for REALTIME.  The problem is that this isn't visible
     nor expected in the POSIX scenario.  Therefore we hide this here and
     fold REALTIME into HIGH.

   Note 2:

     sched_get_thread_priority is only called internally and only for threads
     of the current process, with no good reason for the caller to fail.
     Therefore it never returns an error but a valid priority (base value
     equivalent to process priority class + THREAD_PRIORITY_NORMAL...

   Note 3:

     ...multiplied by 2 to stretch the priorities over the entire range 1 - 32.
*/

static int
sched_base_prio_from_win_prio_class (DWORD pclass)
{
  int base;

  switch (pclass)
    {
    case IDLE_PRIORITY_CLASS:
      base = 4;
      break;
    case BELOW_NORMAL_PRIORITY_CLASS:
      base = 6;
      break;
    case NORMAL_PRIORITY_CLASS:
    default:
      base = 8;
      break;
    case ABOVE_NORMAL_PRIORITY_CLASS:
      base = 10;
      break;
    case HIGH_PRIORITY_CLASS:
    case REALTIME_PRIORITY_CLASS: /* See above note 1 */
      base = 13;
      break;
    }
  return base;
}

int
sched_get_thread_priority (HANDLE thread)
{
  int tprio;
  DWORD pclass;
  int priority;

  tprio = GetThreadPriority (thread);
  pclass = GetPriorityClass (GetCurrentProcess ());
  switch (tprio)
    {
    case THREAD_PRIORITY_ERROR_RETURN:
      priority = sched_base_prio_from_win_prio_class (pclass);
      break;
    case THREAD_PRIORITY_IDLE:
      priority = 1;
      break;
    case THREAD_PRIORITY_TIME_CRITICAL:
      priority = 15;
      break;
    default:
      priority = tprio + sched_base_prio_from_win_prio_class (pclass);
      break;
    }
  return priority << 1; /* See above note 3 */
}

int
sched_set_thread_priority (HANDLE thread, int priority)
{
  DWORD pclass;
  int tprio;

  pclass = GetPriorityClass (GetCurrentProcess ());
  if (!pclass)
    return EPERM;
  if (priority < 1 || priority > 32)
    return EINVAL;

  priority >>= 1; /* See above note 3 */
  if (priority < 1)
    priority = 1;
  else if (priority > 15)
    priority = 15;

  if (priority == 1)
    tprio = THREAD_PRIORITY_IDLE;
  else if (priority == 15)
    tprio = THREAD_PRIORITY_TIME_CRITICAL;
  else
    {
      tprio = priority - sched_base_prio_from_win_prio_class (pclass);
      /* Intermediate values only allowed in REALTIME_PRIORITY_CLASS. */
      if (pclass != REALTIME_PRIORITY_CLASS)
	{
	  if (tprio < THREAD_PRIORITY_LOWEST)
	    tprio = THREAD_PRIORITY_LOWEST;
	  else if (tprio > THREAD_PRIORITY_HIGHEST)
	    tprio = THREAD_PRIORITY_HIGHEST;
	}
    }
  if (!SetThreadPriority (thread, tprio))
    /* invalid handle, no access are the only expected errors. */
    return EPERM;
  return 0;
}

/* set the scheduler */
int
sched_setscheduler (pid_t pid, int policy,
		    const struct sched_param *param)
{
  /* on win32, you can't change the scheduler. Doh! */
  set_errno (ENOSYS);
  return -1;
}

/* yield the cpu */
int
sched_yield ()
{
  SwitchToThread ();
  return 0;
}
EXPORT_ALIAS (sched_yield, pthread_yield)

int
sched_getcpu ()
{
  PROCESSOR_NUMBER pnum;

  GetCurrentProcessorNumberEx (&pnum);
  return pnum.Group * __get_cpus_per_group () + pnum.Number;
}

/* construct an affinity mask with just the 'count' lower-order bits set */
static __cpu_mask
groupmask (int count)
{
  if (count >= (int) (NBBY * sizeof (__cpu_mask)))
    return ~(__cpu_mask) 0;
  else
    return ((__cpu_mask) 1 << count) - 1;
}

/* return the affinity mask of the indicated group from the given cpu set */
static __cpu_mask
getgroup (size_t sizeof_set, const cpu_set_t *set, int groupnum)
{
  int groupsize = __get_cpus_per_group ();
  int bitindex = groupnum * groupsize;

  int setsize = NBBY * sizeof_set; // bit size of whole cpu set
  if (bitindex + groupsize > setsize)
    return (__cpu_mask) 0;

  int wordsize = NBBY * sizeof (cpu_set_t);
  int wordindex = bitindex / wordsize;

  __cpu_mask result = set->__bits[wordindex];
  int offset = bitindex % wordsize;
  if (offset)
    {
      result >>= offset;
      offset = wordsize - offset;
    }
  else
    offset = wordsize;

  if (offset < groupsize)
    result |= (set->__bits[wordindex + 1] << offset);
  if (groupsize < wordsize)
    result &= groupmask (groupsize);

  return result;
}

/* set the given affinity mask for indicated group within the given cpu set */
static __cpu_mask
setgroup (size_t sizeof_set, cpu_set_t *set, int groupnum, __cpu_mask aff)
{
  int groupsize = __get_cpus_per_group ();
  int bitindex = groupnum * groupsize;

  int setsize = NBBY * sizeof_set; // bit size of whole cpu set
  if (bitindex + groupsize > setsize)
    return (__cpu_mask) 0;

  int wordsize = NBBY * sizeof (cpu_set_t);
  int wordindex = bitindex / wordsize;
  int offset = bitindex % wordsize;
  __cpu_mask mask = groupmask (groupsize);
  aff &= mask;

  set->__bits[wordindex] &= ~(mask << offset);
  set->__bits[wordindex] |= aff << offset;

  if ((bitindex + groupsize - 1) / wordsize != wordindex)
    {
      offset = wordsize - offset;
      set->__bits[wordindex + 1] &= ~(mask >> offset);
      set->__bits[wordindex + 1] |= aff >> offset;
    }

  return aff;
}

/* figure out which processor group the set bits indicate; can only be one */
static int
whichgroup (size_t sizeof_set, const cpu_set_t *set)
{
  int res = -1;
  int maxgroup = min (__get_group_count (),
                      (NBBY * sizeof_set) / __get_cpus_per_group ());

  for (int i = 0; i < maxgroup; ++i)
    if (getgroup (sizeof_set, set, i))
      {
	if (res >= 0)
	  return -1; // error return if more than one group indicated
	else
	  res = i; // remember first group found
      }

  return res;
}

int
sched_get_thread_affinity (HANDLE thread, size_t sizeof_set, cpu_set_t *set)
{
  GROUP_AFFINITY ga;
  int status = 0;

  if (thread)
    {
      memset (set, 0, sizeof_set);
      if (!GetThreadGroupAffinity (thread, &ga))
	{
	  status = geterrno_from_win_error (GetLastError (), EPERM);
	  goto done;
	}
      setgroup (sizeof_set, set, ga.Group, ga.Mask);
    }
  else
    status = ESRCH;

done:
  return status;
}

int
__sched_getaffinity_sys (pid_t pid, size_t sizeof_set, cpu_set_t *set)
{
  /* Emulate Linux raw sched_getaffinity syscall for benefit of taskset(1) */
  HANDLE process = 0;
  int status = 0;

  pinfo p (pid ? pid : getpid ());
  if (p)
    {
      process = pid && pid != myself->pid ?
                OpenProcess (PROCESS_QUERY_LIMITED_INFORMATION, FALSE,
                             p->dwProcessId) : GetCurrentProcess ();
      KAFFINITY procmask;
      KAFFINITY sysmask;
      USHORT groupcount = __CPU_GROUPMAX;
      USHORT grouparray[__CPU_GROUPMAX];

      if (!GetProcessAffinityMask (process, &procmask, &sysmask))
        {
          status = geterrno_from_win_error (GetLastError (), EPERM);
          goto done;
        }
      memset (set, 0, sizeof_set);
      if (!GetProcessGroupAffinity (process, &groupcount, grouparray))
	{
	  status = geterrno_from_win_error (GetLastError (), EPERM);
	  goto done;
	}

      KAFFINITY miscmask = groupmask (__get_cpus_per_group ());
      for (int i = 0; i < groupcount; i++)
	setgroup (sizeof_set, set, grouparray[i], miscmask);
    }
  else
    status = ESRCH;

done:
  if (process && process != GetCurrentProcess ())
    CloseHandle (process);

  if (status)
    {
      set_errno (status);
      return -1;
    }

  /* On successful return, we would ordinarily return 0, but instead we
     emulate the behavior of the raw sched_getaffinity syscall on Linux. */
  return min (sizeof_set, sizeof (cpu_set_t));
}

int
sched_getaffinity (pid_t pid, size_t sizeof_set, cpu_set_t *set)
{
  /* Emulate the Linux glibc interface of sched_getaffinity() by calling
     the raw syscall emulation and mapping positive results to 0. */
  int status = __sched_getaffinity_sys (pid, sizeof_set, set);
  return status > 0 ? 0 : status;
}

int
sched_set_thread_affinity (HANDLE thread, size_t sizeof_set, const cpu_set_t *set)
{
  GROUP_AFFINITY ga;
  int group = whichgroup (sizeof_set, set);
  int status = 0;

  if (thread)
    {
      if (group < 0)
	{
	  status = EINVAL;
	  goto done;
	}
      memset (&ga, 0, sizeof (ga));
      ga.Mask = getgroup (sizeof_set, set, group);
      ga.Group = group;
      if (!SetThreadGroupAffinity (thread, &ga, NULL))
	{
	  status = geterrno_from_win_error (GetLastError (), EPERM);
	  goto done;
	}
    }
  else
    status = ESRCH;

done:
  return status;
}

int
sched_setaffinity (pid_t pid, size_t sizeof_set, const cpu_set_t *set)
{
  USHORT groupcount = __CPU_GROUPMAX;
  USHORT grouparray[__CPU_GROUPMAX];
  int group = whichgroup (sizeof_set, set);
  HANDLE process = 0;
  int status = 0;

  pinfo p (pid ? pid : getpid ());
  if (p)
    {
      process = pid && pid != myself->pid ?
		OpenProcess (PROCESS_SET_INFORMATION, FALSE,
			     p->dwProcessId) : GetCurrentProcess ();
      if (!GetProcessGroupAffinity (process, &groupcount, grouparray))
	{
	  status = geterrno_from_win_error (GetLastError (), EPERM);
	  goto done;
	}
      if (group < 0)
	{
	  status = EINVAL;
	  goto done;
	}
      if (groupcount == 1 && grouparray[0] == group)
	{
	  if (!SetProcessAffinityMask (process, getgroup (sizeof_set, set, group)))
	    status = geterrno_from_win_error (GetLastError (), EPERM);
	  goto done;
	}

      /* If we get here, the user is trying to add the process to another
	 group or move it from current group to another group.  These ops
	 are not allowed by Windows.  One has to move one or more of the
	 process' threads to the new group(s) one by one.  Here, we bail.
      */
      status = EINVAL;
      goto done;
    }
  else
    status = ESRCH;

done:
  if (process && process != GetCurrentProcess ())
    CloseHandle (process);

  if (status)
    {
      set_errno (status);
      return -1;
    }

  return 0;
}

} /* extern C */
