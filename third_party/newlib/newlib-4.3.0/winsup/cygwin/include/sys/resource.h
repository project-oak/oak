/* sys/resource.h

This file is part of Cygwin.

This software is a copyrighted work licensed under the terms of the
Cygwin license.  Please consult the file "CYGWIN_LICENSE" for
details. */

#ifndef _SYS_RESOURCE_H_
#define _SYS_RESOURCE_H_

#include <sys/time.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Used for get/setpriority */
#define PRIO_PROCESS	0
#define PRIO_PGRP	1
#define PRIO_USER	2

#define RLIMIT_CPU	0		/* CPU time in seconds */
#define RLIMIT_FSIZE	1		/* Maximum filesize */
#define RLIMIT_DATA	2		/* max data size */
#define RLIMIT_STACK	3		/* max stack size */
#define RLIMIT_CORE	4		/* max core file size */
#define RLIMIT_NOFILE	5		/* max number of open files */
#define RLIMIT_OFILE	RLIMIT_NOFILE	/* BSD name */
#define RLIMIT_AS	6		/* address space (virt. memory) limit */

#define RLIMIT_NLIMITS  7		/* upper bound of RLIMIT_* defines */
#define RLIM_NLIMITS    RLIMIT_NLIMITS

#define RLIM_INFINITY	(~0UL)
#define RLIM_SAVED_MAX	RLIM_INFINITY
#define RLIM_SAVED_CUR	RLIM_INFINITY

typedef unsigned long rlim_t;

struct rlimit {
	rlim_t	rlim_cur;
	rlim_t	rlim_max;
};

#define	RUSAGE_SELF	0		/* calling process */
#define	RUSAGE_CHILDREN	-1		/* terminated child processes */

struct rusage {
	struct timeval ru_utime;	/* user time used */
	struct timeval ru_stime;	/* system time used */
	long ru_maxrss;
	long ru_ixrss;               /* XXX: 0 */
	long ru_idrss;               /* XXX: sum of rm_asrss */
	long ru_isrss;               /* XXX: 0 */
	long ru_minflt;              /* any page faults not requiring I/O */
	long ru_majflt;              /* any page faults requiring I/O */
	long ru_nswap;               /* swaps */
	long ru_inblock;             /* block input operations */
	long ru_oublock;             /* block output operations */
	long ru_msgsnd;              /* messages sent */
	long ru_msgrcv;              /* messages received */
	long ru_nsignals;            /* signals received */
	long ru_nvcsw;               /* voluntary context switches */
	long ru_nivcsw;              /* involuntary " */
#define ru_last         ru_nivcsw
};

int getrlimit (int __resource, struct rlimit *__rlp);
int setrlimit (int __resource, const struct rlimit *__rlp);

int getrusage (int __who, struct rusage *__rusage);

int getpriority (int which, id_t who);
int setpriority (int which, id_t who, int value);

#ifdef __cplusplus
}
#endif

#endif

