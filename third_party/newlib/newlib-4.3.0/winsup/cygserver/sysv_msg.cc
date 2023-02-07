/*
 * Implementation of SVID messages
 *
 * Author:  Daniel Boulet
 *
 * Copyright 1993 Daniel Boulet and RTMX Inc.
 *
 * This system call was implemented by Daniel Boulet under contract from RTMX.
 *
 * Redistribution and use in source forms, with and without modification,
 * are permitted provided that this entire comment appears intact.
 *
 * Redistribution in binary form may occur without any restrictions.
 * Obviously, it would be nice if you gave credit where credit is due
 * but requiring it would be too onerous.
 *
 * This software is provided ``AS IS'' without any warranties of any kind.
 */

/*
 * This file is heavily changed to become part of Cygwin's cygserver.
 */

#ifdef __OUTSIDE_CYGWIN__
#include "woutsup.h"
#include <sys/cdefs.h>
#ifndef __FBSDID
#define __FBSDID(s)	const char version[] = (s)
#endif
__FBSDID("$FreeBSD: /usr/local/www/cvsroot/FreeBSD/src/sys/kern/sysv_msg.c,v 1.52 2003/11/07 04:47:14 rwatson Exp $");
/* CV, 2006-01-09: Inspected upstream up to version 1.60. */

#define _KERNEL 1
#define __BSD_VISIBLE 1
#include <sys/types.h>
#include <sys/sysproto.h>
#include <sys/ipc.h>
#include <sys/param.h>
#include <sys/msg.h>
#include <malloc.h>
#include <errno.h>
#include <time.h>
#include "cygserver.h"
#include "process.h"
#include "cygserver_ipc.h"

#ifdef __CYGWIN__
#define MSG_DEBUG
#endif /* __CYGWIN__ */

#ifdef MSG_DEBUG
#define DPRINTF(a)	debug a
#else
#define DPRINTF(a)
#endif

static void msg_freehdr(struct msg *msghdr);

#ifndef __CYGWIN__
int msgctl(struct thread *, struct msgctl_args *);
int msgget(struct thread *, struct msgget_args *);
int msgsnd(struct thread *, struct msgsnd_args *);
int msgrcv(struct thread *, struct msgrcv_args *);

static sy_call_t *msgcalls[] = {
	(sy_call_t *)msgctl, (sy_call_t *)msgget,
	(sy_call_t *)msgsnd, (sy_call_t *)msgrcv
};
#endif /* __CYGWIN__ */


struct msg {
	struct	msg *msg_next;	/* next msg in the chain */
	long	msg_type;	/* type of this message */
    				/* >0 -> type of this message */
    				/* 0 -> free header */
	u_short	msg_ts;		/* size of this message */
	short	msg_spot;	/* location of start of msg in buffer */
};


#ifndef MSGSSZ
#define MSGSSZ	8		/* Each segment must be 2^N long */
#endif
#ifndef MSGSEG
#define MSGSEG	2048		/* must be less than 32767 */
#endif
#define MSGMAX	(MSGSSZ*MSGSEG)
#ifndef MSGMNB
#define MSGMNB	2048		/* max # of bytes in a queue */
#endif
#ifndef MSGMNI
#define MSGMNI	40
#endif
#ifndef MSGTQL
#define MSGTQL	40
#endif

/*
 * Based on the configuration parameters described in an SVR2 (yes, two)
 * config(1m) man page.
 *
 * Each message is broken up and stored in segments that are msgssz bytes
 * long.  For efficiency reasons, this should be a power of two.  Also,
 * it doesn't make sense if it is less than 8 or greater than about 256.
 * Consequently, msginit in kern/sysv_msg.c checks that msgssz is a power of
 * two between 8 and 1024 inclusive (and panic's if it isn't).
 */
struct msginfo msginfo = {
                MSGMAX,         /* max chars in a message */
                MSGMNB,         /* max chars in a queue */
                MSGMNI,         /* # of message queue identifiers */
                MSGTQL,         /* max messages in system */
                MSGSSZ,         /* size of a message segment */
                		/* (must be small power of 2 greater than 4) */
                MSGSEG          /* number of message segments */
};

/*
 * macros to convert between msqid_ds's and msqid's.
 * (specific to this implementation)
 */
#define MSQID(ix,ds)	((ix) & 0xffff | (((ds).msg_perm.seq << 16) & 0xffff0000))
#define MSQID_IX(id)	((id) & 0xffff)
#define MSQID_SEQ(id)	(((id) >> 16) & 0xffff)

/*
 * The rest of this file is specific to this particular implementation.
 */

struct msgmap {
	short	next;		/* next segment in buffer */
    				/* -1 -> available */
    				/* 0..(MSGSEG-1) -> index of next segment */
};

#define MSG_LOCKED	01000	/* Is this msqid_ds locked? */

static int nfree_msgmaps;	/* # of free map entries */
static short free_msgmaps;	/* head of linked list of free map entries */
static struct msg *free_msghdrs;/* list of free msg headers */
static char *msgpool;		/* MSGMAX byte long msg buffer pool */
static struct msgmap *msgmaps;	/* MSGSEG msgmap structures */
static struct msg *msghdrs;	/* MSGTQL msg headers */
static struct msqid_ds *msqids;	/* MSGMNI msqid_ds struct's */
static struct mtx msq_mtx;	/* global mutex for message queues. */

#ifdef __CYGWIN__
static struct msg_info msg_info;
#endif /* __CYGWIN__ */

void
msginit()
{
	int i;

	TUNABLE_INT_FETCH("kern.ipc.msgseg", &msginfo.msgseg);
	TUNABLE_INT_FETCH("kern.ipc.msgssz", &msginfo.msgssz);
	msginfo.msgmax = msginfo.msgseg * msginfo.msgssz;
	TUNABLE_INT_FETCH("kern.ipc.msgmnb", &msginfo.msgmnb);
	TUNABLE_INT_FETCH("kern.ipc.msgmni", &msginfo.msgmni);
	TUNABLE_INT_FETCH("kern.ipc.msgtql", &msginfo.msgtql);

	msgpool = (char *) sys_malloc(msginfo.msgmax, M_MSG, M_WAITOK);
	if (msgpool == NULL)
		panic("msgpool is NULL");
	msgmaps = (msgmap *) sys_malloc(sizeof(struct msgmap) * msginfo.msgseg, M_MSG, M_WAITOK);
	if (msgmaps == NULL)
		panic("msgmaps is NULL");
	msghdrs = (msg *) sys_malloc(sizeof(struct msg) * msginfo.msgtql, M_MSG, M_WAITOK);
	if (msghdrs == NULL)
		panic("msghdrs is NULL");
	msqids = (msqid_ds *) sys_malloc(sizeof(struct msqid_ds) * msginfo.msgmni, M_MSG, M_WAITOK);
	if (msqids == NULL)
		panic("msqids is NULL");

	/*
	 * msginfo.msgssz should be a power of two for efficiency reasons.
	 * It is also pretty silly if msginfo.msgssz is less than 8
	 * or greater than about 256 so ...
	 */

	i = 8;
	while (i < 1024 && i != msginfo.msgssz)
		i <<= 1;
    	if (i != msginfo.msgssz) {
		DPRINTF(("msginfo.msgssz=%d (0x%x)\n", msginfo.msgssz,
		    msginfo.msgssz));
		panic("msginfo.msgssz not a small power of 2");
	}

	if (msginfo.msgseg > 32767) {
		DPRINTF(("msginfo.msgseg=%d\n", msginfo.msgseg));
		panic("msginfo.msgseg > 32767");
	}

	if (msgmaps == NULL)
		panic("msgmaps is NULL");

	for (i = 0; i < msginfo.msgseg; i++) {
		if (i > 0)
			msgmaps[i-1].next = i;
		msgmaps[i].next = -1;	/* implies entry is available */
	}
	free_msgmaps = 0;
	nfree_msgmaps = msginfo.msgseg;

	if (msghdrs == NULL)
		panic("msghdrs is NULL");

	for (i = 0; i < msginfo.msgtql; i++) {
		msghdrs[i].msg_type = 0;
		if (i > 0)
			msghdrs[i-1].msg_next = &msghdrs[i];
		msghdrs[i].msg_next = NULL;
    	}
	free_msghdrs = &msghdrs[0];

	if (msqids == NULL)
		panic("msqids is NULL");

	for (i = 0; i < msginfo.msgmni; i++) {
		msqids[i].msg_qbytes = 0;	/* implies entry is available */
		msqids[i].msg_perm.seq = 0;	/* reset to a known value */
		msqids[i].msg_perm.mode = 0;
	}
	mtx_init(&msq_mtx, "msq", NULL, MTX_DEF);
}

int
msgunload()
{
	struct msqid_ds *msqptr;
	int msqid;

	for (msqid = 0; msqid < msginfo.msgmni; msqid++) {
		/*
		 * Look for an unallocated and unlocked msqid_ds.
		 * msqid_ds's can be locked by msgsnd or msgrcv while
		 * they are copying the message in/out.  We can't
		 * re-use the entry until they release it.
		 */
		msqptr = &msqids[msqid];
		if (msqptr->msg_qbytes != 0 ||
		    (msqptr->msg_perm.mode & MSG_LOCKED) != 0)
			break;
	}
#ifndef __CYGWIN__
	if (msqid != msginfo.msgmni)
		return (EBUSY);
#endif /* __CYGWIN__ */

	sys_free(msgpool, M_MSG);
	sys_free(msgmaps, M_MSG);
	sys_free(msghdrs, M_MSG);
	sys_free(msqids, M_MSG);
	mtx_destroy(&msq_mtx);
	return (0);
}


#ifndef __CYGWIN__
static int
sysvmsg_modload(struct module *module, int cmd, void *arg)
{
	int error = 0;

	switch (cmd) {
	case MOD_LOAD:
		msginit();
		break;
	case MOD_UNLOAD:
		error = msgunload();
		break;
	case MOD_SHUTDOWN:
		break;
	default:
		error = EINVAL;
		break;
	}
	return (error);
}

static moduledata_t sysvmsg_mod = {
	"sysvmsg",
	&sysvmsg_modload,
	NULL
};

SYSCALL_MODULE_HELPER(msgsys);
SYSCALL_MODULE_HELPER(msgctl);
SYSCALL_MODULE_HELPER(msgget);
SYSCALL_MODULE_HELPER(msgsnd);
SYSCALL_MODULE_HELPER(msgrcv);

DECLARE_MODULE(sysvmsg, sysvmsg_mod,
	SI_SUB_SYSV_MSG, SI_ORDER_FIRST);
MODULE_VERSION(sysvmsg, 1);

/*
 * Entry point for all MSG calls
 *
 * MPSAFE
 */
int
msgsys(thread *td, struct msgsys_args *uap)
{
	int error;

	if (!jail_sysvipc_allowed && jailed(td->td_ucred))
		return (ENOSYS);
	if (uap->which < 0 ||
	    (unsigned) uap->which >= sizeof(msgcalls)/sizeof(msgcalls[0]))
		return (EINVAL);
	error = (*msgcalls[uap->which])(td, &uap->a2);
	return (error);
}
#endif

static void
msg_freehdr(struct msg *msghdr)
{
	while (msghdr->msg_ts > 0) {
		short next;
		if (msghdr->msg_spot < 0 || msghdr->msg_spot >= msginfo.msgseg)
			panic("msghdr->msg_spot out of range");
		next = msgmaps[msghdr->msg_spot].next;
		msgmaps[msghdr->msg_spot].next = free_msgmaps;
		free_msgmaps = msghdr->msg_spot;
		nfree_msgmaps++;
		msghdr->msg_spot = next;
		if (msghdr->msg_ts >= msginfo.msgssz)
			msghdr->msg_ts -= msginfo.msgssz;
		else
			msghdr->msg_ts = 0;
	}
	if (msghdr->msg_spot != -1)
		panic("msghdr->msg_spot != -1");
	msghdr->msg_next = free_msghdrs;
	free_msghdrs = msghdr;
}

#ifndef _SYS_SYSPROTO_H_
struct msgctl_args {
	int	msqid;
	int	cmd;
	struct	msqid_ds *buf;
};
#endif

/*
 * MPSAFE
 */
int
msgctl(struct thread *td, struct msgctl_args *uap)
{
	int msqid = uap->msqid;
	int cmd = uap->cmd;
	struct msqid_ds *user_msqptr = uap->buf;
	int rval, error;
	struct msqid_ds msqbuf;
	struct msqid_ds *msqptr;

	DPRINTF(("call to msgctl(%d, %d, 0x%x)\n", msqid, cmd, user_msqptr));

	if (!jail_sysvipc_allowed && jailed(td->td_ucred))
		return (ENOSYS);

#ifdef __CYGWIN__
	if (cmd == IPC_INFO) {
		if (!msqid) {
			error = copyout(&msginfo, user_msqptr,
					sizeof(struct msginfo));
			td->td_retval[0] = error ? -1 : 0;
			return (error);
		}
		if (msqid > msginfo.msgmni)
			msqid = msginfo.msgmni;
		error = copyout(msqids, user_msqptr,
				msqid * sizeof(struct msqid_ds));
		td->td_retval[0] = error ? -1 : 0;
		return (error);
	} else if (cmd == MSG_INFO) {
		mtx_lock(&msq_mtx);
		error = copyout(&msg_info, user_msqptr,
				sizeof(struct msg_info));
		td->td_retval[0] = error ? -1 : 0;
		mtx_unlock(&msq_mtx);
		return (error);
	}
#endif /* __CYGWIN__ */
	msqid = IPCID_TO_IX(msqid);

	if (msqid < 0 || msqid >= msginfo.msgmni) {
		DPRINTF(("msqid (%d) out of range (0<=msqid<%d)\n", msqid,
		    msginfo.msgmni));
		return (EINVAL);
	}
	if (cmd == IPC_SET &&
	    (error = copyin(user_msqptr, &msqbuf, sizeof(msqbuf))) != 0)
		return (error);

	msqptr = &msqids[msqid];

	mtx_lock(&msq_mtx);
	if (msqptr->msg_qbytes == 0) {
		DPRINTF(("no such msqid\n"));
		error = EINVAL;
		goto done2;
	}
	if (msqptr->msg_perm.seq != IPCID_TO_SEQ(uap->msqid)) {
		DPRINTF(("wrong sequence number\n"));
		error = EINVAL;
		goto done2;
	}

	error = 0;
	rval = 0;

	switch (cmd) {

	case IPC_RMID:
	{
		struct msg *msghdr;
		if ((error = ipcperm(td, &msqptr->msg_perm, IPC_M)))
			goto done2;
		/* Free the message headers */
		msghdr = msqptr->msg_first;
		while (msghdr != NULL) {
			struct msg *msghdr_tmp;

			/* Free the segments of each message */
			msqptr->msg_cbytes -= msghdr->msg_ts;
			msqptr->msg_qnum--;
			msghdr_tmp = msghdr;
			msghdr = msghdr->msg_next;
			msg_freehdr(msghdr_tmp);
		}

		if (msqptr->msg_cbytes != 0)
			panic("msg_cbytes is screwed up");
		if (msqptr->msg_qnum != 0)
			panic("msg_qnum is screwed up");

		msqptr->msg_qbytes = 0;	/* Mark it as free */
#ifdef __CYGWIN__
		msg_info.msg_ids--;
#endif /* __CYGWIN__ */

		wakeup(msqptr);
	}

		break;

	case IPC_SET:
		if ((error = ipcperm(td, &msqptr->msg_perm, IPC_M)))
			goto done2;
		if (msqbuf.msg_qbytes > msqptr->msg_qbytes) {
			error = suser(td);
			if (error)
				goto done2;
		}
		if (msqbuf.msg_qbytes > (unsigned long) msginfo.msgmnb) {
			DPRINTF(("can't increase msg_qbytes beyond %d"
			    "(truncating)\n", msginfo.msgmnb));
			msqbuf.msg_qbytes = msginfo.msgmnb;	/* silently restrict qbytes to system limit */
		}
		if (msqbuf.msg_qbytes == 0) {
			DPRINTF(("can't reduce msg_qbytes to 0\n"));
			error = EINVAL;		/* non-standard errno! */
			goto done2;
		}
		msqptr->msg_perm.uid = msqbuf.msg_perm.uid;	/* change the owner */
		msqptr->msg_perm.gid = msqbuf.msg_perm.gid;	/* change the owner */
		msqptr->msg_perm.mode = (msqptr->msg_perm.mode & ~0777) |
		    (msqbuf.msg_perm.mode & 0777);
		msqptr->msg_qbytes = msqbuf.msg_qbytes;
		msqptr->msg_ctime = time (NULL);
		break;

	case IPC_STAT:
		if ((error = ipcperm(td, &msqptr->msg_perm, IPC_R))) {
			DPRINTF(("requester doesn't have read access\n"));
			goto done2;
		}
		break;

	default:
		DPRINTF(("invalid command %d\n", cmd));
		error = EINVAL;
		goto done2;
	}

	if (error == 0)
		td->td_retval[0] = rval;
done2:
	mtx_unlock(&msq_mtx);
	if (cmd == IPC_STAT && error == 0)
		error = copyout(msqptr, user_msqptr, sizeof(struct msqid_ds));
	return(error);
}

#ifndef _SYS_SYSPROTO_H_
struct msgget_args {
	key_t	key;
	int	msgflg;
};
#endif

/*
 * MPSAFE
 */
int
msgget(struct thread *td, struct msgget_args *uap)
{
	int msqid, error = 0;
	key_t key = uap->key;
	unsigned msgflg = uap->msgflg;
	struct msqid_ds *msqptr = NULL;

	DPRINTF(("msgget(0x%x, 0%o)\n", key, msgflg));

	if (!jail_sysvipc_allowed && jailed(td->td_ucred))
		return (ENOSYS);

	mtx_lock(&msq_mtx);
	if (key != IPC_PRIVATE) {
		for (msqid = 0; msqid < msginfo.msgmni; msqid++) {
			msqptr = &msqids[msqid];
			if (msqptr->msg_qbytes != 0 &&
			    msqptr->msg_perm.key == key)
				break;
		}
		if (msqid < msginfo.msgmni) {
			DPRINTF(("found public key\n"));
			if ((msgflg & IPC_CREAT) && (msgflg & IPC_EXCL)) {
				DPRINTF(("not exclusive\n"));
				error = EEXIST;
				goto done2;
			}
			if ((error = ipcperm(td, &msqptr->msg_perm, msgflg & 0700))) {
				DPRINTF(("requester doesn't have 0%o access\n",
				    msgflg & 0700));
				goto done2;
			}
			goto found;
		}
	}

	DPRINTF(("need to allocate the msqid_ds\n"));
	if (key == IPC_PRIVATE || (msgflg & IPC_CREAT)) {
		for (msqid = 0; msqid < msginfo.msgmni; msqid++) {
			/*
			 * Look for an unallocated and unlocked msqid_ds.
			 * msqid_ds's can be locked by msgsnd or msgrcv while
			 * they are copying the message in/out.  We can't
			 * re-use the entry until they release it.
			 */
			msqptr = &msqids[msqid];
			if (msqptr->msg_qbytes == 0 &&
			    (msqptr->msg_perm.mode & MSG_LOCKED) == 0)
				break;
		}
		if (msqid == msginfo.msgmni) {
			DPRINTF(("no more msqid_ds's available\n"));
			error = ENOSPC;
			goto done2;
		}
		DPRINTF(("msqid %d is available\n", msqid));
		msqptr->msg_perm.key = key;
#ifdef __CYGWIN__
		msqptr->msg_perm.cuid = td->ipcblk->uid;
		msqptr->msg_perm.uid = td->ipcblk->uid;
		msqptr->msg_perm.cgid = td->ipcblk->gid;
		msqptr->msg_perm.gid = td->ipcblk->gid;
#else
		msqptr->msg_perm.cuid = cred->cr_uid;
		msqptr->msg_perm.uid = cred->cr_uid;
		msqptr->msg_perm.cgid = cred->cr_gid;
		msqptr->msg_perm.gid = cred->cr_gid;
#endif /* __CYGWIN__ */
		msqptr->msg_perm.mode = (msgflg & 0777);
		/* Make sure that the returned msqid is unique */
		msqptr->msg_perm.seq = (msqptr->msg_perm.seq + 1) & 0x7fff;
		msqptr->msg_first = NULL;
		msqptr->msg_last = NULL;
		msqptr->msg_cbytes = 0;
		msqptr->msg_qnum = 0;
		msqptr->msg_qbytes = msginfo.msgmnb;
		msqptr->msg_lspid = 0;
		msqptr->msg_lrpid = 0;
		msqptr->msg_stime = 0;
		msqptr->msg_rtime = 0;
		msqptr->msg_ctime = time (NULL);
#ifdef __CYGWIN__
		msg_info.msg_ids++;
#endif /* __CYGWIN__ */
	} else {
		DPRINTF(("didn't find it and wasn't asked to create it\n"));
		error = ENOENT;
		goto done2;
	}

found:
	/* Construct the unique msqid */
	td->td_retval[0] = IXSEQ_TO_IPCID(msqid, msqptr->msg_perm);
done2:
	mtx_unlock(&msq_mtx);
	return (error);
}

#ifndef _SYS_SYSPROTO_H_
struct msgsnd_args {
	int	msqid;
	const void	*msgp;
	size_t	msgsz;
	int	msgflg;
};
#endif

/*
 * MPSAFE
 */
int
msgsnd(struct thread *td, struct msgsnd_args *uap)
{
	int msqid = uap->msqid;
	const void *user_msgp = uap->msgp;
	size_t msgsz = uap->msgsz;
	int msgflg = uap->msgflg;
	int segs_needed, error = 0;
	struct msqid_ds *msqptr;
	struct msg *msghdr;
	short next;

	DPRINTF(("call to msgsnd(%d, 0x%x, %d, %d)\n", msqid, user_msgp, msgsz,
	    msgflg));

	if (!jail_sysvipc_allowed && jailed(td->td_ucred))
		return (ENOSYS);

	mtx_lock(&msq_mtx);
	msqid = IPCID_TO_IX(msqid);

	if (msqid < 0 || msqid >= msginfo.msgmni) {
		DPRINTF(("msqid (%d) out of range (0<=msqid<%d)\n", msqid,
		    msginfo.msgmni));
		error = EINVAL;
		goto done2;
	}

	msqptr = &msqids[msqid];
	if (msqptr->msg_qbytes == 0) {
		DPRINTF(("no such message queue id\n"));
		error = EINVAL;
		goto done2;
	}
	if (msqptr->msg_perm.seq != IPCID_TO_SEQ(uap->msqid)) {
		DPRINTF(("wrong sequence number\n"));
		error = EINVAL;
		goto done2;
	}

	if ((error = ipcperm(td, &msqptr->msg_perm, IPC_W))) {
		DPRINTF(("requester doesn't have write access\n"));
		goto done2;
	}

	segs_needed = (msgsz + msginfo.msgssz - 1) / msginfo.msgssz;
	DPRINTF(("msgsz=%d, msgssz=%d, segs_needed=%d\n", msgsz, msginfo.msgssz,
	    segs_needed));
	for (;;) {
		int need_more_resources = 0;

		/*
		 * check msgsz
		 * (inside this loop in case msg_qbytes changes while we sleep)
		 */

		if (msgsz > msqptr->msg_qbytes) {
			DPRINTF(("msgsz > msqptr->msg_qbytes\n"));
			error = EINVAL;
			goto done2;
		}

		if (msqptr->msg_perm.mode & MSG_LOCKED) {
			DPRINTF(("msqid is locked\n"));
			need_more_resources = 1;
		}
		if (msgsz + msqptr->msg_cbytes > msqptr->msg_qbytes) {
			DPRINTF(("msgsz + msg_cbytes > msg_qbytes\n"));
			need_more_resources = 1;
		}
		if (segs_needed > nfree_msgmaps) {
			DPRINTF(("segs_needed > nfree_msgmaps\n"));
			need_more_resources = 1;
		}
		if (free_msghdrs == NULL) {
			DPRINTF(("no more msghdrs\n"));
			need_more_resources = 1;
		}

		if (need_more_resources) {
			int we_own_it;

			if ((msgflg & IPC_NOWAIT) != 0) {
				DPRINTF(("need more resources but caller "
				    "doesn't want to wait\n"));
				error = EAGAIN;
				goto done2;
			}

			if ((msqptr->msg_perm.mode & MSG_LOCKED) != 0) {
				DPRINTF(("we don't own the msqid_ds\n"));
				we_own_it = 0;
			} else {
				/* Force later arrivals to wait for our
				   request */
				DPRINTF(("we own the msqid_ds\n"));
				msqptr->msg_perm.mode |= MSG_LOCKED;
				we_own_it = 1;
			}
			DPRINTF(("goodnight\n"));
			error = msleep(msqptr, &msq_mtx, (PZERO - 4) | PCATCH,
			    "msgsnd", 50);
			DPRINTF(("good morning, error=%d\n", error));
			if (we_own_it)
				msqptr->msg_perm.mode &= ~MSG_LOCKED;
			if (error == EWOULDBLOCK) {
				DPRINTF(("timed out\n"));
				continue;
			}
			if (error != 0) {
				DPRINTF(("msgsnd:  interrupted system call\n"));
#ifdef __CYGWIN__
			  if (error == EIDRM)
                              goto done2;
#endif /* __CYGWIN__ */
				error = EINTR;
				goto done2;
			}

			/*
			 * Make sure that the msq queue still exists
			 */

			if (msqptr->msg_qbytes == 0) {
				DPRINTF(("msqid deleted\n"));
				error = EIDRM;
				goto done2;
			}

		} else {
			DPRINTF(("got all the resources that we need\n"));
			break;
		}
	}

	/*
	 * We have the resources that we need.
	 * Make sure!
	 */

	if (msqptr->msg_perm.mode & MSG_LOCKED)
		panic("msg_perm.mode & MSG_LOCKED");
	if (segs_needed > nfree_msgmaps)
		panic("segs_needed > nfree_msgmaps");
	if (msgsz + msqptr->msg_cbytes > msqptr->msg_qbytes)
		panic("msgsz + msg_cbytes > msg_qbytes");
	if (free_msghdrs == NULL)
		panic("no more msghdrs");

	/*
	 * Re-lock the msqid_ds in case we page-fault when copying in the
	 * message
	 */

	if ((msqptr->msg_perm.mode & MSG_LOCKED) != 0)
		panic("msqid_ds is already locked");
	msqptr->msg_perm.mode |= MSG_LOCKED;

	/*
	 * Allocate a message header
	 */

	msghdr = free_msghdrs;
	free_msghdrs = msghdr->msg_next;
	msghdr->msg_spot = -1;
	msghdr->msg_ts = msgsz;

	/*
	 * Allocate space for the message
	 */

	while (segs_needed > 0) {
		if (nfree_msgmaps <= 0)
			panic("not enough msgmaps");
		if (free_msgmaps == -1)
			panic("nil free_msgmaps");
		next = free_msgmaps;
		if (next <= -1)
			panic("next too low #1");
		if (next >= msginfo.msgseg)
			panic("next out of range #1");
		DPRINTF(("allocating segment %d to message\n", next));
		free_msgmaps = msgmaps[next].next;
		nfree_msgmaps--;
		msgmaps[next].next = msghdr->msg_spot;
		msghdr->msg_spot = next;
		segs_needed--;
	}

	/*
	 * Copy in the message type
	 */

	mtx_unlock(&msq_mtx);
	if ((error = copyin(user_msgp, &msghdr->msg_type,
	    sizeof(msghdr->msg_type))) != 0) {
		mtx_lock(&msq_mtx);
		DPRINTF(("error %d copying the message type\n", error));
		msg_freehdr(msghdr);
		msqptr->msg_perm.mode &= ~MSG_LOCKED;
		wakeup(msqptr);
		goto done2;
	}
	mtx_lock(&msq_mtx);
	user_msgp = (const char *)user_msgp + sizeof(msghdr->msg_type);

	/*
	 * Validate the message type
	 */

	if (msghdr->msg_type < 1) {
		msg_freehdr(msghdr);
		msqptr->msg_perm.mode &= ~MSG_LOCKED;
		wakeup(msqptr);
		DPRINTF(("mtype (%d) < 1\n", msghdr->msg_type));
		error = EINVAL;
		goto done2;
	}

	/*
	 * Copy in the message body
	 */

	next = msghdr->msg_spot;
	while (msgsz > 0) {
		size_t tlen;
		if (msgsz > (unsigned long) msginfo.msgssz)
			tlen = msginfo.msgssz;
		else
			tlen = msgsz;
		if (next <= -1)
			panic("next too low #2");
		if (next >= msginfo.msgseg)
			panic("next out of range #2");
		mtx_unlock(&msq_mtx);
		if ((error = copyin(user_msgp, &msgpool[next * msginfo.msgssz],
		    tlen)) != 0) {
			mtx_lock(&msq_mtx);
			DPRINTF(("error %d copying in message segment\n",
			    error));
			msg_freehdr(msghdr);
			msqptr->msg_perm.mode &= ~MSG_LOCKED;
			wakeup(msqptr);
			goto done2;
		}
		mtx_lock(&msq_mtx);
		msgsz -= tlen;
		user_msgp = (const char *)user_msgp + tlen;
		next = msgmaps[next].next;
	}
	if (next != -1)
		panic("didn't use all the msg segments");

	/*
	 * We've got the message.  Unlock the msqid_ds.
	 */

	msqptr->msg_perm.mode &= ~MSG_LOCKED;

	/*
	 * Make sure that the msqid_ds is still allocated.
	 */

	if (msqptr->msg_qbytes == 0) {
		msg_freehdr(msghdr);
		wakeup(msqptr);
		error = EIDRM;
		goto done2;
	}

	/*
	 * Put the message into the queue
	 */

	if (msqptr->msg_first == NULL) {
		msqptr->msg_first = msghdr;
		msqptr->msg_last = msghdr;
	} else {
		msqptr->msg_last->msg_next = msghdr;
		msqptr->msg_last = msghdr;
	}
	msqptr->msg_last->msg_next = NULL;

	msqptr->msg_cbytes += msghdr->msg_ts;
	msqptr->msg_qnum++;
	msqptr->msg_lspid = td->td_proc->p_pid;
	msqptr->msg_stime = time (NULL);

#ifdef __CYGWIN__
	msg_info.msg_num++;
	msg_info.msg_tot += uap->msgsz;
#endif /* __CYGWIN__ */

	wakeup(msqptr);
	td->td_retval[0] = 0;
done2:
	mtx_unlock(&msq_mtx);
	return (error);
}

#ifndef _SYS_SYSPROTO_H_
struct msgrcv_args {
	int	msqid;
	void	*msgp;
	size_t	msgsz;
	long	msgtyp;
	int	msgflg;
};
#endif

/*
 * MPSAFE
 */
int
msgrcv(struct thread *td, struct msgrcv_args *uap)
{
	int msqid = uap->msqid;
	void *user_msgp = uap->msgp;
	size_t msgsz = uap->msgsz;
	long msgtyp = uap->msgtyp;
	int msgflg = uap->msgflg;
	size_t len;
	struct msqid_ds *msqptr;
	struct msg *msghdr;
	int error = 0;
	short next;

	DPRINTF(("call to msgrcv(%d, 0x%x, %d, %ld, %d)\n", msqid, user_msgp,
	    msgsz, msgtyp, msgflg));

	if (!jail_sysvipc_allowed && jailed(td->td_ucred))
		return (ENOSYS);

	msqid = IPCID_TO_IX(msqid);

	if (msqid < 0 || msqid >= msginfo.msgmni) {
		DPRINTF(("msqid (%d) out of range (0<=msqid<%d)\n", msqid,
		    msginfo.msgmni));
		return (EINVAL);
	}

	msqptr = &msqids[msqid];
	mtx_lock(&msq_mtx);
	if (msqptr->msg_qbytes == 0) {
		DPRINTF(("no such message queue id\n"));
		error = EINVAL;
		goto done2;
	}
	if (msqptr->msg_perm.seq != IPCID_TO_SEQ(uap->msqid)) {
		DPRINTF(("wrong sequence number\n"));
		error = EINVAL;
		goto done2;
	}

	if ((error = ipcperm(td, &msqptr->msg_perm, IPC_R))) {
		DPRINTF(("requester doesn't have read access\n"));
		goto done2;
	}

	msghdr = NULL;
	while (msghdr == NULL) {
		if (msgtyp == 0) {
			msghdr = msqptr->msg_first;
			if (msghdr != NULL) {
				if (msgsz < msghdr->msg_ts &&
				    (msgflg & MSG_NOERROR) == 0) {
					DPRINTF(("first message on the queue "
					    "is too big (want %d, got %d)\n",
					    msgsz, msghdr->msg_ts));
					error = E2BIG;
					goto done2;
				}
				if (msqptr->msg_first == msqptr->msg_last) {
					msqptr->msg_first = NULL;
					msqptr->msg_last = NULL;
				} else {
					msqptr->msg_first = msghdr->msg_next;
					if (msqptr->msg_first == NULL)
						panic("msg_first/last screwed up #1");
				}
			}
		} else {
			struct msg *previous;
			struct msg **prev;

			previous = NULL;
			prev = &(msqptr->msg_first);
			while ((msghdr = *prev) != NULL) {
				/*
				 * Is this message's type an exact match or is
				 * this message's type less than or equal to
				 * the absolute value of a negative msgtyp?
				 * Note that the second half of this test can
				 * NEVER be true if msgtyp is positive since
				 * msg_type is always positive!
				 */

				if (msgtyp == msghdr->msg_type ||
				    msghdr->msg_type <= -msgtyp) {
					DPRINTF(("found message type %d, "
					    "requested %d\n",
					    msghdr->msg_type, msgtyp));
					if (msgsz < msghdr->msg_ts &&
					    (msgflg & MSG_NOERROR) == 0) {
						DPRINTF(("requested message "
						    "on the queue is too big "
						    "(want %d, got %d)\n",
						    msgsz, msghdr->msg_ts));
						error = E2BIG;
						goto done2;
					}
					*prev = msghdr->msg_next;
					if (msghdr == msqptr->msg_last) {
						if (previous == NULL) {
							if (prev !=
							    &msqptr->msg_first)
								panic("msg_first/last screwed up #2");
							msqptr->msg_first =
							    NULL;
							msqptr->msg_last =
							    NULL;
						} else {
							if (prev ==
							    &msqptr->msg_first)
								panic("msg_first/last screwed up #3");
							msqptr->msg_last =
							    previous;
						}
					}
					break;
				}
				previous = msghdr;
				prev = &(msghdr->msg_next);
			}
		}

		/*
		 * We've either extracted the msghdr for the appropriate
		 * message or there isn't one.
		 * If there is one then bail out of this loop.
		 */

		if (msghdr != NULL)
			break;

		/*
		 * Hmph!  No message found.  Does the user want to wait?
		 */

		if ((msgflg & IPC_NOWAIT) != 0) {
			DPRINTF(("no appropriate message found (msgtyp=%d)\n",
			    msgtyp));
			/* The SVID says to return ENOMSG. */
			error = ENOMSG;
			goto done2;
		}

		/*
		 * Wait for something to happen
		 */

		DPRINTF(("msgrcv:  goodnight\n"));
		error = msleep(msqptr, &msq_mtx, (PZERO - 4) | PCATCH,
		    "msgrcv", 0);
		DPRINTF(("msgrcv:  good morning (error=%d)\n", error));

		if (error != 0) {
			DPRINTF(("msgrcv:  interrupted system call\n"));
#ifdef __CYGWIN__
		    if (error == EIDRM)
                        goto done2;
#endif /* __CYGWIN__ */
			error = EINTR;
			goto done2;
		}

		/*
		 * Make sure that the msq queue still exists
		 */

		if (msqptr->msg_qbytes == 0 ||
		    msqptr->msg_perm.seq != IPCID_TO_SEQ(uap->msqid)) {
			DPRINTF(("msqid deleted\n"));
			error = EIDRM;
			goto done2;
		}
	}

	/*
	 * Return the message to the user.
	 *
	 * First, do the bookkeeping (before we risk being interrupted).
	 */

	msqptr->msg_cbytes -= msghdr->msg_ts;
	msqptr->msg_qnum--;
	msqptr->msg_lrpid = td->td_proc->p_pid;
	msqptr->msg_rtime = time (NULL);

	/*
	 * Make msgsz the actual amount that we'll be returning.
	 * Note that this effectively truncates the message if it is too long
	 * (since msgsz is never increased).
	 */

	DPRINTF(("found a message, msgsz=%d, msg_ts=%d\n", msgsz,
	    msghdr->msg_ts));
	if (msgsz > msghdr->msg_ts)
		msgsz = msghdr->msg_ts;

	/*
	 * Return the type to the user.
	 */

	mtx_unlock(&msq_mtx);
	error = copyout(&(msghdr->msg_type), user_msgp,
	    sizeof(msghdr->msg_type));
	mtx_lock(&msq_mtx);
	if (error != 0) {
		DPRINTF(("error (%d) copying out message type\n", error));
		msg_freehdr(msghdr);
		wakeup(msqptr);
		goto done2;
	}
	user_msgp = (char *)user_msgp + sizeof(msghdr->msg_type);

	/*
	 * Return the segments to the user
	 */

	next = msghdr->msg_spot;
	for (len = 0; len < msgsz; len += msginfo.msgssz) {
		size_t tlen;

		if (msgsz - len > (unsigned long) msginfo.msgssz)
			tlen = msginfo.msgssz;
		else
			tlen = msgsz - len;
		if (next <= -1)
			panic("next too low #3");
		if (next >= msginfo.msgseg)
			panic("next out of range #3");
		mtx_unlock(&msq_mtx);
		error = copyout(&msgpool[next * msginfo.msgssz],
		    user_msgp, tlen);
		mtx_lock(&msq_mtx);
		if (error != 0) {
			DPRINTF(("error (%d) copying out message segment\n",
			    error));
			msg_freehdr(msghdr);
			wakeup(msqptr);
			goto done2;
		}
		user_msgp = (char *)user_msgp + tlen;
		next = msgmaps[next].next;
	}

	/*
	 * Done, return the actual number of bytes copied out.
	 */

#ifdef __CYGWIN__
	msg_info.msg_num--;
	msg_info.msg_tot -= msgsz;
#endif /* __CYGWIN__ */

	msg_freehdr(msghdr);
	wakeup(msqptr);
	td->td_retval[0] = msgsz;
done2:
	mtx_unlock(&msq_mtx);
	return (error);
}

#ifndef __CYGWIN__
static int
sysctl_msqids(SYSCTL_HANDLER_ARGS)
{

	return (SYSCTL_OUT(req, msqids,
	    sizeof(struct msqid_ds) * msginfo.msgmni));
}

SYSCTL_DECL(_kern_ipc);
SYSCTL_INT(_kern_ipc, OID_AUTO, msgmax, CTLFLAG_RD, &msginfo.msgmax, 0, "");
SYSCTL_INT(_kern_ipc, OID_AUTO, msgmni, CTLFLAG_RDTUN, &msginfo.msgmni, 0, "");
SYSCTL_INT(_kern_ipc, OID_AUTO, msgmnb, CTLFLAG_RD, &msginfo.msgmnb, 0, "");
SYSCTL_INT(_kern_ipc, OID_AUTO, msgtql, CTLFLAG_RD, &msginfo.msgtql, 0, "");
SYSCTL_INT(_kern_ipc, OID_AUTO, msgssz, CTLFLAG_RDTUN, &msginfo.msgssz, 0, "");
SYSCTL_INT(_kern_ipc, OID_AUTO, msgseg, CTLFLAG_RDTUN, &msginfo.msgseg, 0, "");
SYSCTL_PROC(_kern_ipc, OID_AUTO, msqids, CTLFLAG_RD,
    NULL, 0, sysctl_msqids, "", "Message queue IDs");
#endif /* __CYGWIN__ */
#endif /* __OUTSIDE_CYGWIN__ */
