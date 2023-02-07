/*
 * Copyright (c) 2000 Silicon Graphics, Inc.  All Rights Reserved.
 * 
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of version 2 of the GNU General Public License as
 * published by the Free Software Foundation.
 * 
 * This program is distributed in the hope that it would be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * Further, this software is distributed without any warranty that it is
 * free of the rightful claim of any third person regarding infringement
 * or the like.  Any license provided herein, whether implied or
 * otherwise, applies only to this software file.  Patent licenses, if
 * any, provided herein do not apply to combinations of this program with
 * other software, or any other product whatsoever.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write the Free Software Foundation, Inc., 59
 * Temple Place - Suite 330, Boston MA 02111-1307, USA.
 * 
 * Contact information: Silicon Graphics, Inc., 1600 Amphitheatre Pkwy,
 * Mountain View, CA  94043, or:
 * 
 * http://www.sgi.com 
 * 
 * For further information regarding this notice, see: 
 * 
 * http://oss.sgi.com/projects/GenInfo/NoticeExplan/
 */

/* $Id$ */

/*****************************************************************************
	OS Testing  - Silicon Graphics, Inc.

	FUNCTION IDENTIFIER : tst_sig  Set up for unexpected signals.

	AUTHOR          : David D. Fenner

	CO-PILOT        : Bill Roske

	DATE STARTED    : 06/06/90

	This module may be linked with c-modules requiring unexpected
	signal handling.  The parameters to tst_sig are as follows:

		fork_flag - set to FORK or NOFORK depending upon whether the
			calling program executes a fork() system call.  It
			is normally the case that the calling program treats
			SIGCLD as an expected signal if fork() is being used.

		handler - a pointer to the unexpected signal handler to
			be executed after an unexpected signal has been
			detected.  If handler is set to DEF_HANDLER, a 
			default handler is used.  This routine should be
			declared as function returning an int.

		cleanup - a pointer to a cleanup routine to be executed
			by the unexpected signal handler before tst_exit is
			called.  This parameter is set to NULL if no cleanup
			routine is required.  An external variable, T_cleanup
			is set so that other user-defined handlers have 
			access to the cleanup routine.  This routine should be
			declared as returning type void.

***************************************************************************/

#ifndef CRAY
#define _BSD_SIGNALS	1	/* Specify that we are using BSD signal interface */
#endif

#include <errno.h>
#include <string.h>
#include <signal.h>
#include "test.h"

#define MAXMESG 150		/* size of mesg string sent to tst_res */

void (*T_cleanup)();		/* pointer to cleanup function */

extern int errno;
static void def_handler();		/* default signal handler */

/****************************************************************************
 * tst_sig() : set-up to catch unexpected signals.  fork_flag is set to NOFORK
 *    if SIGCLD is to be an "unexpected signal", otherwise it is set to
 *    FORK.  cleanup points to a cleanup routine to be executed before
 *    tst_exit is called (cleanup is set to NULL if no cleanup is desired).
 *    handler is a pointer to the signal handling routine (if handler is
 *    set to NULL, a default handler is used).
 ***************************************************************************/

void
tst_sig(int fork_flag, void (*handler)(), void (*cleanup)())
{
	char mesg[MAXMESG];		/* message buffer for tst_res */
	int sig;

	/*
	 * save T_cleanup and handler function pointers
	 */
	T_cleanup = cleanup;		/* used by default handler */

	if (handler == DEF_HANDLER) {
		/* use default handler */
		handler = def_handler;
	}

	/*
	 * now loop through all signals and set the handlers
	 */

	for (sig = 1; sig < NSIG; sig++) {
	    /*
	     * SIGKILL is never unexpected.
	     * SIGCLD is only unexpected when
	     *    no forking is being done.
	     * SIGINFO is used for file quotas and should be expected
	     */

	    switch (sig) {
	        case SIGKILL:
	        case SIGSTOP:
	        case SIGCONT:
#ifdef CRAY
	        case SIGINFO:
	        case SIGRECOVERY:	/* allow chkpnt/restart */
#endif  /* CRAY */

#ifdef SIGSWAP
  case SIGSWAP:
#endif /* SIGSWAP */

#ifdef SIGCKPT
	        case SIGCKPT:
#endif
#ifdef SIGRESTART
	        case SIGRESTART:
#endif
                /*
                 * pthread-private signals SIGPTINTR and SIGPTRESCHED.
                 * Setting a handler for these signals is disallowed when
                 * the binary is linked against libpthread.
                 */
#ifdef SIGPTINTR
                case SIGPTINTR:
#endif /* SIGPTINTR */
#ifdef SIGPTRESCHED
                case SIGPTRESCHED:
#endif /* SIGPTRESCHED */
#ifdef __CYGWIN__
		case SIGILL:
		case SIGTRAP:
		case SIGABRT:
		case SIGEMT:
		case SIGFPE:
		case SIGBUS:
#endif
	            break;

	        case SIGCLD:
	            if ( fork_flag == FORK )
		        continue;

	        default:
		    if (signal(sig, handler) == SIG_ERR) {
		        (void) sprintf(mesg,
			    "signal() failed for signal %d. error:%d %s.",
			    sig, errno, strerror(errno));
		        tst_resm(TWARN, mesg);
		    }
		break;
            }
#ifdef __sgi
	    /* On irix  (07/96), signal() fails when signo is 33 or higher */
	    if ( sig+1 >= 33 )
		break;
#endif  /*  __sgi */

	} /* endfor */
}



/****************************************************************************
 * def_handler() : default signal handler that is invoked when
 *      an unexpected signal is caught.
 ***************************************************************************/

static void
def_handler(int sig)
{
	char mesg[MAXMESG];		/* holds tst_res message */

	/* first reset trap for this signal (except SIGCLD - its weird) */
	if ((sig != SIGCLD) && (sig != SIGSTOP) && (sig != SIGCONT)) {
		if (signal(sig, def_handler) == SIG_ERR) {
			(void) sprintf(mesg,
				"def_handler: signal() failed for signal %d. error:%d %s.",
				sig, errno, strerror(errno));
			tst_resm(TWARN, mesg);
		}
	}

	(void) sprintf(mesg, "Unexpected signal %d received.", sig);

	/*
         * Break remaining test cases, do any cleanup, then exit
	 */
	tst_brkm(TBROK, 0, mesg);

	/* now cleanup and exit */
	if (T_cleanup) {
		(*T_cleanup)();
	}

	tst_exit();
}
