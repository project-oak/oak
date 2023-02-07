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
 *
 */
/* $Id$ */
/***********************************************************************************
 * 
 * OS Test   -  Silicon Graphics, Inc.  Eagan, Minnesota
 * 
 * TEST IDENTIFIER :  signal03  Boundary value and other invalid value checking
 * 				 of signal setup and signal sending.
 * 
 * PARENT DOCUMENT :  sgntds01  Signal System Call
 * 		
 * AUTHOR           :  Dave Baumgartner
 * 		    :  Rewrote 12/92 by Richard Logan
 * 
 * CO-PILOT         :  Barrie Kletscher
 * 
 * DATE STARTED     :  10/17/85
 * 
 * TEST ITEMS
 * 
 * 	1. SIGKILL can not be set to be caught, errno:EINVAL (POSIX).
 * 	2. SIGKILL can not be caught.
 * 	3. SIGKILL can not be set to be ignored, errno:EINVAL (POSIX).
 * 	4. SIGKILL can not be ignored.
 * 	5. SIGKILL can not be reset to default, errno:EINVAL (POSIX.
 * 
 * ENVIRONMENTAL NEEDS
 * 
 * 	NONE
 * 
 * SPECIAL PROCEDURAL REQUIREMENTS
 * 
 * 	None
 * 
 * INTERCASE DEPENDENCIES
 * 
 * 	2 depends on 1 and 4 on 3.
 * 
 * DETAILED DESCRIPTION
 * 
 * 	main()
 * 	Call catch_test to test setup and catching of SIGKILL.
 * 
 * 
 * 	Call ignore_test to test setup and ignoring of SIGKILL.
 * 
 * 
 * 	Call sigdfl_test to test setting SIGKILL to default.
 * 
 * 	* END OF MAIN *
 * 
 * 
 * 	catch_test()
 * 
 * 	fork a child
 * 	if this is the parent
 * 		sleep to let child start.
 * 		send sig to child.
 * 		wait for the child to terminate.
 * 
 * 		if the termination status of the child equals the signal sent to it
 * 			Test item 1 PASSED the child was killed.
 * 		else if status equals the exit value of SIG_CAUGHT
 * 			Test item 2 FAILED sig was caught.
 * 		else 
 * 			Test item 2 FAILED because the child was not killed
 * 			but sig was not caught either.
 * 
 * 	else this the child
 * 		set exit_val to SIG_NOT_CAUGHT.
 * 		set to catch sig, where the interrupt routine just sets 
 * 		exit_val to SIG_CAUGHT.
 * 
 * 		If the return value and errno, after trying to set to catch sig,
 * 		do not indicate that an error has occurred.
 * 			Test item 1 FAILED bad return, return value:X, errno:X.
 * 		else
 * 			Test item 1 PASSED sig was not set to be caught.
 * 
 * 		pause until the parent sends a signal.
 * 		The child should be killed by the signal but if not exit
 * 		with exit_val.
 * 
 * 	* End of catch_test. *
 * 
 * 
 * 	ignore_test()
 * 
 * 	fork a child
 * 	if this is the parent
 * 		sleep to let child start.
 * 		send SIGKILL to child.
 * 		wait for the child to terminate.
 * 
 * 		if the termination status of the child equals SIGKILL
 * 			Test item 4 PASSED the child was killed.
 * 		else if the status equals the exit value of SIG_IGNORED
 * 			Test item 4 FAILED SIGKILL was ignored.
 * 
 * 	else this the child
 * 
 * 		If the return value and errno, after trying to set to ignore SIGKILL,
 * 		do not indicate that an error has occurred.
 * 			Test item 3 FAILED bad return, return value:X, errno:X.
 * 		else
 * 			Test item 3 PASSED SIGKILL was not set to be ignored.
 * 
 * 		pause until the parent sends SIGKILL.
 * 		The child should be killed by the signal but if not exit
 * 		with SIG_IGNORED.
 * 
 * 	* End of ignore_test. *
 * 
 * 
 * 	sigdfl_test()
 * 
 * 	If the return value and errno, after trying to set to SIGKILL to default,
 * 	do not indicate that an error has occurred.
 * 		Test item 5 FAILED bad return, return value:X, errno:X.
 * 	else
 * 		Test item 5 PASSED SIGKILL was not set to default.
 * 
 * 	* End of sigdfl_test. *
 * 
 * BUGS/NOTES
 * 	Since the system call under test is executed in the child, no
 *	timings on this system call will be reported.
 * 
***********************************************************************************/

#include <signal.h>
#include <errno.h>  
#include <fcntl.h>
#include <string.h>
#include <sys/wait.h>

#include "test.h"
#include "usctest.h"

void setup();
void cleanup(void) __attribute__((noreturn));
void do_test();
void sigdfl_test();
void update_timings();

#if defined(linux)
# define SIG_PF sig_t  /* This might need to be sighandler_t on some systems */
#elif defined(__CYGWIN__)
typedef void (*sighandler_t) (int);
#define SIG_PF sighandler_t
#endif

#define SIG_CAUGHT	1
#define SIG_NOT_CAUGHT	0
#define SIG_IGNORED	5
#define TIMED_OUT	99

#define TIMEOUT		20

#define GO_FLAG		1
#define ERROR_FLAG	2
#define PASS_FLAG	3
#define FAIL_FLAG	4

#define IGNORE_TEST	1
#define CATCH_TEST	2

#define MAXMESG 150	/* The Maximum message that can be created.	*/

int exit_val;		/* Global variable, used to tell whether the	*/
			/* child exited instead of being killed.	*/
extern int errno;	/* errno holds the error value returned by	*/
			/* a system call.                        	*/
char mesg[MAXMESG];	/* Holds messages to pass to tst_res.		*/ 

struct ipc_t {
    int status;
    char mesg[MAXMESG];
    struct tblock timings;
} Ipc_info;

const char *TCID = "signal03";
int TST_TOTAL = 5;
extern int Tst_count;           /* count of test items completed */

int Pid;		/* Return value from fork.			 */

long Tret;

/***********************************************************************
 *   M A I N
 ***********************************************************************/
int
main(argc, argv)
int argc;
char **argv;
{
    int lc;
    const char *msg;

    /***************************************************************
    * parse standard options
    ***************************************************************/
    if ( (msg=parse_opts(argc, argv, (option_t *) NULL, NULL)) != (char *) NULL ) {
        tst_brkm(TBROK, NULL, "OPTION PARSING ERROR - %s", msg);
	tst_exit();
    }

    /***************************************************************
     * perform global setup for test
     ***************************************************************/
    setup();

    /***************************************************************
     * check looping state if -c option given
     ***************************************************************/
    for (lc=0; TEST_LOOPING(lc); lc++) {

        /* reset Tst_count in case we are looping. */
        Tst_count=0;

	errno=-4;

	/*
	 * Call catch_test to test setup and catching of SIGKILL.
	 */
	(void) do_test(CATCH_TEST, Tst_count);

	/*
	 * Call ignore_test to test setup and ignoring of SIGKILL.
	 */
	(void) do_test(IGNORE_TEST, Tst_count);

	/*
	 * Call sigdfl_test to test setting SIGKILL to default.
	 */
	(void) sigdfl_test();

    }

    cleanup();

    return 0;
} /*End of main*/

/***********************************************************************
 *
 ***********************************************************************/
void
do_test(test_case, tst_count)
int test_case;
int tst_count;
{
  int term_stat;	/* Termination status of the child returned to	 */
			/* the parent.					 */
  char string[30];
  int fd1[2];		/* ipc */
  int rd_sz;		/* size of read */
  void p_timeout_handler();
  void c_timeout_handler();
  void catchsig();

  Tst_count = tst_count;

  /*
   * Create a pipe of ipc
   */
  if ( pipe(fd1) == -1 ) {
	 sprintf(mesg,
	 "pipe system call failed, Errno: %d, Error message: %s",
			errno,strerror(errno)); 
	 tst_resm(TBROK,mesg);
	 tst_resm(TBROK,mesg);
	 return;
  }

  /*
   * Cause the read to return 0 once EOF is encountered and the
   * read to return -1 if pipe is empty.
   */

  if ( fcntl(fd1[0], F_SETFL, O_NONBLOCK) == -1 ) {
	sprintf(mesg, "fcntl(fd1[0], F_SETFL, O_NONBLOCK) failed: errno=%d",
	    errno);
	tst_resm(TBROK,mesg);
        tst_resm(TBROK,mesg);
	close(fd1[0]);
	close(fd1[1]);
	return;
  }

  if ((Pid = fork()) > 0) {	/* parent */

	signal(SIGALRM, p_timeout_handler);

	alarm(TIMEOUT);

	close(fd1[1]);      /* close write side */

	/*
	 * Deal with child's messages.
	 * Only the GO_FLAG status will allow parent to
	 * go on.  All pipe io will be in the ipc_t structure sizes 
	 * to avoid reading part of next message.
	 */
        while ( 1 ) {

	    while ( (rd_sz=read(fd1[0], (char *)&Ipc_info, sizeof(Ipc_info))) != 0 ) {
	        if ( rd_sz > 0 )
	            break;	/* read something */
	    }

	    if ( rd_sz == 0 ) {		/* if EOF encountered */
		sprintf(mesg, "child's pipe is closed before 'go' message received");
		tst_resm(TBROK, Ipc_info.mesg);
		tst_resm(TBROK, Ipc_info.mesg);
		close(fd1[0]);
	 	return;
	    }

	    else if ( Ipc_info.status == GO_FLAG ) {
	 	break;	/* go on */
	    }
	    else if ( Ipc_info.status == ERROR_FLAG ) {
		tst_resm(TBROK, "From child: %s", Ipc_info.mesg);
		tst_resm(TBROK, "From child: %s", Ipc_info.mesg);
		close(fd1[0]);
	 	return;
	    }
	    else if ( Ipc_info.status == PASS_FLAG ) {
		
		if ( STD_FUNCTIONAL_TEST )
		    tst_resm(TPASS, "From child: %s", Ipc_info.mesg);
		else
		    Tst_count++;
		update_timings(Ipc_info.timings);
	    }
	    else if ( Ipc_info.status == FAIL_FLAG ) {
		tst_resm(TFAIL, "From child: %s", Ipc_info.mesg);
		update_timings(Ipc_info.timings);
            }   
	    else {
		tst_resm(TINFO, "Unknown message from child: %s", mesg);
	    }
	}

	/*
	 * Send the signal SIGKILL to the child.
	 */
	 if (kill(Pid,SIGKILL) == -1)
	 {
		/*
		 * The kill system call failed.
		 */
	       	 sprintf(mesg,
		 "kill(Pid,SIGKILL) failed, Errno: %d, Error message: %s",
				errno,strerror(errno)); 
		 tst_resm(TBROK,mesg);
		 tst_resm(TBROK,mesg);
		 close(fd1[0]);
	 	 return;
	}

	/*
	 * Wait for the child to terminate and check the termination status.
	 */
	if (wait(&term_stat) == -1) {
		/*
		 * The wait system call failed.
		 */
	       	 sprintf(mesg,
		 "Wait system call failed. Errno: %d, Error message: %s",
				errno,strerror(errno)); 
		 tst_resm(TBROK,mesg);
		 tst_resm(TBROK,mesg);
		 close(fd1[0]);
	 	 return;
	}
	else if ( STD_FUNCTIONAL_TEST ) {
	    if ((term_stat & 0377) == SIGKILL) {
		/*
		 * The child was killed by the signal sent,
		 * which is correct.
		 */
		 tst_resm(TPASS,"The child was killed by SIGKILL.");
	    }
	    else if ( (term_stat >> 8) == TIMED_OUT ) {
	        sprintf(mesg, "child exited with a timed out exit status");
	        tst_resm(TBROK,mesg);
	    }
	    else {
	        if ((term_stat >> 8) == SIG_IGNORED && test_case == IGNORE_TEST ) {
		    sprintf(mesg, 
		        "SIGKILL was ignored by child after sent by parent.");
	        }
	        else if ((term_stat >> 8) == SIG_CAUGHT && test_case == CATCH_TEST ) {
		    sprintf(mesg,
		        "SIGKILL was caught by child after sent by parent.");
	        }
	        else {
	            sprintf(mesg,
		        "Child's termination status is unexpected. Status: %d (%#o).",
		        term_stat, term_stat);
	        }
	        tst_resm(TFAIL, mesg);
	    }
	}
	else {
	    Tst_count++;	/* increment test counter */
	}
	close(fd1[0]);

    }	/* End of parent. */
    else if (Pid == 0) {	
	/*
	 * This is the child.
	 * Set up to ignore/catch SIGKILL and check the return values.
	 */
	errno=0;
	if ( test_case == IGNORE_TEST ) {
	    exit_val = SIG_IGNORED;
	    strcpy(string, "signal(SIGKILL, SIG_IGN)");

	    Tret=(long)signal(SIGKILL, SIG_IGN);
	    TEST_ERRNO=errno;
	}
	else {
	    exit_val = SIG_NOT_CAUGHT;
	    strcpy(string, "signal(SIGKILL, catchsig)");
	    Tret=(long)signal(SIGKILL, catchsig);
	    TEST_ERRNO=errno;
	}
	Ipc_info.timings=tblock;	

	if ( (SIG_PF)Tret == SIG_ERR  ) {
	    if ( TEST_ERRNO == EINVAL ) {
	        sprintf(Ipc_info.mesg, "%s ret:%ld SIG_ERR (%ld) as expected",
		    string, Tret, (long)SIG_ERR);
		Ipc_info.status = PASS_FLAG;
	    }
	    else {
	        sprintf(Ipc_info.mesg,
		    "%s ret:%ld, errno:%d expected ret:%ld, errno:%d",
		    string, Tret, TEST_ERRNO, (long)SIG_ERR, EINVAL);
		Ipc_info.status = FAIL_FLAG;
	    }
		
	    write(fd1[1], (char *)&Ipc_info, sizeof(Ipc_info));
	}
	else {
	    /*
	     * The child was not allowed to set the signal to 
	     * be ignored and errno was correct.
	     */
	    sprintf(Ipc_info.mesg,
		"%s ret:%ld, errno:%d expected ret:%ld, errno:%d",
		string, Tret, TEST_ERRNO, (long)SIG_ERR, EINVAL);
	    Ipc_info.status = FAIL_FLAG;
	    write(fd1[1], (char *)&Ipc_info, sizeof(Ipc_info));
	}

	/*
	 * tell parent we are ready - setup by child is done
	 */
	Ipc_info.status = GO_FLAG;
	write(fd1[1], (char *)&Ipc_info, sizeof(Ipc_info));

	/*
	 * Set the alarm to wake up from the pause below if
	 * the parents signal is ignored.
	 */
	signal(SIGALRM, p_timeout_handler);
	alarm(TIMEOUT);

	/*
	 * Pause until the parent sends a signal or until alarm is received.
	 */
	pause();

	exit(exit_val);


    }	/* End of child. */
    else {
	/*
	 * The fork system call failed.
	 */
	 sprintf(mesg,
		"Fork system call failed. Errno: %d, Error message: %s",
			errno,strerror(errno)); 
	 tst_resm(TBROK,mesg);
	 tst_resm(TBROK,mesg);
 	 close(fd1[0]);
         close(fd1[1]);
	 return;
    }

} /* End of do_test. */

/***********************************************************************
 * sigdfl_test - test for attempt to set SIGKILL to default 
 ***********************************************************************/
void
sigdfl_test()
{
  /*
   * Try to set SIGKILL to default and check the return values.
   */
   errno=-4;

   Tret=(long)signal(SIGKILL,SIG_DFL);
   TEST_RETURN=Tret;
   TEST_ERRNO=errno;


    if ( (SIG_PF)TEST_RETURN == SIG_ERR  ) {
	if ( STD_FUNCTIONAL_TEST ) {
	    if ( TEST_ERRNO != EINVAL ) {
	        sprintf(mesg,
	            "signal(SIGKILL,SIG_DFL) ret:%d, errno:%d expected ret:-1, errno:%d",
	            TEST_RETURN, TEST_ERRNO, EINVAL);
	        tst_resm(TFAIL, mesg);
	    }
	    else {
	        sprintf(mesg,
	            "signal(SIGKILL,SIG_DFL) ret:%d, errno:%d as expected.",
	            TEST_RETURN, TEST_ERRNO);
	        tst_resm(TPASS, mesg);
	    }
	}
	else
	    Tst_count++;
    }
    else {
	sprintf(mesg,
	    "signal(SIGKILL,SIG_DFL) ret:%d, errno:%d expected ret:-1, errno:%d",
	    TEST_RETURN, TEST_ERRNO, EINVAL);
	tst_resm(TFAIL, mesg);
    }

}	/* End of sigdfl_test. */

/***************************************************************
 * setup() - performs all ONE TIME setup for this test.
 ***************************************************************/
void
setup()
{
    /* capture signals */
    tst_sig(FORK, DEF_HANDLER, cleanup);

    /* make and change to a temporary directory */
    tst_tmpdir();

    /* Pause if that option was specified */
    TEST_PAUSE;

}       /* End setup() */

/***************************************************************
 * cleanup() - performs all ONE TIME cleanup for this test at
 *              completion or premature exit.
 ***************************************************************/
void
cleanup()
{

    /*
     * print timing stats if that option was specified.
     * print errno log if that option was specified.
     */

    TEST_CLEANUP;

    /*
     * remove the temporary directory and exit with
     * return code appropriate for results 
     */

    tst_rmdir();

    tst_exit();

}       /* End cleanup() */

/***********************************************************************
 *  Signal handler routine that used by the parent to handler
 *  a time out situation.  It will attempt to kill the child and
 *  call cleanup.
 ***********************************************************************/
void
p_timeout_handler()
{
    kill(Pid, SIGKILL);
    cleanup();
}

/***********************************************************************
 * Signal handler routine that used by the child to handle
 * a time out situation.  It will set a global varaible and return
 * if called.
 ***********************************************************************/
void
c_timeout_handler()
{
    exit_val = TIMED_OUT;
    return;
}

/***********************************************************************
 * This signal handling routine will set a global variable and return
 * if called.
 ***********************************************************************/
void
catchsig()
{
   exit_val = SIG_CAUGHT;
   return;
}

/***********************************************************************
 * Update timing information
 ***********************************************************************/
void
update_timings(atblock)
struct tblock atblock;
{
    tblock.tb_max += atblock.tb_max;
    tblock.tb_min += atblock.tb_min;
    tblock.tb_total += atblock.tb_total;
    tblock.tb_count += atblock.tb_count;
}
