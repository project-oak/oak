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
/**********************************************************
 * 
 *    OS Test - Silicon Graphics, Inc.
 * 
 *    TEST IDENTIFIER	: ulimit01
 * 
 *    EXECUTED BY	: anyone
 * 
 *    TEST TITLE	: Basic test for ulimit(2)
 * 
 *    PARENT DOCUMENT	: usctpl01
 * 
 *    TEST CASE TOTAL	: 6
 * 
 *    WALL CLOCK TIME	: 1
 * 
 *    CPU TYPES		: ALL
 * 
 *    AUTHOR		: William Roske
 * 
 *    CO-PILOT		: Dave Fenner
 * 
 *    DATE STARTED	: 03/30/92
 * 
 *    INITIAL RELEASE	: UNICOS 7.0
 * 
 *    TEST CASES
 * 
 * 	1.) ulimit(2) returns...(See Description)
 *	
 *    INPUT SPECIFICATIONS
 * 	The standard options for system call tests are accepted.
 *	(See the parse_opts(3) man page).
 * 
 *    OUTPUT SPECIFICATIONS
 * 	
 *    DURATION
 * 	Terminates - with frequency and infinite modes.
 * 
 *    SIGNALS
 * 	Uses SIGUSR1 to pause before test if option set.
 * 	(See the parse_opts(3) man page).
 *
 *    RESOURCES
 * 	None
 * 
 *    ENVIRONMENTAL NEEDS
 * 	The libcuts.a and libsys.a libraries must be included in 
 *	the compilation of this test.
 * 
 *    SPECIAL PROCEDURAL REQUIREMENTS
 * 	None
 * 
 *    INTERCASE DEPENDENCIES
 * 	None
 * 
 *    DETAILED DESCRIPTION
 *	This is a Phase I test for the ulimit(2) system call.  It is intended
 *	to provide a limited exposure of the system call, for now.  It
 *	should/will be extended when full functional tests are written for
 *	ulimit(2).
 * 
 * 	Setup:
 * 	  Setup signal handling.
 *	  Pause for SIGUSR1 if option specified.
 * 
 * 	Test:
 *	 Loop if the proper options are given.
 * 	  Execute system call
 *	  Check return code, if system call failed (return=-1)
 *		Log the errno and Issue a FAIL message.
 *	  Otherwise, Issue a PASS message.
 * 
 * 	Cleanup:
 * 	  Print errno log and/or timing stats if options given
 * 
 * 
 *#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#**/

#include <ulimit.h>
#include <errno.h>
#include <string.h>
#include <signal.h>
#include "test.h"
#include "usctest.h"

void setup();
void cleanup(void) __attribute__((noreturn));



const char *TCID="ulimit01"; 	/* Test program identifier.    */
int TST_TOTAL=6;    		/* Total number of test cases. */
extern int Tst_count;		/* Test Case counter for tst_* routines */

int cmd;
long limit;	/* saved limit */

struct limits_t {
   int cmd;
   long newlimit;
   int nlim_flag;	/* special flag for UL_SETFSIZE records  */
   int exp_fail;
} Scenarios[] = {

  { UL_GETFSIZE, -1, 0, 0 },
  { UL_SETFSIZE, -1, 0, 1 },	/* negative test */
  { UL_SETFSIZE, -2, 1, 0 },	/* case case: must be after UL_GETFSIZE */
  { UL_SETFSIZE, -2, 2, 0 },	/* case case: must be after UL_GETFSIZE */

#if UL_GMEMLIM
  { UL_GMEMLIM, -1, 0, 0 },
#endif
#if UL_GDESLIM
  { UL_GDESLIM, -1, 0, 0 },
#endif
#if UL_GSHMEMLIM
  { UL_GSHMEMLIM, -1, 0, 0 },
#endif
  
};

int
main(int ac, char **av)
{
    int lc;		/* loop counter */
    int i;		/* inner loop (test case) counter */
    const char *msg;		/* message returned from parse_opts */
    int tmp;

    TST_TOTAL = sizeof(Scenarios)/sizeof(struct limits_t);
    
    /***************************************************************
     * parse standard options
     ***************************************************************/
    if ( (msg=parse_opts(ac, av, (option_t *)NULL, NULL)) != (char *) NULL ) {
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
	
	for ( i=0; i<TST_TOTAL; i++) {

	    cmd=Scenarios[i].cmd;
	    limit=Scenarios[i].newlimit;

	    /* 
	     * Call ulimit(2)
	     */
	    TEST(ulimit(cmd, limit));
	    
	    /* check return code */
	    if ( TEST_RETURN == -1 ) {
		if ( Scenarios[i].exp_fail ) {
		    if ( STD_FUNCTIONAL_TEST ) {
			tst_resm(TPASS, "ulimit(%d, %d) Failed, errno=%d : %s", cmd, limit,
					TEST_ERRNO, strerror(TEST_ERRNO));
		    }
		} else {
		    tst_resm(TFAIL, "ulimit(%d, %d) Failed, errno=%d : %s", cmd, limit,
			   	    TEST_ERRNO, strerror(TEST_ERRNO));
		}
	    } else {
		if ( Scenarios[i].exp_fail ) {
		    tst_resm(TFAIL, "ulimit(%d, %d) returned %d",
		       		    cmd, limit, TEST_RETURN);
		} else if ( STD_FUNCTIONAL_TEST ) {
		    tst_resm(TPASS, "ulimit(%d, %d) returned %d",
		       		    cmd, limit, TEST_RETURN);
		}

		/*
		 * Save the UL_GETFSIZE return value in the newlimit field
		 * for UL_SETFSIZE test cases.
		 */
		if ( cmd == UL_GETFSIZE ) {
		    for (tmp=i+1; tmp<TST_TOTAL; tmp++) {
			if ( Scenarios[tmp].nlim_flag == 1 ) {
			    Scenarios[tmp].newlimit = TEST_RETURN;
			}
			if ( Scenarios[tmp].nlim_flag == 2 ) {
			    Scenarios[tmp].newlimit = TEST_RETURN-1;
			}
		    }
		}
	    }
	}
    }	/* End for TEST_LOOPING */

    /***************************************************************
     * cleanup and exit
     ***************************************************************/
    cleanup();

    return 0;
}	/* End main */

/***************************************************************
 * setup() - performs all ONE TIME setup for this test.
 ***************************************************************/
void 
setup()
{

    /* capture signals */
    tst_sig(NOFORK, DEF_HANDLER, cleanup);

    /* Pause if that option was specified */
    TEST_PAUSE;

}	/* End setup() */


/***************************************************************
 * cleanup() - performs all ONE TIME cleanup for this test at
 *		completion or premature exit.
 ***************************************************************/
void 
cleanup()
{
    /*
     * print timing stats if that option was specified.
     */
    TEST_CLEANUP;

    /* exit with return code appropriate for results */
    tst_exit();
}	/* End cleanup() */
