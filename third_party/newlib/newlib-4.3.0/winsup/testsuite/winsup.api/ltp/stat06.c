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
/**********************************************************
 * 
 *    OS Test - Silicon Graphics, Inc.
 * 
 *    TEST IDENTIFIER	: stat06
 * 
 *    EXECUTED BY	: anyone
 * 
 *    TEST TITLE	: stat(2) negative path testcases
 * 
 *    PARENT DOCUMENT	: None
 * 
 *    TEST CASE TOTAL	: 7
 * 
 *    WALL CLOCK TIME	: 1
 * 
 *    CPU TYPES		: ALL
 * 
 *    AUTHOR		: Richard Logan
 * 
 *    CO-PILOT		: William Roske
 * 
 *    DATE STARTED	: 03/30/94
 * 
 *    INITIAL RELEASE	: UNICOS 7.0
 * 
 *    TEST CASES
 * 
 * 	1-7) See Testcases structure below.
 *	
 *    INPUT SPECIFICATIONS
 * 	The standard options for system call tests are accepted.
 *	(See the parse_opts(3) man page).
 *      -h  : print help and exit
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
 *	This is a Phase I test for the stat(2) system call.  It is intended
 *	to provide a limited exposure of the system call, for now.  It
 *	should/will be extended when full functional tests are written for
 *	stat(2).
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

#include <sys/types.h>
#include <sys/fcntl.h>
#include <sys/stat.h>
#include <errno.h>
#include <string.h>
#include <signal.h>
#include <setjmp.h>
#include "test.h"
#include "usctest.h"

void setup();
void cleanup(void) __attribute__((noreturn));

const char *TCID="stat06";		/* Test program identifier.    */
int TST_TOTAL=8;    		/* Total number of test cases. */
extern int Tst_count;		/* Test Case counter for tst_* routines */

extern char *get_high_address();

int exp_enos[]={0, 0};

int high_address_setup();
int longpath_setup();
int no_setup();
int filepath_setup();
char Longpathname[PATH_MAX+2];
char High_address[64];
struct stat statbuf;
jmp_buf sig11_recover;
void sig11_handler(int sig);

struct test_case_t {
   const char *pathname;
   struct stat *stbuf;
   const char *desc;
   int exp_errno;
   int (*setupfunc)();
} Test_cases[] = {
    { "nonexistfile", &statbuf, "non-existent file", ENOENT, no_setup},
    { "", &statbuf, "path is empty string", ENOENT, no_setup},
    { "nefile/file", &statbuf, "path contains a non-existent file",
		ENOENT, no_setup },
#ifndef __CYGWIN__
    { "file/file", &statbuf, "path contains a regular file",
		ENOTDIR, filepath_setup },
#endif
    { Longpathname, &statbuf, "pathname too long", ENAMETOOLONG, longpath_setup },
    { High_address, &statbuf, "address beyond address space", EFAULT, high_address_setup },
    { (char *)-1, &statbuf, "negative address", EFAULT, no_setup },
    { "file", (struct stat *)-1, "invalid struct stat address", EFAULT, filepath_setup },
    { NULL, NULL, NULL, 0, no_setup }
};

/***********************************************************************
 * Main
 ***********************************************************************/
int
main(int ac, char **av)
{
    int lc;		/* loop counter */
    const char *msg;	/* message returned from parse_opts */
    const char *fname;
    const char *desc;
    int ind;
    struct stat *stbuf;
    struct sigaction sa, osa;
    
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

    /* set the expected errnos... */
    TEST_EXP_ENOS(exp_enos);

    /***************************************************************
     * check looping state if -c option given
     ***************************************************************/
    for (lc=0; TEST_LOOPING(lc); lc++) {

	/* reset Tst_count in case we are looping. */
	Tst_count=0;
	

        for (ind=0; Test_cases[ind].desc != NULL; ind++ ) {

	    fname = Test_cases[ind].pathname;
	    desc = Test_cases[ind].desc;
	    stbuf = Test_cases[ind].stbuf;
       
	    if (stbuf == (struct stat *)-1) {
		/* special sig11 case */
		sa.sa_handler = &sig11_handler;
		sigemptyset(&sa.sa_mask);
		sa.sa_flags = 0;

		sigaction(SIGSEGV, NULL, &osa);
		sigaction(SIGSEGV, &sa, NULL);

		if (setjmp(sig11_recover)) {
		    TEST_RETURN = -1;
		    TEST_ERRNO = EFAULT;
		} else {
		    TEST(stat(fname, stbuf));
		}
		sigaction(SIGSEGV, &osa, NULL);
	    } else {
		/*
		 *  Call stat(2)
		 */

		TEST(stat(fname, stbuf));
	    }
	
	    /* check return code */
	    if ( TEST_RETURN == -1 ) {
	        if ( STD_FUNCTIONAL_TEST ) {
		    if ( TEST_ERRNO == Test_cases[ind].exp_errno )
	                tst_resm(TPASS, "stat(<%s>, &stbuf) Failed, errno=%d",
			    desc, TEST_ERRNO);
		    else
			tst_resm(TFAIL,
			    "stat(<%s>, &stbuf) Failed, errno=%d, expected errno:%d",
                            desc, TEST_ERRNO, Test_cases[ind].exp_errno);
	        }
		else
		   Tst_count++;
	    } else  {
	        tst_resm(TFAIL,
		    "stat(<%s>, &stbuf) returned %d, expected -1, errno:%d",
		    desc, TEST_RETURN, Test_cases[ind].exp_errno);
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
    int ind;

    /* capture signals */
    tst_sig(NOFORK, DEF_HANDLER, cleanup);

    /* make a temp directory and cd to it */
    tst_tmpdir();

    /* Pause if that option was specified */
    TEST_PAUSE;

    for (ind=0; Test_cases[ind].desc != NULL; ind++ ) {
	Test_cases[ind].setupfunc();
    }

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
     * print errno log if that option was specified.
     */
    TEST_CLEANUP;

    /* Remove tmp dir and all files in it */
    tst_rmdir();

    /* exit with return code appropriate for results */
    tst_exit();

}	/* End cleanup() */

/******************************************************************
 * no_setup() - does nothing
 ******************************************************************/
int
no_setup()
{
    return 0;
}

/******************************************************************
 * high_address_setup() - generates an address that should cause a segfault
 ******************************************************************/
int
high_address_setup()
{
    int ind;

    for (ind=0; Test_cases[ind].desc != NULL; ind++ ) {
	if ( Test_cases[ind].pathname == High_address ) {
	/*if ( strcmp(Test_cases[ind].pathname, HIGH_ADDRESS) == 0 ) { ***/
	    Test_cases[ind].pathname = get_high_address();
	    break;
	}
    }
    return 0;

}

/******************************************************************
 * longpath_setup() - creates a filename that is too long
 ******************************************************************/
int
longpath_setup()
{
   int ind;

    for(ind=0; ind<= PATH_MAX+1; ind++) {
	Longpathname[ind] = 'a';
    }
    return 0;

}

/******************************************************************
 * filepath_setup() creates a file the exists that we will treat as a directory
 ******************************************************************/
int
filepath_setup()
{
    int fd;

    if ( (fd=creat("file", 0777)) == -1 ) {
	tst_brkm(TBROK, cleanup, "creat(file) failed, errno:%d %s",
	    errno, strerror(errno));
    }
    close(fd);
    return 0;
}

/******************************************************************
 * sig11_handler() - our segfault recover hack
 ******************************************************************/
void 
sig11_handler(int sig)
{
    longjmp(sig11_recover, 1);
}
