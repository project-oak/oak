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
/************************************************************
 * OS Test - Silicon Graphics, Inc.
 * Mendota Heights, Minnesota
 * 
 * TEST IDENTIFIER:  aiotcs02:  write/close flushes data to the file
 * 
 * PARENT DOCUMENT:  aiotds01:  kernel i/o
 * 
 * AUTHOR: Barrie Kletscher
 * 
 * CO-PILOT: Dave Baumgartner
 * 
 * TEST ITEMS:
 * 	for each open flags set used:
 * 	1. Multiple writes to a file work as specified for
 * 	   more than BUFSIZ bytes.
 * 	2. Multiple writes to a file work as specified for
 * 	   BUFSIZ bytes.
 * 	3. Multiple writes to a file work as specified for
 * 	   lower than BUFSIZ bytes.
 * 
 * INPUT SPECIFICATIONS:
 * 	Standard parse_opts supported options.
 *  
 * OUTPUT SPECIFICATIONS
 * 	Standard tst_res output format
 * 
 * ENVIRONMENTAL NEEDS:
 * 	This program uses the environment variable TMPDIR for the location
 * 	of the temporary directory.
 * 
 * 
 * SPECIAL PROCEDURAL REQUIREMENTS:
 * 	The program must be linked with tst_*.o and parse_opts.o.
 * 
 * INTERCASE DEPENDENCIES:
 * 	NONE.
 * 
 * DETAILED DESCRIPTION:
 * 	Attempt to get some memory to work with.
 * 	Call testrun writing (BUFSIZ + 1) bytes
 * 	Call testrun writing BUFSIZ bytes
 * 	Repeated call to testrun() with decreasing write sizes
 * 		less than BUFSIZ
 * 	End
 * 
 * 	Start testrun()
 * 	Attempt to open a temporary file.
 * 	Write the memory to the file.
 * 	Attempt to close the file which also flushes the buffers.
 * 	Now check to see if the number of bytes written is the
 * 		same as the number of bytes in the file.
 * 	Cleanup
 * 
 * BUGS:
 * 	NONE.
 * 
************************************************************/

#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/signal.h>
#include <errno.h>
#include "test.h"
#include "usctest.h"

#define FLAG O_RDWR | O_CREAT | O_TRUNC	/* Flags used when opening temp tile */
#define MODE  0777			/* Mode to open file with */
#define WRITES 10			/* Number of times buffer is written */
#define DECR 1000			/* Number of bytes decremented between */
					/* Calls to testrun() */
#define OK -1				/* Return value from testrun() */

#define FNAME1	"aio02.1"
#define FNAME2	"aio02.2"
#define FNAME3	"aio02.3"

#define ERR_MSG1 "Bytes in file not equal to bytes written."
#define ERR_MSG2 "Bytes in file (%d) not equal to bytes written (%d)."

char	*dp;	/* pointer to area of memory */

void setup();
void cleanup(void) __attribute__((noreturn));
int testrun(int flag, int bytes, int ti);

const char *TCID="asyncio02";         /* Test program identifier.    */
int TST_TOTAL=6;                /* Total number of test cases. */
extern int Tst_count;           /* Test Case counter for tst_* routines */
extern int Tst_nobuf;           /* variable used to turn off tst_res buffering */

extern int errno;

int exp_enos[]={0};             /* Array of expected errnos */
char mesg[150];
const char *filename;		/* name of the temporary file */

char *Progname;
int Open_flags;

int Flags[] = {
	O_RDWR | O_CREAT | O_TRUNC,
	O_RDWR | O_CREAT | O_TRUNC
};

int Num_flags;

/***********************************************************************
 * MAIN
 ***********************************************************************/
int
main(int ac, char **av)
{

    int	i;		/* counter */
    int ret_val;	/* return value from testrun call */
    int eok;		/* everything is ok flag */
    int lc;             /* loop counter */
    const char *msg;          /* message returned from parse_opts */
    int flag_cnt;

    Tst_nobuf=1;
    Num_flags = sizeof(Flags)/sizeof(int);
    TST_TOTAL= 3 * Num_flags;

    /***************************************************************
     * parse standard options, and exit if there is an error
     ***************************************************************/
    if ( (msg=parse_opts(ac, av, (option_t *) NULL, NULL)) != (char *) NULL ) {
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

	for (flag_cnt=0; flag_cnt<Num_flags; flag_cnt++) {

	/*
 	 * call testrun writing (BUFSIZ + 1) byte chunks
 	 */

	filename=FNAME1;
	if( testrun(Flags[flag_cnt],BUFSIZ+1,1) != OK)
	    tst_resm(TFAIL,ERR_MSG1);

	else if ( STD_FUNCTIONAL_TEST ) {
	        tst_resm(TPASS,
		    "More than BUFSIZE bytes multiple synchronous writes to a file check out ok");
	}

	/*
 	 * call testrun writing BUFSIZ byte chunks
 	 */

	filename=FNAME2;
	if(testrun(Flags[flag_cnt],BUFSIZ,2) != OK) {
	    tst_resm(TFAIL,ERR_MSG1);
	}
	else if ( STD_FUNCTIONAL_TEST ) {
	    tst_resm(TPASS,
		"BUFSIZE bytes multiple synchronous writes to a file checks out ok");
	}

	/*
 	 * while the byte chunks are greater than 0
 	 *	call testrun() with decreasing chunk sizes
 	 */

	filename=FNAME3;
	eok=1;
	for(i = BUFSIZ-1; i >= 0; i -= DECR) {
	    if((ret_val = testrun(Flags[flag_cnt],i,3)) != OK) {
		char output[80];	/* local output char string */

		(void)sprintf(output,ERR_MSG2,ret_val,i*WRITES);
		tst_resm(TFAIL,output);
	    }
	}

	if ( eok && STD_FUNCTIONAL_TEST ) 
	    tst_resm(TPASS,
		"Less than BUFSIZE bytes multiple synchronous writes to a file checks out ok");

	}
    }
    cleanup();

    return 0;
}	/* end main() */

/***********************************************************
 *
 *	This function does the actual running of the tests.
 *
 ***********************************************************/
int
testrun(int flag, int bytes, int ti)
{

	void cleanup();

	int	fildes,		/* temporary file's descriptor */
		i;		/* counter */

	int ret;

	struct	stat buffer;	/* buffer of memory required for stat command */

	/*
 	 *	Attempt to open a temporary file.
 	 */

	if((fildes = open(filename,flag,MODE)) == -1) {
	    sprintf(mesg, "open failed, errno:%d", errno);
                    tst_brkm(TBROK, cleanup, mesg);
	}

	/*
 	 *	Write the memory to the file.
 	 */

	for(i = 0; i < WRITES; i++) {
		TEST( write(fildes,dp,(unsigned)bytes) );
		
		if( TEST_RETURN == -1) {
		    sprintf(mesg, "write failed, errno:%d", errno);
            	    tst_brkm(TBROK, cleanup, mesg);
		}
	}	/* end for() */

	/*
 	 *	Attempt to close the file which also flushes the buffers.
 	 */

	if(close(fildes) == -1) {
	    sprintf(mesg, "close failed, errno:%d", errno);
            tst_brkm(TBROK, cleanup, mesg);
	}

        ret=OK;
	if ( STD_FUNCTIONAL_TEST ) {

	    /*
 	     *	Now check to see if the number of bytes written is the
 	     *	same as the number of bytes in the file.
 	     */

	    if(stat(filename,&buffer) == -1) {
	        sprintf(mesg, "stat failed, errno:%d", errno);
	        tst_brkm(TBROK, cleanup, mesg);
	    }


	    if(buffer.st_size != (off_t)(bytes * WRITES)) {
		    ret=(int)buffer.st_size;
	    }
	}

	if ( unlink(filename) == -1 ) {
	    sprintf(mesg, "unlink failed, errno:%d", errno);
	    tst_brkm(TBROK, cleanup, mesg);
        }

	return ret;

}	/* end testrun() */

/***************************************************************
 * setup() - performs all ONE TIME setup for this test.
 ***************************************************************/
void
setup()
{
    /* capture signals */
    tst_sig(FORK, DEF_HANDLER, cleanup);

    /* create a temporary directory and go to it */
    tst_tmpdir();

    /* Indicate which errnos are expected */
    TEST_EXP_ENOS(exp_enos);

    /* Pause if that option was specified */
    TEST_PAUSE;

    /*
     *	Attempt to get some memory to work with.
     */

    if((dp = (char *)malloc((unsigned)BUFSIZ+1)) == NULL) {
        sprintf(mesg, "malloc failed, errno:%d", errno);
        tst_brkm(TBROK, cleanup, mesg);
    }


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

    /* remove temporary directory and all files in it. */
    tst_rmdir();

    /* exit with return code appropriate for results */
    tst_exit();

}       /* End cleanup() */


