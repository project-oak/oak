/*
 *
 *   Copyright (c) International Business Machines  Corp., 2001
 *
 *   This program is free software;  you can redistribute it and/or modify
 *   it under the terms of the GNU General Public License as published by
 *   the Free Software Foundation; either version 2 of the License, or
 *   (at your option) any later version.
 *
 *   This program is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY;  without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See
 *   the GNU General Public License for more details.
 *
 *   You should have received a copy of the GNU General Public License
 *   along with this program;  if not, write to the Free Software
 *   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
 */

/*
 * Test Name: sync01
 *
 * Test Description:
 *  Open a file for write; modify the file, then do a sync().
 *  Verify that the data has been written to disk by re-opening the file.
 *
 * Expected Result:
 *  sync() alawys returns 0 in Linux. The data written to the file should
 *  be updated to the disk.
 *
 * Algorithm:
 *  Setup:
 *   Setup signal handling.
 *   Create temporary directory.
 *   Pause for SIGUSR1 if option specified.
 *
 *  Test:
 *   Loop if the proper options are given.
 *   Execute system call
 *   Check return code, if system call failed (return=-1)
 *   	Log the errno and Issue a FAIL message.
 *   Otherwise,
 *   	Verify the Functionality of system call	
 *      if successful,
 *      	Issue Functionality-Pass message.
 *      Otherwise,
 *		Issue Functionality-Fail message.
 *  Cleanup:
 *   Print errno log and/or timing stats if options given
 *   Delete the temporary directory created.
 *
 * Usage:  <for command-line>
 *  sync01 [-c n] [-f] [-i n] [-I x] [-p x] [-t]
 *	where,  -c n : Run n copies concurrently.
 *		-f   : Turn off functionality Testing.
 *		-i n : Execute test n times.
 *		-I x : Execute test for x seconds.
 *		-P x : Pause for x seconds between iterations.
 *		-t   : Turn on syscall timing.
 *
 * History
 *	07/2001 John George
 *		-Ported
 *
 * Restrictions:
 *  None.
 */

#include <sys/types.h>
#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <signal.h>
#include <sys/stat.h>

#include "test.h"
#include "usctest.h"

#define TEMP_FILE	"temp_file"
#define FILE_MODE       S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH

const char *TCID="sync01";		/* Test program identifier.    */
int TST_TOTAL=1;		/* Total number of test cases. */
extern int Tst_count;		/* Test Case counter for tst_* routines */
char write_buffer[BUFSIZ];	/* buffer used to write data to file*/
int fildes;			/* file descriptor for temporary file */

void setup();			/* Main setup function of test */
void cleanup(void) __attribute__((noreturn));			/* cleanup function for the test */

int
main(int ac, char **av)
{
	int lc;				/* loop counter */
	const char *msg;		/* message returned from parse_opts */
	char read_buffer[BUFSIZ];	/* buffer used to read data from file*/
    
	/* Parse standard options given to run the test. */
	msg = parse_opts(ac, av, (option_t *) NULL, NULL);
	if (msg != (char *) NULL) {
		tst_brkm(TBROK, cleanup, "OPTION PARSING ERROR - %s", msg);
		/*NOTREACHED*/
	}

	/* Perform global setup for test */
	setup();

	/* Check looping state if -i option given */
	for (lc = 0; TEST_LOOPING(lc); lc++) {
		/* Reset Tst_count in case we are looping. */
		Tst_count=0;

		/* 
		 * Call sync(2) to commit buffer data to disk.
		 */
		TEST_VOID(sync());

		if (TEST_RETURN == -1) {
			tst_resm(TFAIL, "%s, Failed, errno=%d : %s",
				TCID, TEST_ERRNO, strerror(TEST_ERRNO));
		} else {
			/*
			 * Perform functional verification if test
			 * executed without (-f) option.
			 */
			if (STD_FUNCTIONAL_TEST) {
				/* Set the file ptr to b'nning of file */
				if (lseek(fildes, 0, SEEK_SET) < 0) {
					tst_brkm(TFAIL, cleanup, "lseek() "
						"failed on %s, error=%d",
						 TEMP_FILE, errno);
					/*NOTREACHED*/
				}

				/* Read the contents of file */
				if (read(fildes, read_buffer, \
						 sizeof(read_buffer)) > 0) {
					if (memcmp(read_buffer, write_buffer, strlen(write_buffer))) {
						tst_resm(TFAIL, "Data read "
							"from %s doesn't match "
							"with witten data",
							TEMP_FILE);
					} else {
						tst_resm(TPASS, "Functionality "
							"of sync() successful");
					}
				} else {
					tst_brkm(TFAIL, cleanup,
						 "read() Fails on %s, error=%d",
						 TEMP_FILE, errno);
						/*NOTREACHED*/
				}
			} else {
				tst_resm(TPASS, "call succeeded");
			}
		}
		Tst_count++;			/* incr. TEST_LOOP counter */
	}	/* End for TEST_LOOPING */

	/* Call cleanup() to undo setup done for the test. */
	cleanup();
	/*NOTREACHED*/

}	/* End main */

/*
 * void
 * setup() - performs all ONE TIME setup for this test.
 *  Create a temporary directory and change directory to it.
 *  Create a test file under temporary directory and write some
 *  data into it.
 */
void 
setup()
{
	/* capture signals */
	tst_sig(NOFORK, DEF_HANDLER, cleanup);

	/* Pause if that option was specified
	 * TEST_PAUSE contains the code to fork the test with the -i option.
	 * You want to make sure you do this before you create your temporary
	 * directory.
	 */
	TEST_PAUSE;

	/* make a temp directory and cd to it */
	tst_tmpdir();

	/* Copy some data into data buffer */
	strcpy(write_buffer,  "abcdefghijklmnopqrstuvwxyz");

	/* Creat a temporary file under above directory */
	if ((fildes = open(TEMP_FILE, O_RDWR | O_CREAT, FILE_MODE)) == -1) {
		tst_brkm(TBROK, cleanup,
			 "open(%s, O_RDWR | O_CREAT, %#o) Failed, errno=%d :%s",
			 TEMP_FILE, FILE_MODE, errno, strerror(errno));
		/*NOTREACHED*/
	}

	/* Write the buffer data into file */
	if (write(fildes, write_buffer, strlen(write_buffer)) != \
				(int)strlen(write_buffer)) {
		tst_brkm(TBROK, cleanup,
			 "write() failed to write buffer data to %s",
			 TEMP_FILE);
		/*NOTREACHED*/
	}
	
}	/* End setup() */

/*
 * void
 * cleanup() - performs all ONE TIME cleanup for this test at
 *             completion or premature exit.
 *  Remove the test directory and testfile created in the setup.
 */
void 
cleanup()
{
	/*
	 * print timing stats if that option was specified.
	 * print errno log if that option was specified.
	 */
	TEST_CLEANUP;

	/* Close the temporary file */
	if (close(fildes) == -1) {
		tst_brkm(TFAIL, NULL,
			 "close(%s) Failed, errno=%d : %s",
			 TEMP_FILE, errno, strerror(errno));
	}

	/* Remove tmp dir and all files in it */
	tst_rmdir();

	/* exit with return code appropriate for results */
	tst_exit();
}	/* End cleanup() */
