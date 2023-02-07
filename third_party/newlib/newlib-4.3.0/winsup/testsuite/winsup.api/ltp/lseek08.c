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
 * Test Name: lseek03
 *
 * Test Description:
 *  Verify that, lseek() call succeeds to set the file pointer position 
 *  to the end of the file when 'whence' value set to SEEK_END and any
 *  attempts to read from that position should fail.
 *
 * Expected Result:
 *  lseek() should return the offset which is set to the file size measured 
 *  in bytes. read() attempt should fail with -1 return value.
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
 *  lseek03 [-c n] [-f] [-i n] [-I x] [-P x] [-t]
 *     where,  -c n : Run n copies concurrently.
 *             -f   : Turn off functionality Testing.
 *	       -i n : Execute test n times.
 *	       -I x : Execute test for x seconds.
 *	       -P x : Pause for x seconds between iterations.
 *	       -t   : Turn on syscall timing.
 *
 * HISTORY
 *	07/2001 Ported by Wayne Boyer
 *
 * RESTRICTIONS:
 *  None.
 */

#include <sys/types.h>
#include <errno.h>
#include <fcntl.h>
#include <utime.h>
#include <string.h>
#include <sys/stat.h>
#include <signal.h>

#include "test.h"
#include "usctest.h"

#define TEMP_FILE	"tmp_file"
#define FILE_MODE	S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH

const char *TCID="lseek03";		/* Test program identifier.    */
int TST_TOTAL=1;		/* Total number of test cases. */
extern int Tst_count;		/* Test Case counter for tst_* routines */
int fildes;			/* file handle for temp file */
ssize_t file_size;		/* size of the temporary file */

void setup();			/* Main setup function of test */
void cleanup(void) __attribute__((noreturn));			/* cleanup function for the test */

int
main(int ac, char **av)
{
	int lc;			/* loop counter */
	const char *msg;	/* message returned from parse_opts */
	char read_buf[1];	/* data read from temp. file */
    
	/* Parse standard options given to run the test. */
	msg = parse_opts(ac, av, (option_t *) NULL, NULL);
	if (msg != (char *) NULL) {
		tst_brkm(TBROK, NULL, "OPTION PARSING ERROR - %s", msg);
		tst_exit();
	}

	/* Perform global setup for test */
	setup();

	/* Check looping state if -i option given */
	for (lc = 0; TEST_LOOPING(lc); lc++) {
		/* Reset Tst_count in case we are looping. */
		Tst_count=0;

		/* 
		 * Invoke lseek(2) to move the read/write file
		 * pointer/handle to the END of the file.
		 */
		TEST(lseek(fildes, 0, SEEK_END));

		/* check return code of lseek(2) */
		if (TEST_RETURN == (off_t)-1) {
			tst_resm(TFAIL, "lseek on (%s) Failed, errno=%d : %s",
				 TEMP_FILE, TEST_ERRNO, strerror(TEST_ERRNO));
			continue;
		}
		/*
		 * Perform functional verification if test
		 * executed without (-f) option.
		 */
		if (STD_FUNCTIONAL_TEST) {
			/*
			 * Check if the return value from lseek(2)
			 * is equal to the file_size.
			 */
			if (TEST_RETURN != file_size) {
				tst_resm(TFAIL, "lseek() returned incorrect "
					 "value %d, expected %d",
					 TEST_RETURN, file_size);
				continue;
			}
			/*
			 * The return value is okay, now attempt to read data
			 * from the file.  This should fail as the file pointer
			 * should be pointing to END OF FILE.
			 */
			read_buf[0] = '\0';
			if (read(fildes, &read_buf, sizeof(read_buf)) > 0) {
				tst_resm(TFAIL, "read() successful on %s",
					 TEMP_FILE);
			} else {
				tst_resm(TPASS, "Functionality of lseek() on "
					 "%s successful", TEMP_FILE);
			}
		} else {
			tst_resm(TPASS, "call succeeded");
		}
	}	/* End for TEST_LOOPING */

	/* Call cleanup() to undo setup done for the test. */
	cleanup();

	/* NOTREACHED*/
}	/* End main */

/*
 * setup() - performs all ONE TIME setup for this test.
 *	     Create a temporary directory and change directory to it.
 *	     Create a test file under temporary directory and write some
 *	     data into it.
 *	     Get the size of the file using fstat().
 */
void 
setup()
{
	struct stat stat_buf;		/* struct. buffer for stat(2) */
	char write_buf[BUFSIZ];		/* buffer to hold data */

	/* capture signals */
	tst_sig(NOFORK, DEF_HANDLER, cleanup);

	/* Pause if that option was specified */
	TEST_PAUSE;

	/* make a temp directory and cd to it */
	tst_tmpdir();

	/* Get the data to be written to temporary file */
	strcpy(write_buf, "abcdefg\n");

	/* Creat/open a temporary file under above directory */
	if ((fildes = open(TEMP_FILE, O_RDWR | O_CREAT, FILE_MODE)) == -1) {
		tst_brkm(TBROK, cleanup,
			 "open(%s, O_RDWR|O_CREAT, %#o) Failed, errno=%d :%s",
			 TEMP_FILE, FILE_MODE, errno, strerror(errno));
	}

	/* Write data into temporary file */
	if(write(fildes, write_buf, strlen(write_buf)) <= 0) {
		tst_brkm(TBROK, cleanup,
			 "write(2) on %s Failed, errno=%d : %s",
			 TEMP_FILE, errno, strerror(errno));
	}

	/* Get the size of the file using fstat */
	if (fstat(fildes, &stat_buf) < 0) {
		tst_brkm(TBROK, cleanup,
			 "fstat(2) on %s Failed, errno=%d : %s",
			 TEMP_FILE, errno, strerror(errno));
	}

	file_size = stat_buf.st_size;
}

/*
 * cleanup() - performs all ONE TIME cleanup for this test at
 *             completion or premature exit.
 *	       Remove the test directory and testfile created in the setup.
 */
void 
cleanup()
{
	/*
	 * print timing stats if that option was specified.
	 * print errno log if that option was specified.
	 */
	TEST_CLEANUP;

	/* Close the temporary file created */
	if (close(fildes) < 0) {
		tst_brkm(TFAIL, NULL,
			 "close(%s) Failed, errno=%d : %s:",
			 TEMP_FILE, errno, strerror(errno));
	}

	/* Remove tmp dir and all files in it */
	tst_rmdir();

	/* exit with return code appropriate for results */
	tst_exit();
}
