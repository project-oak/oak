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
 * Test Name: stat03
 *
 * Test Description:
 *   Verify that,
 *   1) stat(2) returns -1 and sets errno to EACCES if search permission is
 *      denied on a component of the path prefix.
 *   2) stat(2) returns -1 and sets errno to ENOENT if the specified file
 *	does not exists or empty string.
 *   3) stat(2) returns -1 and sets errno to EFAULT if pathname points
 *	outside user's accessible address space.
 *   4) stat(2) returns -1 and sets errno to ENAMETOOLONG if the pathname
 *	component is too long.
 *   5) stat(2) returns -1 and sets errno to ENOTDIR if the directory
 *	component in pathname is not a directory.
 *
 * Expected Result:
 *  stat() should fail with return value -1 and set expected errno.
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
 *   	if errno set == expected errno
 *   		Issue sys call fails with expected return value and errno.
 *   	Otherwise,
 *		Issue sys call fails with unexpected errno.
 *   Otherwise,
 *	Issue sys call returns unexpected value.
 *
 *  Cleanup:
 *   Print errno log and/or timing stats if options given
 *   Delete the temporary directory(s)/file(s) created.
 *
 * Usage:  <for command-line>
 *  stat03 [-c n] [-e] [-i n] [-I x] [-p x] [-t]
 *	where,  -c n : Run n copies concurrently.
 *		-e   : Turn on errno logging.
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
 *
 */

#include <fcntl.h>
#include <errno.h>
#include <string.h>
#include <signal.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <pwd.h>

#include "test.h"
#include "usctest.h"

#define MODE_RWX	S_IRWXU | S_IRWXG | S_IRWXO
#define FILE_MODE	S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH
#define DIR_TEMP	"testdir_1"
#define TEST_FILE1	"testdir_1/tfile_1"
#define TEST_FILE2	"t_file/tfile_2"

int no_setup();
int setup1();			/* setup function to test chmod for EACCES */
int setup2();			/* setup function to test chmod for ENOTDIR */
int longpath_setup();	/* setup function to test chmod for ENAMETOOLONG */
char nobody_uid[] = "nobody";
struct passwd *ltpuser;


char Longpathname[PATH_MAX+2];
char High_address_node[64];

struct test_case_t {		/* test case struct. to hold ref. test cond's*/
	const char *pathname;
	const char *desc;
	int exp_errno;
	int (*setupfunc)();
} Test_cases[] = {
#ifndef __CYGWIN__
	{ TEST_FILE1,  "No Search permissions to process", EACCES, setup1 },
#endif
	{ High_address_node, "Address beyond address space", EFAULT, no_setup },
	{ (char *)-1, "Negative address", EFAULT, no_setup },
	{ Longpathname, "Pathname too long", ENAMETOOLONG, longpath_setup },
	{ "", "Pathname is empty", ENOENT, no_setup },
#ifndef __CYGWIN__
	{ TEST_FILE2, "Path contains regular file", ENOTDIR, setup2 },
#endif
	{ NULL, NULL, 0, no_setup }
};

const char *TCID="stat03";           /* Test program identifier.    */
int TST_TOTAL = 6;		/* Total number of test cases. */
extern int Tst_count;           /* Test Case counter for tst_* routines */
int exp_enos[]={EACCES, EFAULT, ENAMETOOLONG, ENOENT, ENOTDIR, 0};

void setup();			/* Main setup function for the tests */
void cleanup(void) __attribute__((noreturn));			/* cleanup function for the test */
char *get_high_address(void);

int
main(int ac, char **av)
{
	struct stat stat_buf;	/* stat structure buffer */
	int lc;			/* loop counter */
	const char *msg;	/* message returned from parse_opts */
	const char *file_name;	/* ptr. for file name whose mode is modified*/
	const char *test_desc;	/* test specific error message */
	int ind;		/* counter to test different test conditions */

	/* Parse standard options given to run the test. */
	msg = parse_opts(ac, av, (option_t *) NULL, NULL);
	if (msg != (char *) NULL) {
		tst_brkm(TBROK, NULL, "OPTION PARSING ERROR - %s", msg);
		tst_exit();
		/*NOTREACHED*/
	}

	/*
	 * Invoke setup function to call individual test setup functions
	 * to simulate test conditions.
	 */
	setup();

	/* set the expected errnos... */
	TEST_EXP_ENOS(exp_enos);

	/* Check looping state if -i option given */
	for (lc = 0; TEST_LOOPING(lc); lc++) {
		/* Reset Tst_count in case we are looping. */
		Tst_count=0;

		for (ind = 0; Test_cases[ind].desc != NULL; ind++) {
			file_name = Test_cases[ind].pathname;
			test_desc = Test_cases[ind].desc;

			if (file_name == High_address_node) {
				file_name = (char *)get_high_address();
			}

			/*
			 * Call stat(2) to test different test conditions.
			 * verify that it fails with -1 return value and
			 * sets appropriate errno.
			 */
			TEST(stat(file_name, &stat_buf));
	
			/* Check return code from stat(2) */
			if (TEST_RETURN == -1) {
				TEST_ERROR_LOG(TEST_ERRNO);
				if (TEST_ERRNO == Test_cases[ind].exp_errno) {
					tst_resm(TPASS,
						 "stat() fails, %s, errno:%d",
						 test_desc, TEST_ERRNO);
				} else {
					tst_resm(TFAIL, "stat() fails, %s,"
						" errno:%d, expected errno:%d",
						test_desc, TEST_ERRNO,
						Test_cases[ind].exp_errno);
				}
			} else {
				tst_resm(TFAIL, "stat(2) returned %d,"
					" expected -1, errno:%d", TEST_RETURN,
					 Test_cases[ind].exp_errno);
			}
		}	/* End of TEST CASE LOOPING. */
		Tst_count++;			/* incr TEST_LOOP counter */
	}	/* End for TEST_LOOPING */

	/*
	 * Invoke cleanup() to delete the test directory/file(s) created
	 * in the setup().
	 */
	cleanup();
	/*NOTREACHED*/

}	/* End main */

/*
 * void 
 * setup(void) - performs all ONE TIME setup for this test.
 * 	Exit the test program on receipt of unexpected signals.
 *	Create a temporary directory and change directory to it.
 *	Invoke individual test setup functions according to the order
 *	set in struct. definition.
 */
void
setup()
{
	int ind;			/* counter for setup functions */

	/* Capture unexpected signals */
	tst_sig(FORK, DEF_HANDLER, cleanup);
#if 0
	/* Switch to nobody user for correct error code collection */
        if (geteuid() != 0) {
                tst_brkm(TBROK, tst_exit, "Test must be run as root");
        }
         ltpuser = getpwnam(nobody_uid);
         if (setuid(ltpuser->pw_uid) == -1) {
                tst_resm(TINFO, "setuid failed to "
                         "to set the effective uid to %d",
                         ltpuser->pw_uid);
                perror("setuid");
         }
#endif
	/* Pause if that option was specified
	 * TEST_PAUSE contains the code to fork the test with the -i option.
	 * You want to make sure you do this before you create your temporary
	 * directory.
	 */
	TEST_PAUSE;

	/* Make a temp dir and cd to it */
	tst_tmpdir();

	/* call individual setup functions */
	for (ind = 0; Test_cases[ind].desc != NULL; ind++) {
		Test_cases[ind].setupfunc();
	}
}	/* End setup() */

/*
 * int
 * no_setup() - Some test conditions for stat(2) do not any setup.
 *              Hence, this function just returns 0.
 *  This function simply returns 0.
 */
int
no_setup()
{
        return 0;
}


/*
 * int
 * setup1() - setup function for a test condition for which stat(2)
 *	      returns -1 and sets errno to EACCES.
 *  Create a test directory under temporary directory and create a test file
 *  under this directory with mode "0666" permissions.
 *  Modify the mode permissions on test directory such that process will not
 *  have search permissions on test directory.
 *
 *  The function returns 0.
 */
int
setup1()
{
	int fd;			/* file handle for testfile */

	/* Creat a test directory */
	if (mkdir(DIR_TEMP, MODE_RWX) < 0) {
		tst_brkm(TBROK, cleanup, "mkdir(2) of %s failed", DIR_TEMP);
		/*NOTREACHED*/
	}

	/* Creat a test file under above test directory */
	if ((fd = open(TEST_FILE1, O_RDWR|O_CREAT, 0666)) == -1) {
		tst_brkm(TBROK, cleanup,
			 "open(%s, O_RDWR|O_CREAT, 0666) failed, errno=%d : %s",
			 TEST_FILE1, errno, strerror(errno));
		/*NOTREACHED*/
	}
	/* Close the test file */
	if (close(fd) == -1) {
		tst_brkm(TBROK, cleanup,
			 "close(%s) Failed, errno=%d : %s",
			 TEST_FILE1, errno, strerror(errno));
		/*NOTREACHED*/
	}

	/* Modify mode permissions on test directory */
	if (chmod(DIR_TEMP, FILE_MODE) < 0) {
		tst_brkm(TBROK, cleanup, "chmod(2) of %s failed", DIR_TEMP);
		/*NOTREACHED*/
	}
	return 0;
}

/*
 * int
 * setup2() - setup function for a test condition for which stat(2)
 *	     returns -1 and sets errno to ENOTDIR.
 * 
 *  Create a test file under temporary directory so that test tries to
 *  change mode of a testfile "tfile_2" under "t_file" which happens to be
 *  another regular file.
 */
int
setup2()
{
	int fd;				/* File handle for test file */
	
	/* Creat a test file under temporary directory */
	if ((fd = open("t_file", O_RDWR|O_CREAT, MODE_RWX)) == -1) {
		tst_brkm(TBROK, cleanup,
			 "open(2) on t_file failed, errno=%d : %s",
			 errno, strerror(errno));
		/*NOTREACHED*/
	}
	/* Close the test file created above */
	if (close(fd) == -1) {
		tst_brkm(TBROK, cleanup,
			 "close(t_file) Failed, errno=%d : %s",
			 errno, strerror(errno));
		/*NOTREACHED*/
	}
	return 0;
}

/*
 * int
 * longpath_setup() - setup to create a node with a name length exceeding
 *                    the MAX. length of PATH_MAX.
 *   This function retruns 0.
 */
int
longpath_setup()
{
	int ind;                /* counter variable */

	for (ind = 0; ind <= (PATH_MAX + 1); ind++) {
		Longpathname[ind] = 'a';
	}
	return 0;
}

/*
 * void
 * cleanup() - Performs all ONE TIME cleanup for this test at
 *             completion or premature exit.
 *	Print test timing stats and errno log if test executed with options.
 *	Remove temporary directory and sub-directories/files under it
 *	created during setup().
 *	Exit the test program with normal exit code.
 */
void
cleanup()
{
	/*
	 * print timing stats if that option was specified.
	 * print errno log if that option was specified.
	 */
	TEST_CLEANUP;

#ifndef __CYGWIN__	
	/* Restore mode permissions on test directory created in setup2() */
	if (chmod(DIR_TEMP, MODE_RWX) < 0) {
		tst_brkm(TFAIL, NULL, "chmod(2) of %s failed", DIR_TEMP);
	}
#endif

	/* Remove files and temporary directory created */
	tst_rmdir();
  
	/* exit with return code appropriate for results */
	tst_exit();
}	/* End cleanup() */
