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
 * Test Name: access03
 *
 * Test Description:
 *  Verify that,
 *   1. access() fails with -1 return value and sets errno to EACCES
 *      if the permission bits of the file mode do not permit the
 *	 requested (Read/Write/Execute) access.
 *   2. access() fails with -1 return value and sets errno to EINVAL
 *	if the specified access mode argument is invalid.
 *   3. access() fails with -1 return value and sets errno to EFAULT
 *	if the pathname points outside allocate address space for the
 *	process.
 *   4. access() fails with -1 return value and sets errno to ENOENT
 *	if the specified file doesn't exist (or pathname is NULL).
 *   5. access() fails with -1 return value and sets errno to ENAMETOOLONG
 *      if the pathname size is > PATH_MAX characters.
 *
 * Expected Result:
 *  access() should fail with return value -1 and set expected errno.
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
 *  access03 [-c n] [-e] [-i n] [-I x] [-P x] [-t]
 *     where,  -c n : Run n copies concurrently.
 *             -e   : Turn on errno logging.
 *	       -i n : Execute test n times.
 *	       -I x : Execute test for x seconds.
 *	       -P x : Pause for x seconds between iterations.
 *	       -t   : Turn on syscall timing.
 *
 * HISTORY
 *	07/2001 Ported by Wayne Boyer
 *
 * RESTRICTIONS:
 *  This test should be run by 'non-super-user' only.
 * 
 */

#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <signal.h>
#include <sys/types.h>
#include <sys/stat.h>

#include "test.h"
#include "usctest.h"

#define INV_OK		-1
#define TEST_FILE1	"test_file1"
#define TEST_FILE2	"test_file2"
#define TEST_FILE3	"test_file3"
#define TEST_FILE4	"test_file4"

#define FILE_MODE	S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH

int no_setup();
int setup1();			/* setup() to test access() for EACCES */
int setup2();			/* setup() to test access() for EACCES */
int setup3();			/* setup() to test access() for EACCES */
int setup4();			/* setup() to test access() for EINVAL */
int longpath_setup();	/* setup function to test access() for ENAMETOOLONG */

char Longpathname[PATH_MAX+2];
char High_address_node[64];

struct test_case_t {		/* test case structure */
	const char *pathname;
	int a_mode;
	const char *desc;
	int exp_errno;
	int (*setupfunc)();
} Test_cases[] = {
	{ TEST_FILE1, R_OK, "Read Access denied on file", EACCES, setup1 },
	{ TEST_FILE2, W_OK, "Write Access denied on file", EACCES, setup2 },
	{ TEST_FILE3, X_OK, "Execute Access denied on file", EACCES, setup3 },
	{ TEST_FILE4, INV_OK, "Access mode invalid", EINVAL, setup4 },
	{ High_address_node, R_OK, "Address beyond address space", EFAULT, no_setup },
	{ (char *)-1, R_OK, "Negative address", EFAULT, no_setup },
	{ "", W_OK, "Pathname is empty", ENOENT, no_setup },
	{ Longpathname, R_OK, "Pathname too long", ENAMETOOLONG, longpath_setup },
	{ NULL, 0, NULL, 0, no_setup }
};

const char *TCID="access03";		/* Test program identifier.    */
int TST_TOTAL=8;		/* Total number of test cases. */
extern int Tst_count;		/* Test Case counter for tst_* routines */
int exp_enos[]={EACCES, EFAULT, EINVAL, ENOENT, ENAMETOOLONG, 0};

void setup();			/* Main setup function of test */
void cleanup(void) __attribute__((noreturn));			/* cleanup function for the test */
char *get_high_address (void);

int
main(int ac, char **av)
{
	int lc;			/* loop counter */
	const char *msg;	/* message returned from parse_opts */
	const char *file_name;	/* name of the testfile */
	const char *test_desc;	/* test specific message */
	int access_mode;	/* specified access mode for testfile */
	int ind;		/* counter for testcase looping */

	/* Parse standard options given to run the test. */
	msg = parse_opts(ac, av, (option_t *) NULL, NULL);
	if (msg != (char *) NULL) {
		tst_brkm(TBROK, tst_exit, "OPTION PARSING ERROR - %s", msg);
	}

	/* Perform global setup for test */
	setup();

	/* set the expected errnos... */
	TEST_EXP_ENOS(exp_enos);

	/* Check looping state if -i option given */
	for (lc = 0; TEST_LOOPING(lc); lc++) {
		/* Reset Tst_count in case we are looping. */
		Tst_count = 0;

		for (ind = 0; Test_cases[ind].desc != NULL; ind++) {
			file_name = Test_cases[ind].pathname;
			access_mode = Test_cases[ind].a_mode;
			test_desc = Test_cases[ind].desc;

			if (file_name == High_address_node) {
				file_name = (char *)get_high_address();
			}

			/* 
			 * Call access(2) to test different test conditions.
			 * verify that it fails with -1 return value and
			 * sets appropriate errno.
			 */
			TEST(access(file_name, access_mode));

			if (TEST_RETURN != -1) {
				tst_resm(TFAIL, "access() returned %d, "
					 "expected -1, errno:%d", TEST_RETURN,
					 Test_cases[ind].exp_errno);
				continue;
			}

			TEST_ERROR_LOG(TEST_ERRNO);

			/*
			 * Call a function to verify whether
			 * the specified file has specified 
			 * access mode.
			 */
			if (TEST_ERRNO == Test_cases[ind].exp_errno) {
				tst_resm(TPASS, "access() fails, %s, errno:%d",
					 test_desc, TEST_ERRNO);
			} else {
				tst_resm(TFAIL, "access() fails, %s, errno:%d, "
					 "expected errno:%d", test_desc,
					 TEST_ERRNO, Test_cases[ind].exp_errno);
			}
		}	/* Test Case Looping */
	}	/* End for TEST_LOOPING */

	/* Call cleanup() to undo setup done for the test. */
	cleanup();

	/*NOTREACHED*/
}

/*
 * setup() - performs all ONE TIME setup for this test.
 *
 *  Create a temporary directory and change directory to it.
 *  Call individual test specific setup functions.
 */
void 
setup()
{
	int ind;			/* counter for testsetup functions */

	/* capture signals */
	tst_sig(NOFORK, DEF_HANDLER, cleanup);

	/* Check that the test process id is not root/super-user */
	if (geteuid() == 0) {
		tst_brkm(TBROK, NULL, "Must be non-root/super for this test!");
		tst_exit();
	}

	/* Pause if that option was specified */
	TEST_PAUSE;

	/* make a temp directory and cd to it */
	tst_tmpdir();

	/* call individual setup functions */
	for (ind = 0; Test_cases[ind].desc != NULL; ind++) {
		Test_cases[ind].setupfunc();
	}
}

/*
 * no_setup() - some test conditions do not need any setup.
 *		Hence, this function simply returns 0.
 */
int
no_setup()
{
	return 0;
}

/*
 * setup1() - Setup function to test access() for return value -1
 *	      and errno EACCES when read access denied for specified
 *	      testfile.
 *
 *   Creat/open a testfile and close it.
 *   Deny read access permissions on testfile.
 *   This function returns 0.
 */
int
setup1()
{
	int fd1;			/* file handle for testfile */

	/* Creat a test file under above directory created */
	if ((fd1 = open(TEST_FILE1, O_RDWR|O_CREAT, FILE_MODE)) == -1) {
		tst_brkm(TBROK, cleanup,
			 "open(%s, O_RDWR|O_CREAT, %#o) Failed, errno=%d :%s",
			 TEST_FILE1, FILE_MODE, errno, strerror(errno));
	}

	/* Close the testfile created above */
	if (close(fd1) == -1) {
		tst_brkm(TBROK, cleanup, "close(%s) Failed, errno=%d : %s",
			 TEST_FILE1, errno, strerror(errno));
	}

	/* Change mode permissions on testfile */
	if (chmod(TEST_FILE1, 0333) < 0) { 
		tst_brkm(TBROK, cleanup, "chmod() failed on %s, errno=%d",
			 TEST_FILE1, errno);
	}

	return 0;
}

/*
 * setup2() - Setup function to test access() for return value -1 and
 *	      errno EACCES when write access denied on testfile.
 *
 *   Creat/open a testfile and close it.
 *   Deny write access permissions on testfile.
 *   This function returns 0.
 */
int
setup2()
{
	int fd2;			/* file handle for testfile */

	/* Creat a test file under above directory created */
	if ((fd2 = open(TEST_FILE2, O_RDWR|O_CREAT, FILE_MODE)) == -1) {
		tst_brkm(TBROK, cleanup,
			 "open(%s, O_RDWR|O_CREAT, %#o) Failed, errno=%d :%s",
			 TEST_FILE2, FILE_MODE, errno, strerror(errno));
	}

	/* Close the testfile created above */
	if (close(fd2) == -1) {
		tst_brkm(TBROK, cleanup, "close(%s) Failed, errno=%d : %s",
			 TEST_FILE2, errno, strerror(errno));
	}

	/* Change mode permissions on testfile */
	if (chmod(TEST_FILE2, 0555) < 0) { 
		tst_brkm(TBROK, cleanup, "chmod() failed on %s, errno=%d",
			 TEST_FILE2, errno);
	}

	return 0;
}

/*
 * setup3() - Setup function to test access() for return value -1 and
 *	      errno EACCES when execute access denied on testfile.
 *
 *   Creat/open a testfile and close it.
 *   Deny search access permissions on testfile.
 *   This function returns 0.
 */
int
setup3()
{
	int fd3;			/* file handle for testfile */

	/* Creat a test file under above directory created */
	if ((fd3 = open(TEST_FILE3, O_RDWR|O_CREAT, FILE_MODE)) == -1) {
		tst_brkm(TBROK, cleanup,
			 "open(%s, O_RDWR|O_CREAT, %#o) Failed, errno=%d :%s",
			 TEST_FILE3, FILE_MODE, errno, strerror(errno));
	}

	/* Close the testfile created above */
	if (close(fd3) == -1) {
		tst_brkm(TBROK, cleanup, "close(%s) Failed, errno=%d : %s",
			 TEST_FILE3, errno, strerror(errno));
	}

	/* Change mode permissions on testfile */
	if (chmod(TEST_FILE3, 0666) < 0) { 
		tst_brkm(TBROK, cleanup, "chmod() failed on %s, errno=%d",
			 TEST_FILE3, errno);
	}

	return 0;
}

/*
 * setup4() - Setup function to test access() for return value -1
 *	      and errno EINVAL when specified access mode argument is
 *	      invalid.
 *
 *   Creat/open a testfile and close it.
 *   This function returns 0.
 */
int
setup4()
{
	int fd4;			/* file handle for testfile */

	/* Creat a test file under above directory created */
	if ((fd4 = open(TEST_FILE4, O_RDWR|O_CREAT, FILE_MODE)) == -1) {
		tst_brkm(TBROK, cleanup,
			 "open(%s, O_RDWR|O_CREAT, %#o) Failed, errno=%d :%s",
			 TEST_FILE4, FILE_MODE, errno, strerror(errno));
	}

	/* Close the testfile created above */
	if (close(fd4) == -1) {
		tst_brkm(TBROK, cleanup, "close(%s) Failed, errno=%d : %s",
			 TEST_FILE4, errno, strerror(errno));
	}

	return 0;
}

/*
 * longpath_setup() - setup to create a node with a name length exceeding
 * 		      the MAX. length of PATH_MAX.
 */
int
longpath_setup()
{
	int ind;

	for (ind = 0; ind <= (PATH_MAX + 1); ind++) {
		Longpathname[ind] = 'a';
	}

	return 0;
}

/*
 * cleanup() - performs all ONE TIME cleanup for this test at
 *             completion or premature exit.
 *
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

	/*
	 * Delete the test directory/file and temporary directory
	 * created in the setup.
	 */
	tst_rmdir();

	/* exit with return code appropriate for results */
	tst_exit();
}
