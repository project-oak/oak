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
 * NAME
 * 	chdir02.c
 *
 * DESCRIPTION
 *	Testcase to test whether chdir(2) sets errno correctly.
 * 
 * ALGORITHM
 *	1.	Test for ENAMETOOLONG:
 *		Create a bad directory name with length more than
 *
 *		VFS_MAXNAMELEN (Linux kernel variable), and attempt to
 *		chdir(2) to it.
 *
 *	2.	Test for ENOENT:
 *		Attempt to chdir(2) on a non-existent directory
 *
 *	3.	Test for EFAULT:
 *		Pass an address which lies outside the address space of the
 *		process, and expect an EFAULT.
 *
 * USAGE:  <for command-line>
 * chdir02 [-c n] [-e] [-i n] [-I x] [-P x] [-t]
 *     where,  -c n : Run n copies concurrently.
 *             -e   : Turn on errno logging.
 *             -i n : Execute test n times.
 *             -I x : Execute test for x seconds.
 *             -P x : Pause for x seconds between iterations.
 *             -t   : Turn on syscall timing.
 *
 * HISTORY
 *	07/2001 Ported by Wayne Boyer
 *
 * RESTRICTIONS
 *	NONE
 */

#include <errno.h>
#include <sys/stat.h>
#include <test.h>
#include <usctest.h>

const char *TCID = "chdir02";
int TST_TOTAL = 3;
extern int Tst_count;

int exp_enos[] = {ENAMETOOLONG, ENOENT, EFAULT, 0};

char bad_dir[] = "abcdefghijklmnopqrstmnopqrstuvwxyzabcdefghijklmnopqrstmnopqrstuvwxyzabcdefghijklmnopqrstmnopqrstuvwxyzabcdefghijklmnopqrstmnopqrstuvwxyzabcdefghijklmnopqrstmnopqrstuvwxyzabcdefghijklmnopqrstmnopqrstuvwxyzabcdefghijklmnopqrstmnopqrstuvwxyzabcdefghijklmnopqrstmnopqrstuvwxyz"; 

char noexist_dir[] = "/tmp/noexistdir";

struct test_case_t {
	char *dname;
	int error;
} TC[] = {
	/*
 	 * to test whether chdir() is setting ENAMETOOLONG if the
	 * directory is more than VFS_MAXNAMELEN
 	 */
	{bad_dir, ENAMETOOLONG},

	/*
	 * to test whether chdir() is setting ENOENT if the
	 * directory is not existing.
	 */
	{noexist_dir, ENOENT},

	/*
	 * to test whether chdir() is setting EFAULT if the
	 * directory is an invalid address.
	 */
	{(void *)-1, EFAULT}
};

int flag;
#define	FAILED	1

void setup(void);
void cleanup(void) __attribute__((noreturn));

int
main(int ac, char **av)
{
	int lc;				/* loop counter */
	int i;
	const char *msg;		/* message returned from parse_opts */

	/* parse standard options */
	if ((msg = parse_opts(ac, av, (option_t *)NULL, NULL)) != (char *)NULL){
		tst_brkm(TBROK, cleanup, "OPTION PARSING ERROR - %s", msg);
	}

	setup();

	/* set up the expected errnos */
	TEST_EXP_ENOS(exp_enos);

	/* check looping state if -i option is given */
	for (lc = 0; TEST_LOOPING(lc); lc++) {
		/* reset Tst_count in case we are looping */
		Tst_count = 0;

		/* loop through the test cases */
		for (i=0; i<TST_TOTAL; i++) {

			TEST(chdir(TC[i].dname));

			if (TEST_RETURN != -1) {
				tst_resm(TFAIL, "call succeeded unexpectedly");
				continue;
			}

			TEST_ERROR_LOG(TEST_ERRNO);

			if (TEST_ERRNO == TC[i].error) {
				tst_resm(TPASS, "expected failure - "
					 "errno = %d : %s", TEST_ERRNO,
					 strerror(TEST_ERRNO));
			} else {
				tst_resm(TFAIL, "unexpected error - %d : %s - "
					 "expected %d", TEST_ERRNO,
					 strerror(TEST_ERRNO), TC[i].error);
			}
		}
	}
	cleanup();

	/*NOTREACHED*/
}

/*
 * setup() - performs all ONE TIME setup for this test.
 */
void
setup()
{
	/* capture signals */
	tst_sig(NOFORK, DEF_HANDLER, cleanup);

	/* Pause if that option was specified */
	TEST_PAUSE;

	/* make a temporary directory and cd to it */
	tst_tmpdir();
}


/*
 * cleanup() - performs all ONE TIME cleanup for this test at
 *	       completion or premature exit.
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
	 * Delete the test directory created in setup().
	 */
	tst_rmdir();

	/* exit with return code appropriate for results */
	tst_exit();
}
