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
 *	pipe10.c
 *
 * DESCRIPTION
 *	Check that parent can open a pipe and have a child read from it
 *
 * ALGORITHM
 *	Parent opens pipe, child reads. Passes if child can read all the
 *	characters written by the parent.
 *
 * USAGE:  <for command-line>
 *  pipe10 [-c n] [-f] [-i n] [-I x] [-P x] [-t]
 *     where,  -c n : Run n copies concurrently.
 *             -f   : Turn off functionality Testing.
 *             -i n : Execute test n times.
 *             -I x : Execute test for x seconds.
 *             -P x : Pause for x seconds between iterations.
 *             -t   : Turn on syscall timing.
 *
 * HISTORY
 *	07/2001 Ported by Wayne Boyer
 *
 * RESTRICTIONS
 *	None
 */
#include <errno.h>
#include <sys/wait.h>
#include <test.h>
#include <usctest.h>

const char *TCID = "pipe10";
int TST_TOTAL = 1;
extern int Tst_count;

void setup(void);
void cleanup(void) __attribute__((noreturn));

int
main(int ac, char **av)
{
	int lc;				/* loop counter */
	const char *msg;		/* message returned from parse_opts */

	int fd[2];			/* fds for pipe read/write */
	char wrbuf[BUFSIZ], rebuf[BUFSIZ];
	int red, written;		/* no of chars read and */ 
					/* written to pipe */
	int length, greater, forkstat;

	/* parse standard options */
	if ((msg = parse_opts(ac, av, (option_t *)NULL, NULL)) != (char *)NULL){
		tst_brkm(TBROK, tst_exit, "OPTION PARSING ERROR - %s", msg);
		/*NOTREACHED*/
	}

	setup();

	for (lc = 0; TEST_LOOPING(lc); lc++) {

		/* reset Tst_count in case we are looping */
		Tst_count = 0;

		TEST(pipe(fd));

		if (TEST_RETURN == -1) {
			tst_resm(TFAIL, "pipe creation failed");
			continue;
		}

		if (!STD_FUNCTIONAL_TEST) {
			tst_resm(TPASS, "call succeeded");
			continue;
		}

		strcpy(wrbuf, "abcdefghijklmnopqrstuvwxyz\0");
		length = strlen(wrbuf);

		written = write(fd[1], wrbuf, length);

		/* did write write at least some chars */
		if ((written < 0) || (written > length)) {
			tst_brkm(TBROK, cleanup, "write to pipe failed");
		}

		forkstat = fork();

		if (forkstat == -1) {
			tst_brkm(TBROK, cleanup, "fork() failed");
			/*NOTREACHED*/
		}

		if (forkstat == 0) {		/* child */
			red = read(fd[0], rebuf, written);

			/* did read , get at least some chars */
			if ((red < 0) || (red > written)) {
				tst_brkm(TBROK, cleanup, "read pipe failed");
			}

			greater = memcmp(rebuf, wrbuf, red);

			/* are the strings written and read equal */
			if (greater == 0) {
				tst_resm(TPASS, "functionality is correct");
			} else {
				tst_resm(TFAIL, "read & write strings do "
					 "not match");
			}
		} else {	/* parent */
			/* let the child carry on */
			exit(0);
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
	tst_sig(FORK, DEF_HANDLER, cleanup);

	/* Pause if that option was specified */
	TEST_PAUSE;
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

	/* exit with return code appropriate for results */
	tst_exit();
}
