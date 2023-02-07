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
 *	pipe01.c
 *
 * DESCRIPTION
 *	Testcase to check the basic functionality of the pipe(2) syscall:
 *	Check that both ends of the pipe (both file descriptors) are
 *	available to a process opening the pipe.
 *
 * ALGORITHM
 *	Write a string of characters down a pipe; read the string from the
 *	other file descriptor. Test passes if both can be done, as reported
 *	by the number of characters written and read.
 *
 * USAGE:  <for command-line>
 *  pipe01 [-c n] [-f] [-i n] [-I x] [-P x] [-t]
 *     where,  -c n : Run n copies concurrently.
 *             -f   : Turn off functionality Testing.
 *             -i n : Execute test n times.
 *             -I x : Execute test for x seconds.
 *             -P x : Pause for x seconds between iterations.
 *             -t   : Turn on syscall timing.
 *
 * RESTRICITONS
 *	NONE
 */
#include <errno.h>
#include "test.h"
#include "usctest.h"

const char *TCID = "pipe01";
int TST_TOTAL = 1;
extern int Tst_count;

void setup(void);
void cleanup(void) __attribute__((noreturn));

int
main(int ac, char **av)
{
	int lc;				/* loop counter */
	const char *msg;		/* message returned from parse_opts */

	int fildes[2];			/* fds for pipe read and write */
	char wrbuf[BUFSIZ], rebuf[BUFSIZ];
	int red, written;		/* no. of chars read/written to pipe */
	int greater, length;
	char *strcpy();

	/* parse standard options */
	if ((msg = parse_opts(ac, av, (option_t *)NULL, NULL)) != (char *)NULL){
		tst_brkm(TBROK, tst_exit, "OPTION PARSING ERROR - %s", msg);
		/*NOTREACHED*/
	}

	setup();

	for (lc = 0; TEST_LOOPING(lc); lc++) {

		/* reset Tst_count in case we are looping */
		Tst_count = 0;

		TEST(pipe(fildes));

		if (TEST_RETURN == -1) {
			tst_resm(TFAIL, "pipe() failed unexpectedly - errno %d",
				 TEST_ERRNO);
			continue;
		}

		if (STD_FUNCTIONAL_TEST) {

			strcpy(wrbuf, "abcdefghijklmnopqrstuvwxyz");
			length = strlen(wrbuf);

			if ((written = write(fildes[1], wrbuf, length)) == -1) {
				tst_brkm(TBROK, cleanup, "write() failed");
			}

			if ((written < 0) || (written > 26)) {
				tst_resm(TFAIL, "Condition #1 test failed");
				continue;
			}

			if ((red = read(fildes[0], rebuf, written)) == -1) {
				tst_brkm(TBROK, cleanup, "read() failed");
			}

			if ((red < 0) || (red > written)) {
				tst_resm(TFAIL, "Condition #2 test failed");
				continue;
			}

			/* are the strings written and read equal */
			if ((greater = memcmp(rebuf, wrbuf, red)) != 0) {
				tst_resm(TFAIL, "Condition #3 test failed");
				continue;
			}
			tst_resm(TPASS, "pipe() functionality is correct");
		} else {
			tst_resm(TPASS, "call succeeded");
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
