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
 *	umask02.c
 *
 * DESCRIPTION
 *	Check that umask changes the mask, and that the previous
 *	value of the mask is returned correctly for each value.
 *
 * ALGORITHM
 *	For each mask value (9 bits) set mask, and check that the return
 *	corresponds to the previous value set.
 *
 * USAGE:  <for command-line>
 *	umask02 [-c n] [-e] [-i n] [-I x] [-P x] [-t]
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
 * Restrictions
 *	None
 */

#include <sys/stat.h>
#include "test.h"
#include "usctest.h"

const char *TCID = "umask02";
int TST_TOTAL = 1;
extern int Tst_count;

void setup(void);
void cleanup(void) __attribute__((noreturn));

int
main(int argc, char **argv)
{
	int lc;				/* loop counter */
	const char *msg;		/* message returned from parse_opts */

	int uret = 0, i, mskval = 0000;

	/* parse standard options */
	if ((msg = parse_opts(argc, argv, (option_t *)NULL, NULL)) !=
		(char *) NULL) {
		tst_brkm(TBROK, cleanup, "OPTION PARSING ERROR - %s", msg);
		/*NOTREACHED*/
	}

	setup();

	/* Check for looping state if -i option is given */
	for (lc = 0; TEST_LOOPING(lc); lc++) {

		/* reset Tst_count in case we are looping */
		Tst_count = 0;

		for (umask(++mskval), i = 1; mskval < 01000;
			uret = umask(++mskval), i++) {
			if ((uret != mskval - 1) && (mskval != 0000)) {
				tst_brkm(TBROK, cleanup, "bad mask value "
					 "returned");
				/*NOTREACHED*/
			} else {
				 tst_resm(TPASS, "umask(%d) susuccessfully "
						"returned %d.", mskval, uret);
			}
		}
	mskval = 0000;
	uret = 0;
	tst_resm(TINFO, "end of loop %d\n", lc);
	}
	cleanup();
	/*NOTREACHED*/
}

/*
 * setup()
 *	performs all ONE TIME setup for this test
 */
void
setup(void)
{
	/* capture signals */
	tst_sig(FORK, DEF_HANDLER, cleanup);

	/* Pause if that option was specified
	 * TEST_PAUSE contains the code to fork the test with the -c option.
	 */
	TEST_PAUSE;
}

/*
 * cleanup()
 *	performs all ONE TIME cleanup for this test at
 *	completion or premature exit
 */
void
cleanup(void)
{
	/*
	 * print timing stats if that option was specified.
	 * print errno log if that option was specified.
	 */
	TEST_CLEANUP;

	/* exit with return code appropriate for results */
	tst_exit();
	/*NOTREACHED*/
}
