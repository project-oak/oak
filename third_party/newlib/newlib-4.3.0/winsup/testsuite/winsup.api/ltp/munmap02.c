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
 * Test Name: munmap02
 *
 * Test Description:
 *  Verify that, munmap call will succeed to unmap a mapped file or
 *  anonymous shared memory region from the calling process's address space
 *  if the region specified by the address and the length is part or all of
 *  the mapped region.
 *
 * Expected Result:
 *  munmap call should succeed to unmap a part or all of mapped region of a
 *  file or anonymous shared memory from the process's address space and it
 *  returns with a value 0, 
 *  further reference to the unmapped region should result in a segmentation
 *  fault (SIGSEGV).
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
 *  munmap01 [-c n] [-f] [-i n] [-I x] [-P x] [-t]
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
#include <errno.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/mman.h>

#include "test.h"
#include "usctest.h"

#define TEMPFILE	"mmapfile"

const char *TCID="munmap02";	/* Test program identifier.    */
int TST_TOTAL=1;		/* Total number of test cases. */
extern int Tst_count;		/* Test Case counter for tst_* routines */

size_t page_sz;			/* system page size */
char *addr;			/* addr of memory mapped region */
int fildes;			/* file descriptor for tempfile */
unsigned int map_len;		/* length of the region to be mapped */

void setup();			/* Main setup function of test */
void cleanup(void);		/* cleanup function for the test */
void sig_handler();		/* signal catching function */

int
main(int ac, char **av)
{
	int lc;			/* loop counter */
	const char *msg;	/* message returned from parse_opts */
	
	/* Parse standard options given to run the test. */
	msg = parse_opts(ac, av, (option_t *)NULL, NULL);
	if (msg != (char *)NULL) {
		tst_brkm(TBROK, tst_exit, "OPTION PARSING ERROR - %s", msg);
	}

	/* Check looping state if -i option given */
	for (lc = 0; TEST_LOOPING(lc); lc++) {

		/* Reset Tst_count in case we are looping. */
		Tst_count=0;

		/* Perform global setup for test */
		setup();

		/* 
		 * Call munmap to unmap the part of the mapped region of the
		 * temporary file from the address and length that is part of
		 * the mapped region.
		 */
		TEST(munmap(addr, map_len));

		/* Check for the return value of munmap() */
		if (TEST_RETURN == -1) {
			tst_resm(TFAIL, "munmap() fails, errno=%d : %s",
				 TEST_ERRNO, strerror(TEST_ERRNO));
			continue;
		}
		/*
		 * Perform functional verification if test
		 * executed without (-f) option.
		 */
		if (STD_FUNCTIONAL_TEST) {
			/*
			 * Check whether further reference is possible
			 * to the unmapped memory region by writing
			 * to the first byte of region with
			 * some arbitrary number.
			 */
			*addr = 50; 

			/* This message is printed if no SIGSEGV */
			tst_resm(TFAIL, "process succeeds to refer unmapped "
				 "memory region");
		} else {
			tst_resm(TPASS, "call succeeded");
		}

		/* Call cleanup() to undo setup done for the test. */
		cleanup();

	}	/* End for TEST_LOOPING */

	/* exit with return code appropriate for results */
	tst_exit();

	/*NOTREACHED*/
}	/* End main */

/*
 * setup() - performs all ONE TIME setup for this test.
 * Setup signal handler to catch SIGSEGV.
 * Get system page size, create a temporary file for reading/writing,
 * write one byte data into it, map the open file for the specified
 * map length.
 */
void 
setup()
{

	/* capture signals */
	tst_sig(NOFORK, DEF_HANDLER, cleanup);

	/* call signal function to trap the signal generated */
	if (signal(SIGSEGV, sig_handler) == SIG_ERR) {
		tst_brkm(TBROK, cleanup, "signal fails to catch signal");
		tst_exit();
	}

	/* Pause if that option was specified */
	TEST_PAUSE;

	/* Get the system page size */
	if ((page_sz = getpagesize()) < 0) {
		tst_brkm(TBROK, cleanup,
			 "getpagesize() fails to get system page size");
		tst_exit();
	}

	/*
	 * Get the length of the open file to be mapped into process
	 * address space.
	 */
	map_len = 3 * page_sz;

	/* make a temp directory and cd to it */
	tst_tmpdir();

	/* Creat a temporary file used for mapping */
	if ((fildes = open(TEMPFILE, O_RDWR | O_CREAT, 0666)) < 0) {
		tst_brkm(TBROK, cleanup, "open() on %s Failed, errno=%d : %s",
			 TEMPFILE, errno, strerror(errno));
		tst_exit();
	}

	/*
	 * move the file pointer to maplength position from the beginning
	 * of the file.
	 */
	if (lseek(fildes, map_len, SEEK_SET) == -1) {
		tst_brkm(TBROK, cleanup, "lseek() fails on %s, errno=%d : %s",
			 TEMPFILE, errno, strerror(errno));
		tst_exit();
	}

	/* Write one byte into temporary file */
	if (write(fildes, "a", 1) != 1) {
		tst_brkm(TBROK, cleanup, "write() on %s Failed, errno=%d : %s",
			 TEMPFILE, errno, strerror(errno));
		tst_exit();
	}
	
	/*
	 * map the open file 'TEMPFILE' from its beginning up to the maplength
	 * into the calling process's address space at the system choosen
	 * with read/write permissions to the the mapped region.
	 */
	addr = mmap(0, map_len, PROT_READ | PROT_WRITE,
		    MAP_FILE | MAP_SHARED, fildes, 0);

	/* check for the return value of mmap system call */
	if (addr == (char *)MAP_FAILED) {
		tst_brkm(TBROK, cleanup, "mmap() Failed on %s, errno=%d : %s",
			 TEMPFILE, errno, strerror(errno));
		tst_exit();
	}

	/*
	 * increment the start address of the region at which the file is
	 * mapped to a maplength of 3 times the system page size by the value
	 * of system  page size and decrement the maplength value by the value
	 * of system page size.
	 */
	addr = (char *)((long)addr + page_sz);
	map_len = map_len - page_sz;
}

/*
 * void
 * sig_handler() - signal catching function.
 *   This function is used to trap the signal generated when tried to read or
 *   write to the memory mapped region which is already detached from the
 *   calling process address space.
 *   this function is invoked when SIGSEGV generated and it calls test
 *   cleanup function and exit the program.
 */
void
sig_handler()
{
	tst_resm(TPASS, "Functionality of munmap() successful");

	/* Invoke test cleanup function and exit */
	cleanup();

	/* exit with return code appropriate for results */
	tst_exit();
}

/*
 * cleanup() - performs all ONE TIME cleanup for this test at
 *             completion or premature exit.
 *  Unmap the portion of the region of the file left unmapped.
 *  Close the temporary file.
 *  Remove the temporary directory.
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
	 * get the start address and length of the portion of
	 * the mapped region of the file.
	 */
	addr = (char *)((long)addr - page_sz);
	map_len = map_len - page_sz;

	/* unmap the portion of the region of the file left unmapped */
	if (munmap(addr, map_len) < 0) {
		tst_brkm(TBROK, NULL,
			 "munmap() fails to unmap portion of mapped region");
	}

	/* Close the temporary file */
	if (close(fildes) < 0) {
		tst_brkm(TBROK, NULL, "close() on %s Failed, errno=%d : %s",
			 TEMPFILE, errno, strerror(errno));
	}

	/* Remove the temporary directory and all files in it */
	tst_rmdir();
}
