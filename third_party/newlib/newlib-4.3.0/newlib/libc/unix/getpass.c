#ifndef _NO_GETPASS
/*
 * Copyright (c) 1988 The Regents of the University of California.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 4. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#if defined(LIBC_SCCS) && !defined(lint)
static char sccsid[] = "@(#)getpass.c	5.9 (Berkeley) 5/6/91";
#endif /* LIBC_SCCS and not lint */

#include <stdio.h>
#include <unistd.h>
#include <pwd.h>
#include <sys/termios.h>
#include <sys/signal.h>
#include <_syslist.h>

#ifndef _PATH_PASSWD
#define _PATH_PASSWD            "/etc/passwd"
#endif

#ifndef _PASSWORD_LEN
#define _PASSWORD_LEN           128     /* max length, not counting NULL */
#endif

char *
getpass (prompt)
     const char *prompt;
{
  struct termios term;
  register int ch;
  register char *p;
  FILE *fp, *outfp;
  long omask;
  int echo;
  static char buf[_PASSWORD_LEN + 1];

  /*
   * read and write to /dev/tty if possible; else read from
   * stdin and write to stderr.
   */

  if ((outfp = fp = fopen ("/dev/tty", "w+")) == NULL)
    {
      outfp = stderr;
      fp = stdin;
    }
  /*
   * note - blocking signals isn't necessarily the
   * right thing, but we leave it for now.
   */
  omask = sigblock (sigmask (SIGINT) | sigmask (SIGTSTP));
  (void) tcgetattr (fileno (fp), &term);
  echo = (term.c_lflag & ECHO);
  if (echo)
    {
      term.c_lflag &= ~ECHO;
      (void) tcsetattr (fileno (fp), TCSAFLUSH, &term);
    }
  (void) fputs (prompt, outfp);
  rewind (outfp);		/* implied flush */
  for (p = buf; (ch = getc (fp)) != EOF && ch != '\n';)
    if (p < buf + _PASSWORD_LEN)
      *p++ = ch;
  *p = '\0';
  (void) write (fileno (outfp), "\n", 1);
  if (echo)
    {
      term.c_lflag |= ECHO;
      tcsetattr (fileno (fp), TCSAFLUSH, &term);
    }
  (void) sigsetmask (omask);
  if (fp != stdin)
    (void) fclose (fp);
  return buf;
}
#endif /* !_NO_GETPASS  */
