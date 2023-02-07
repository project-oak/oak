#ifndef __PTY_H__
#define __PTY_H__

#include <_ansi.h>
#include <sys/termios.h>

#ifdef __cplusplus
extern "C" {
#endif

int openpty (int *, int *, char *, const struct termios *,
		     const struct winsize *);
int forkpty (int *, char *, const struct termios *,
		     const struct winsize *);

#ifdef __cplusplus
}
#endif

#endif /* __PTY_H__ */
