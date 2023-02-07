/*
 * Copyright (c) 2010 David Xu <davidxu@freebsd.org>
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice unmodified, this list of conditions, and the following
 *    disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * $FreeBSD$
 */

/* semaphore.h: POSIX 1003.1b semaphores */

#ifndef _SEMAPHORE_H_
#define _SEMAPHORE_H_

#include <sys/cdefs.h>
#include <sys/lock.h>
#include <sys/_types.h>
#include <sys/_timespec.h>

typedef struct {
	unsigned long _flags;
	struct _Semaphore_Control _Semaphore;
} sem_t;

#define	SEM_FAILED	((sem_t *)0)

__BEGIN_DECLS
int	 sem_close(sem_t *);
int	 sem_destroy(sem_t *);
int	 sem_getvalue(sem_t * __restrict, int * __restrict);
int	 sem_init(sem_t *, int, unsigned int);
sem_t	*sem_open(const char *, int, ...);
int	 sem_post(sem_t *);
int	 sem_timedwait(sem_t * __restrict, const struct timespec * __restrict);
int	 sem_trywait(sem_t *);
int	 sem_unlink(const char *);
int	 sem_wait(sem_t *);
__END_DECLS

#endif /* !_SEMAPHORE_H_ */
