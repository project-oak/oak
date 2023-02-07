/*-
 * Copyright (c) 2011 David Chisnall
 * Copyright (c) 2015 embedded brains GmbH
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
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * $FreeBSD$
 */

#include <stdlib.h>
#include <unistd.h>
#include <sys/lock.h>

/**
 * Linked list of quick exit handlers.  This is simpler than the atexit()
 * version, because it is not required to support C++ destructors or
 * DSO-specific cleanups.
 */
struct quick_exit_handler {
	struct quick_exit_handler *next;
	void (*cleanup)(void);
};

/**
 * Lock protecting the handlers list.
 */
#ifndef __SINGLE_THREAD__
__LOCK_INIT(static, __at_quick_exit_mutex);
#endif
/**
 * Stack of cleanup handlers.  These will be invoked in reverse order when
 */
static struct quick_exit_handler *handlers;

int
at_quick_exit(void (*func)(void))
{
	struct quick_exit_handler *h;

	h = malloc(sizeof(*h));

	if (NULL == h)
		return (1);
	h->cleanup = func;
#ifndef __SINGLE_THREAD__
	__lock_acquire(__at_quick_exit_mutex);
#endif
	h->next = handlers;
	handlers = h;
#ifndef __SINGLE_THREAD__
	__lock_release(__at_quick_exit_mutex);
#endif
	return (0);
}

void
quick_exit(int status)
{
	struct quick_exit_handler *h;

	/*
	 * XXX: The C++ spec requires us to call std::terminate if there is an
	 * exception here.
	 */
	for (h = handlers; NULL != h; h = h->next)
		h->cleanup();
	_exit(status);
}
