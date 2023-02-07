/* $NetBSD: hcreate.c,v 1.2 2001/02/19 21:26:04 ross Exp $ */

/*
 * Copyright (c) 2001 Christopher G. Demetriou
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
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission.
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
 * <<Id: LICENSE_GC,v 1.1 2001/10/01 23:24:05 cgd Exp>>
 */

/*
 * hcreate() / hsearch() / hdestroy()
 *
 * SysV/XPG4 hash table functions.
 *
 * Implementation done based on NetBSD manual page and Solaris manual page,
 * plus my own personal experience about how they're supposed to work.
 *
 * I tried to look at Knuth (as cited by the Solaris manual page), but
 * nobody had a copy in the office, so...
 */

#include <sys/cdefs.h>
#if 0
#if defined(LIBC_SCCS) && !defined(lint)
__RCSID("$NetBSD: hcreate.c,v 1.2 2001/02/19 21:26:04 ross Exp $");
#endif /* LIBC_SCCS and not lint */
#endif

#include <sys/types.h>
#include <sys/queue.h>
#include <errno.h>
#include <search.h>
#include <stdlib.h>
#include <string.h>

/*
 * DO NOT MAKE THIS STRUCTURE LARGER THAN 32 BYTES (4 ptrs on 64-bit
 * ptr machine) without adjusting MAX_BUCKETS_LG2 below.
 */
struct internal_entry {
	SLIST_ENTRY(internal_entry) link;
	ENTRY ent;
};
SLIST_HEAD(internal_head, internal_entry);

#define	MIN_BUCKETS_LG2	4
#define	MIN_BUCKETS	(1 << MIN_BUCKETS_LG2)

/*
 * max * sizeof internal_entry must fit into size_t.
 * assumes internal_entry is <= 32 (2^5) bytes.
 */
#ifdef __MSP430X_LARGE__
/* 20-bit size_t.  */
#define	MAX_BUCKETS_LG2	(20 - 1 - 5)
#else
#define	MAX_BUCKETS_LG2	(sizeof (size_t) * 8 - 1 - 5)
#endif
#define	MAX_BUCKETS	((size_t)1 << MAX_BUCKETS_LG2)

/* Default hash function, from db/hash/hash_func.c */
extern __uint32_t (*__default_hash)(const void *, size_t);

int
hcreate_r(size_t nel, struct hsearch_data *htab)
{
	size_t idx;
	unsigned int p2;

	/* Make sure this this isn't called when a table already exists. */
	if (htab->htable != NULL) {
		errno = EINVAL;
		return 0;
	}

	/* If nel is too small, make it min sized. */
	if (nel < MIN_BUCKETS)
		nel = MIN_BUCKETS;

	/* If it's too large, cap it. */
	if (nel > MAX_BUCKETS)
		nel = MAX_BUCKETS;

	/* If it's is not a power of two in size, round up. */
	if ((nel & (nel - 1)) != 0) {
		for (p2 = 0; nel != 0; p2++)
			nel >>= 1;
		nel = 1 << p2;
	}
	
	/* Allocate the table. */
	htab->htablesize = nel;
	htab->htable = malloc(htab->htablesize * sizeof htab->htable[0]);
	if (htab->htable == NULL) {
		errno = ENOMEM;
		return 0;
	}

	/* Initialize it. */
	for (idx = 0; idx < htab->htablesize; idx++)
		SLIST_INIT(&(htab->htable[idx]));

	return 1;
}

void
hdestroy_r(struct hsearch_data *htab)
{
#if 0
	struct internal_entry *ie;
	size_t idx;
#endif
	if (htab->htable == NULL)
		return;

#if 0
	for (idx = 0; idx < htab->htablesize; idx++) {
		while (!SLIST_EMPTY(&(htab->htable[idx]))) {
			ie = SLIST_FIRST(&(htab->htable[idx]));
			SLIST_REMOVE_HEAD(&(htab->htable[idx]), link);
                        free(ie->ent.key);
			free(ie);
		}
	}
#endif
	free(htab->htable);
	htab->htable = NULL;
}

int
hsearch_r(ENTRY item, ACTION action, ENTRY **retval, struct hsearch_data *htab)
{
	struct internal_head *head;
	struct internal_entry *ie;
	__uint32_t hashval;
	size_t len;

	len = strlen(item.key);
	hashval = (*__default_hash)(item.key, len);

        head = &(htab->htable[hashval & (htab->htablesize - 1)]);
	ie = SLIST_FIRST(head);
	while (ie != NULL) {
		if (strcmp(ie->ent.key, item.key) == 0)
			break;
		ie = SLIST_NEXT(ie, link);
	}

	if (ie != NULL)
          {
            *retval = &ie->ent;
            return 1;
          }
	else if (action == FIND)
          {
            *retval = NULL;
            return 0;
          }

	ie = malloc(sizeof *ie);
	if (ie == NULL)
          {
            *retval = NULL;
            return 0;
          }
	ie->ent.key = item.key;
	ie->ent.data = item.data;

	SLIST_INSERT_HEAD(head, ie, link);
        *retval = &ie->ent;
	return 1;
}
