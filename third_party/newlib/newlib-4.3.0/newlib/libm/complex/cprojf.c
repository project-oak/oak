/*	$NetBSD: cprojf.c,v 1.3 2010/09/20 17:51:38 christos Exp $	*/

/*-
 * Copyright (c) 2010 The NetBSD Foundation, Inc.
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
 * THIS SOFTWARE IS PROVIDED BY THE NETBSD FOUNDATION, INC. AND CONTRIBUTORS
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE FOUNDATION OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * imported and modified include for newlib 2010/10/03 
 * Marco Atzeri <marco_atzeri@yahoo.it>
 */

#include <sys/cdefs.h>
/*__RCSID("$NetBSD: cprojf.c,v 1.3 2010/09/20 17:51:38 christos Exp $"); */

#include <complex.h>
#include <math.h>

#include "../common/fdlibm.h"

/*
 * cprojf(float complex z)
 *
 * These functions return the value of the projection (not stereographic!)
 * onto the Riemann sphere.
 *
 * z projects to z, except that all complex infinities (even those with one
 * infinite part and one NaN part) project to positive infinity on the real axis.
 * If z has an infinite part, then cproj(z) shall be equivalent to:
 *
 * INFINITY + I * copysign(0.0, cimag(z))
 */

float complex
cprojf(float complex z)
{
	float_complex w = { .z = z };

	if (isinf(crealf(z)) || isinf(cimagf(z))) {
#ifdef __INFINITY
		REAL_PART(w) = __INFINITY;
#else
		REAL_PART(w) = INFINITY;
#endif
		IMAG_PART(w) = copysignf(0.0, cimagf(z));
	}

	return (w.z);
}
