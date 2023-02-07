/* $NetBSD: ctan.c,v 1.1 2007/08/20 16:01:37 drochner Exp $ */

/*-
 * Copyright (c) 2007 The NetBSD Foundation, Inc.
 * All rights reserved.
 *
 * This code is derived from software written by Stephen L. Moshier.
 * It is redistributed by the NetBSD Foundation by permission of the author.
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

/*
FUNCTION
        <<ctan>>, <<ctanf>>---complex tangent

INDEX
        ctan
INDEX
        ctanf

SYNOPSIS
       #include <complex.h>
       double complex ctan(double complex <[z]>);
       float complex ctanf(float complex <[z]>);


DESCRIPTION
        These functions compute the complex tangent of <[z]>.

        <<ctanf>> is identical to <<ctan>>, except that it performs
        its calculations on <<floats complex>>.

RETURNS
        These functions return the complex tangent value.

PORTABILITY
        <<ctan>> and <<ctanf>> are ISO C99

QUICKREF
        <<ctan>> and <<ctanf>> are ISO C99

*/


#include <complex.h>
#include <math.h>
#include "cephes_subr.h"

double complex
ctan(double complex z)
{
	double complex w;
	double d;

	d = cos(2.0 * creal(z)) + cosh(2.0 * cimag(z));

	if (fabs(d) < 0.25)
		d = _ctans(z);

	if (d == 0.0) {
		/* mtherr ("ctan", OVERFLOW); */
		w = HUGE_VAL + HUGE_VAL * I;
		return w;
	}

	w = sin(2.0 * creal(z)) / d + (sinh(2.0 * cimag(z)) / d) * I;
	return w;
}
