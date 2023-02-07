/* $NetBSD: clog.c,v 1.1 2007/08/20 16:01:35 drochner Exp $ */

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
        <<clog>>, <<clogf>>---complex base-e logarithm

INDEX
        clog
INDEX
        clogf

SYNOPSIS
       #include <complex.h>
       double complex clog(double complex <[z]>);
       float complex clogf(float complex <[z]>);


DESCRIPTION
        These functions compute the complex natural (base-<[e]>) logarithm 
        of <[z]>, with a branch cut along the negative real axis. 

        <<clogf>> is identical to <<clog>>, except that it performs
        its calculations on <<floats complex>>.

RETURNS
        @ifnottex
        The clog functions return the complex natural logarithm value, in 
        the range of a strip mathematically unbounded along the real axis 
        and in the interval [-i*pi , +i*pi] along the imaginary axis.
        @end ifnottex
        @tex
        The clog functions return the complex natural logarithm value, in
        the range of a strip mathematically unbounded along the real axis
         and in the interval [$-i\pi$, $+i\pi$] along the imaginary axis.
        @end tex

PORTABILITY
        <<clog>> and <<clogf>> are ISO C99

QUICKREF
        <<clog>> and <<clogf>> are ISO C99

*/

#include <complex.h>
#include <math.h>

double complex
clog(double complex z)
{
	double complex w;
	double p, rr;

	rr = cabs(z);
	p = log(rr);
	rr = atan2(cimag(z), creal(z));
	w = p + rr * I;
	return w;
}
