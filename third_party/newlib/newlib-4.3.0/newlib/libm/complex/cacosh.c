/* $NetBSD: cacosh.c,v 1.2 2009/08/03 19:41:32 drochner Exp $ */

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
        <<cacosh>>, <<cacoshf>>---complex arc hyperbolic cosine

INDEX
        cacosh
INDEX
        cacoshf

SYNOPSIS
       #include <complex.h>
       double complex cacosh(double complex <[z]>);
       float complex cacoshf(float complex <[z]>);


DESCRIPTION
        These functions compute the complex arc hyperbolic cosine of <[z]>,
        with a branch cut at values less than 1 along the real axis.

        <<cacoshf>> is identical to <<cacosh>>, except that it performs
        its calculations on <<floats complex>>.

RETURNS
        @ifnottex
        These functions return the complex arc hyperbolic cosine value, 
        in the range of a half-strip of non-negative values along the 
        real axis and in the interval [-i * pi, +i * pi] along the 
        imaginary axis.
        @end ifnottex
        @tex
        These functions return the complex arc hyperbolic cosine value, 
        in the range of a half-strip of non-negative values along the 
        real axis and in the interval [$-i\pi$, $+i\pi$] along the 
        imaginary axis.
        @end tex

PORTABILITY
        <<cacosh>> and <<cacoshf>> are ISO C99

QUICKREF
        <<cacosh>> and <<cacoshf>> are ISO C99

*/


#include <complex.h>

double complex
cacosh(double complex z)
{
	double complex w;

#if 0 /* does not give the principal value */
	w = I * cacos(z);
#else
	w = clog(z + csqrt(z + 1) * csqrt(z - 1));
#endif
	return w;
}
