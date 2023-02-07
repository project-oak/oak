/* $NetBSD: csinh.c,v 1.1 2007/08/20 16:01:36 drochner Exp $ */

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
        <<csinh>>, <<csinhf>>---complex hyperbolic sine

INDEX
        csinh
INDEX
        csinhf

SYNOPSIS
       #include <complex.h>
       double complex csinh(double complex <[z]>);
       float complex csinhf(float complex <[z]>);


DESCRIPTION
        These functions compute the complex hyperbolic sine of <[z]>.

        <<ccoshf>> is identical to <<ccosh>>, except that it performs
        its calculations on <<floats complex>>.

RETURNS
        These functions return the complex hyperbolic sine value.

PORTABILITY
        <<csinh>> and <<csinhf>> are ISO C99

QUICKREF
        <<csinh>> and <<csinhf>> are ISO C99

*/

#include <complex.h>
#include <math.h>

double complex
csinh(double complex z)
{
	double complex w;
	double x, y;

	x = creal(z);
	y = cimag(z);
	w = sinh(x) * cos(y) + (cosh(x) * sin(y)) * I;
	return w;
}
