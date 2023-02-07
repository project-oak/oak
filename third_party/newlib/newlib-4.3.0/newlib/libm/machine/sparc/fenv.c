/*	$NetBSD: fenv.c,v 1.2 2017/03/22 23:11:09 chs Exp $	*/

/*-
 * Copyright (c) 2004-2005 David Schultz <das@FreeBSD.ORG>
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
 */
#include <sys/cdefs.h>
__RCSID("$NetBSD: fenv.c,v 1.2 2017/03/22 23:11:09 chs Exp $");



#include <assert.h>
#include <fenv.h>

#define _DIAGASSERT(x) assert(x)

#ifdef __weak_alias
__weak_alias(feclearexcept,_feclearexcept)
__weak_alias(fedisableexcept,_fedisableexcept)
__weak_alias(feenableexcept,_feenableexcept)
__weak_alias(fegetenv,_fegetenv)
__weak_alias(fegetexcept,_fegetexcept)
__weak_alias(fegetexceptflag,_fegetexceptflag)
__weak_alias(fegetround,_fegetround)
__weak_alias(feholdexcept,_feholdexcept)
__weak_alias(feraiseexcept,_feraiseexcept)
__weak_alias(fesetenv,_fesetenv)
__weak_alias(fesetexceptflag,_fesetexceptflag)
__weak_alias(fesetround,_fesetround)
__weak_alias(fetestexcept,_fetestexcept)
__weak_alias(feupdateenv,_feupdateenv)
#endif

/* Load floating-point state register (32bits) */
#define	__ldfsr(__r)	__asm__	__volatile__		\
	("ld %0, %%fsr" : : "m" (__r))

/* Save floating-point state register (32bits) */
#define	__stfsr(__r)	__asm__	__volatile__		\
	("st %%fsr, %0" : "=m" (*(__r)))

/*
 * The feclearexcept() function clears the supported floating-point exceptions
 * represented by `excepts'.
 */
int
feclearexcept(int excepts)
{
	fexcept_t r;
	int ex;

	_DIAGASSERT((excepts & ~FE_ALL_EXCEPT) == 0);

	ex = excepts & FE_ALL_EXCEPT;

	__stfsr(&r);
	r &= ~ex;
	__ldfsr(r);

	/* Success */
	return 0;
}

/*
 * The fegetexceptflag() function stores an implementation-defined
 * representation of the states of the floating-point status flags indicated
 * by the argument excepts in the object pointed to by the argument flagp.
 */
int
fegetexceptflag(fexcept_t *flagp, int excepts)
{
	fexcept_t r;
	int ex;

	_DIAGASSERT(flagp != NULL);
	_DIAGASSERT((excepts & ~FE_ALL_EXCEPT) == 0);

	ex = excepts & FE_ALL_EXCEPT;

	__stfsr(&r);
	*flagp = r & ex;

	/* Success */
	return 0;
}


/*
 * This function sets the floating-point status flags indicated by the argument
 * `excepts' to the states stored in the object pointed to by `flagp'. It does
 * NOT raise any floating-point exceptions, but only sets the state of the flags.
 */
int
fesetexceptflag(const fexcept_t *flagp, int excepts)
{
	fexcept_t r;
	int ex;

	_DIAGASSERT(flagp != NULL);
	_DIAGASSERT((excepts & ~FE_ALL_EXCEPT) == 0);

	ex = excepts & FE_ALL_EXCEPT;

	__stfsr(&r);
	r &= ~ex;
	r |= *flagp & ex;
	__ldfsr(r);

	/* Success */
	return 0;
}

/*
 * The feraiseexcept() function raises the supported floating-point exceptions
 * represented by the argument `excepts'.
 *
 * The order in which these floating-point exceptions are raised is unspecified
 * (by the standard).
 */
int
feraiseexcept(int excepts)
{
	volatile double d;
	int ex;

	_DIAGASSERT((excepts & ~FE_ALL_EXCEPT) == 0);

	ex = excepts & FE_ALL_EXCEPT;

	/*
	 * With a compiler that supports the FENV_ACCESS pragma properly, simple
	 * expressions like '0.0 / 0.0' should be sufficient to generate traps.
	 * Unfortunately, we need to bring a volatile variable into the equation
	 * to prevent incorrect optimizations.
	 */
	if (ex & FE_INVALID) {
		d = 0.0;
		d = 0.0 / d;
	}
	if (ex & FE_DIVBYZERO) {
		d = 0.0;
		d = 1.0 / d;
	}
	if (ex & FE_OVERFLOW) {
		d = 0x1.ffp1023;
		d *= 2.0;
	}
	if (ex & FE_UNDERFLOW) {
		d = 0x1p-1022;
		d /= 0x1p1023;
	}
	if (ex & FE_INEXACT) {
		d = 0x1p-1022;
		d += 1.0;
	}

	/* Success */
	return 0;
}

/*
 * The fetestexcept() function determines which of a specified subset of the
 * floating-point exception flags are currently set. The `excepts' argument
 * specifies the floating-point status flags to be queried.
 */
int
fetestexcept(int excepts)
{
	fexcept_t r;

	_DIAGASSERT((excepts & ~FE_ALL_EXCEPT) == 0);

	__stfsr(&r);

	return r & (excepts & FE_ALL_EXCEPT);
}

/*
 * The fegetround() function gets the current rounding direction.
 */
int
fegetround(void)
{
	fenv_t r;

	__stfsr(&r);

	return (r >> _ROUND_SHIFT) & _ROUND_MASK;
}

/*
 * The fesetround() function establishes the rounding direction represented by
 * its argument `round'. If the argument is not equal to the value of a rounding
 * direction macro, the rounding direction is not changed.
 */
int
fesetround(int round)
{
	fenv_t r;

	_DIAGASSERT((round & ~_ROUND_MASK) == 0);
	if (round & ~_ROUND_MASK)
		return -1;

	__stfsr(&r);
	r &= ~(_ROUND_MASK << _ROUND_SHIFT);
	r |= round << _ROUND_SHIFT;
	__ldfsr(r);

	/* Success */
	return 0;
}

/*
 * The fegetenv() function attempts to store the current floating-point
 * environment in the object pointed to by envp.
 */
int
fegetenv(fenv_t *envp)
{
	_DIAGASSERT(envp != NULL);

	__stfsr(envp);

	/* Success */
	return 0;
}


/*
 * The feholdexcept() function saves the current floating-point environment
 * in the object pointed to by envp, clears the floating-point status flags, and
 * then installs a non-stop (continue on floating-point exceptions) mode, if
 * available, for all floating-point exceptions.
 */
int
feholdexcept(fenv_t *envp)
{
	fenv_t r;

	_DIAGASSERT(envp != NULL);

	__stfsr(&r);
	*envp = r;
	r &= ~(FE_ALL_EXCEPT | _ENABLE_MASK);
	__ldfsr(r);

	/* Success */
	return 0;
}

/*
 * The fesetenv() function attempts to establish the floating-point environment
 * represented by the object pointed to by envp. The argument `envp' points
 * to an object set by a call to fegetenv() or feholdexcept(), or equal a
 * floating-point environment macro. The fesetenv() function does not raise
 * floating-point exceptions, but only installs the state of the floating-point
 * status flags represented through its argument.
 */
int
fesetenv(const fenv_t *envp)
{
	_DIAGASSERT(envp != NULL);

	__ldfsr(*envp);

	/* Success */
	return 0;
}


/*
 * The feupdateenv() function saves the currently raised floating-point
 * exceptions in its automatic storage, installs the floating-point environment
 * represented by the object pointed to by `envp', and then raises the saved
 * floating-point exceptions. The argument `envp' shall point to an object set
 * by a call to feholdexcept() or fegetenv(), or equal a floating-point
 * environment macro.
 */
int
feupdateenv(const fenv_t *envp)
{
	fexcept_t r;

	_DIAGASSERT(envp != NULL);

	__stfsr(&r);
	__ldfsr(*envp);

	_DIAGASSERT((r & ~FE_ALL_EXCEPT) == 0);
	feraiseexcept(r & FE_ALL_EXCEPT);

	/* Success */
	return 0;
}

/*
 * The following functions are extentions to the standard
 */
int
feenableexcept(int mask)
{
	fenv_t old_r, new_r;

	__stfsr(&old_r);
	new_r = old_r | ((mask & FE_ALL_EXCEPT) << _FPUSW_SHIFT);
	__ldfsr(new_r);

	return (old_r >> _FPUSW_SHIFT) & FE_ALL_EXCEPT;
}

int
fedisableexcept(int mask)
{
	fenv_t old_r, new_r;

	__stfsr(&old_r);
	new_r = old_r & ~((mask & FE_ALL_EXCEPT) << _FPUSW_SHIFT);
	__ldfsr(new_r);

	return (old_r >> _FPUSW_SHIFT) & FE_ALL_EXCEPT;
}

int
fegetexcept(void)
{
	fenv_t r;

	__stfsr(&r);
	return (r & _ENABLE_MASK) >> _FPUSW_SHIFT;
}
