/*
 * Copyright 2023 Siemens
 *
 * The authors hereby grant permission to use, copy, modify, distribute,
 * and license this software and its documentation for any purpose, provided
 * that existing copyright notices are retained in all copies and that this
 * notice is included verbatim in any distributions.  No written agreement,
 * license, or royalty fee is required for any of the authorized uses.
 * Modifications to this software may be copyrighted by their authors
 * and need not follow the licensing terms described here, provided that
 * the new terms are clearly indicated on the first page of each file where
 * they apply.
 */

/*
 * Copyright (c) 1994-2009  Red Hat, Inc. All rights reserved.
 *
 * This copyrighted material is made available to anyone wishing to use,
 * modify, copy, or redistribute it subject to the terms and conditions
 * of the BSD License.   This program is distributed in the hope that
 * it will be useful, but WITHOUT ANY WARRANTY expressed or implied,
 * including the implied warranties of MERCHANTABILITY or FITNESS FOR
 * A PARTICULAR PURPOSE.  A copy of this license is available at
 * http://www.opensource.org/licenses. Any Red Hat trademarks that are
 * incorporated in the source code or documentation are not subject to
 * the BSD License and may only be used or replicated with the express
 * permission of Red Hat, Inc.
 */

/******************************************************************
 * The following routines are coded directly from the algorithms
 * and coefficients given in "Software Manual for the Elementary
 * Functions" by William J. Cody, Jr. and William Waite, Prentice
 * Hall, 1980.
 ******************************************************************/

/* Based on newlib/libm/mathfp/s_sine.c in Newlib.  */

#include "amdgcnmach.h"

v64si v64df_numtest (v64df x);

static const double HALF_PI = 1.57079632679489661923;
static const double ONE_OVER_PI = 0.31830988618379067154;
static const double r[] = { -0.16666666666666665052,
                             0.83333333333331650314e-02,
                            -0.19841269841201840457e-03,
                             0.27557319210152756119e-05,
                            -0.25052106798274584544e-07,
                             0.16058936490371589114e-09,
                            -0.76429178068910467734e-12,
                             0.27204790957888846175e-14 };

#if defined (__has_builtin) && __has_builtin (__builtin_gcn_fabsv)

DEF_VD_MATH_FUNC(v64df, sine, v64df x, int cosine)
{
  const double YMAX = 210828714.0;

  FUNCTION_INIT (v64df);

  v64si num_type = v64df_numtest (x);
  VECTOR_IF (num_type == NAN, cond)
    errno = EDOM;
    VECTOR_RETURN (x, cond);
  VECTOR_ELSEIF (num_type == INF, cond)
    errno = EDOM;
    VECTOR_RETURN (VECTOR_INIT (z_notanum.d), cond);
  VECTOR_ENDIF

  /* Use sin and cos properties to ease computations. */
  v64di sgn;
  v64df y;

  if (cosine)
    {
      sgn = VECTOR_INIT (0L);
      y = __builtin_gcn_fabsv (x) + HALF_PI;
    }
  else
    {
      sgn = x < 0.0;
      y = VECTOR_MERGE (-x, x, x < 0.0);
    }

  /* Check for values of y that will overflow here. */
  VECTOR_IF (y > YMAX, cond)
    errno = ERANGE;
    VECTOR_RETURN (x, cond);
  VECTOR_ENDIF

  /* Calculate the exponent. */
  v64si Nneg = __builtin_convertvector (y * ONE_OVER_PI - 0.5, v64si);
  v64si Npos = __builtin_convertvector (y * ONE_OVER_PI + 0.5, v64si);
  v64si N = VECTOR_MERGE (Nneg, Npos, y < 0.0);
  v64df XN = __builtin_convertvector (N, v64df);

  VECTOR_COND_MOVE (sgn, ~sgn, (N & 1) != 0);

  if (cosine)
    XN -= 0.5;

  y = __builtin_gcn_fabsv (x) - XN * __PI;

  v64df res;

  VECTOR_IF ((-z_rooteps < y) & (y < z_rooteps), cond)
    VECTOR_COND_MOVE (res, y, cond);
  VECTOR_ELSE (cond)
    v64df g = y * y;

    /* Calculate the Taylor series. */
    v64df R = (((((((r[6] * g + r[5]) * g + r[4]) * g + r[3]) * g + r[2]) * g + r[1]) * g + r[0]) * g);

    /* Finally, compute the result. */
    VECTOR_COND_MOVE (res, y + y * R, cond);
  VECTOR_ENDIF
 
  VECTOR_COND_MOVE (res, -res, sgn);

  VECTOR_RETURN (res, NO_COND);

  FUNCTION_RETURN;
}

#endif
