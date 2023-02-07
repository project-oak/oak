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

/* Based in newlib/libm/mathfp/sf_sineh.c in Newlib.  */

#include "amdgcnmach.h"

v64sf v64sf_expf_aux (v64sf, v64si);
v64si v64sf_numtestf (v64sf);
v64si v64sf_isposf (v64sf);

static const float q[] = { -0.428277109e+2 };
static const float p[] = { -0.713793159e+1,
			-0.190333399 };
static const float LNV = 0.6931610107;
static const float INV_V2 = 0.2499930850;
static const float V_OVER2_MINUS1 = 0.1383027787e-4;

#if defined (__has_builtin) && __has_builtin (__builtin_gcn_fabsvf)

DEF_VS_MATH_FUNC (v64sf, sinehf, v64sf x, int cosineh)
{
  const float WBAR = 18.55;
  
  FUNCTION_INIT (v64sf);

  v64si sgn = VECTOR_INIT (0);
  v64si v_cosineh = VECTOR_INIT (cosineh ? -1 : 0);

  /* Check for special values. */
  v64si num_type = v64sf_numtestf (x);
  VECTOR_IF (num_type == NAN, cond)
    errno = EDOM;
    VECTOR_RETURN (x, cond);
  VECTOR_ELSEIF (num_type == INF, cond)
    errno = ERANGE;
    VECTOR_RETURN (VECTOR_MERGE (VECTOR_INIT (z_infinity_f.f),
				 VECTOR_INIT (-z_infinity_f.f),
				 v64sf_isposf (x)),
		   cond);
  VECTOR_ENDIF

  v64sf y = __builtin_gcn_fabsvf (x);

  if (!cosineh)
    VECTOR_COND_MOVE (sgn, VECTOR_INIT (-1), x < 0.0f);

  v64sf res;

  VECTOR_IF (((y > 1.0f) & ~v_cosineh) | v_cosineh, cond)
    VECTOR_IF2 (y > (float) BIGX, cond2, cond)
      v64sf w = y - LNV;

      /* Check for w > maximum here. */
      VECTOR_IF2 (w > (float) BIGX, cond3, cond2)
	errno = ERANGE;
	VECTOR_RETURN (x, cond3);
      VECTOR_ENDIF

      v64sf z = v64sf_expf_aux (w, __mask);

      VECTOR_COND_MOVE (res, z * (V_OVER2_MINUS1 + 1.0f),
			cond2 & (w > WBAR));
    VECTOR_ELSE2 (cond2, cond)
      v64sf z = v64sf_expf_aux (y, __mask);
      if (cosineh) {
	VECTOR_COND_MOVE (res, (z + 1 / z) * 0.5f, cond2);
      } else {
	VECTOR_COND_MOVE (res, (z - 1 / z) * 0.5f, cond2);
      }
    VECTOR_ENDIF

    VECTOR_COND_MOVE (res, -res, sgn);
  VECTOR_ELSE (cond)
    /* Check for y being too small. */
    VECTOR_IF2 (y < z_rooteps_f, cond2, cond);
      VECTOR_COND_MOVE (res, x, cond2);
    VECTOR_ELSE2 (cond2, cond)
      /* Calculate the Taylor series. */
      v64sf f = x * x;
      v64sf Q = f + q[0];
      v64sf P = p[1] * f + p[0];
      v64sf R = f * (P / Q);

      VECTOR_COND_MOVE (res, x + x * R, cond2);
    VECTOR_ENDIF
  VECTOR_ENDIF

  VECTOR_RETURN (res, NO_COND);

  FUNCTION_RETURN;
}

#endif
