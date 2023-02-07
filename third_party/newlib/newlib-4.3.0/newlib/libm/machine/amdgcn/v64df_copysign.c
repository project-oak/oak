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
 * ====================================================
 * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
 *
 * Developed at SunPro, a Sun Microsystems, Inc. business.
 * Permission to use, copy, modify, and distribute this
 * software is freely granted, provided that this notice 
 * is preserved.
 * ====================================================
 */

/* Based on newlib/libm/common/s_copysign.c in Newlib.  */

#include "amdgcnmach.h"

DEF_VD_MATH_FUNC (v64df, copysign, v64df x, v64df y)
{
  FUNCTION_INIT (v64df);

  v64si hx, hy;
  GET_HIGH_WORD(hx, x, NO_COND);
  GET_HIGH_WORD(hy, y, NO_COND);
  SET_HIGH_WORD(x, (hx & 0x7fffffff) | (hy & 0x80000000), NO_COND);
  VECTOR_RETURN (x, NO_COND);

  FUNCTION_RETURN;
}

DEF_VARIANTS2 (copysign, df, df)
