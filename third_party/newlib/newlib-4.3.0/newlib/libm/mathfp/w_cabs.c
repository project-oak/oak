/*
 * cabs() wrapper for hypot().
 * 
 * Written by J.T. Conklin, <jtc@wimsey.com>
 * Placed into the Public Domain, 1994.
 */

#include "fdlibm.h"

struct complex {
	double x;
	double y;
};

double
cabs(z)
	struct complex z;
{
	return hypot(z.x, z.y);
}
