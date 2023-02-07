/*#######################################################################
# RDOS operating system
# Copyright (C) 1988-2006, Leif Ekblad
#
# This library is free software; you can redistribute it and/or modify
# it under the terms of the GNU Lesser General Public License as published
# by the Free Software Foundation; either version 2.1 of the License, or
# (at your option) any later version.
#
# This library is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
# GNU Lesser General Public License for more details.
#
# You should have received a copy of the GNU Lesser General Public
# License along with this library; if not, write to the Free Software
# Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA 
#
# The author of this program may be contacted at leif@rdos.net
#
# open.c                                                                
# open function implementation
#
##########################################################################*/

#include "config.h"
#include <_ansi.h>
#include <_syslist.h>
#include <fcntl.h>
#include <errno.h>
#include "rdos.h"
#include <stdarg.h>

int open(const char *file, int flags, ...)
{
	int handle;
	int pos;

	if (flags & O_CREAT)
		handle = RdosCreateFile(file, flags);
	else
		handle = RdosOpenFile(file, flags);

	if (handle >= 0)
	{
		if (flags & O_APPEND)
		{
			pos = RdosGetFileSize(handle);
			RdosSetFilePos(handle, pos);
		}

		if (flags & O_TRUNC)
			RdosSetFileSize(handle, 0);
	
		return handle;
	}
	else
		return -1;
}
