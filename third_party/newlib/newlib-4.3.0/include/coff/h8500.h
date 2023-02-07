/* coff information for Renesas H8/500
   
   Copyright 2001, 2003, 2010 Free Software Foundation, Inc.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3 of the License, or
   (at your option) any later version.
   
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
   
   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street - Fifth Floor, Boston,
   MA 02110-1301, USA.  */

#define L_LNNO_SIZE 4
#include "coff/external.h"

#define	H8500MAGIC	0x8500

#define H8500BADMAG(x) ((0xffff && ((x).f_magic) != H8500MAGIC))

/********************** RELOCATION DIRECTIVES **********************/

/* The external reloc has an offset field, because some of the reloc
   types on the h8 don't have room in the instruction for the entire
   offset - eg the strange jump and high page addressing modes.  */

struct external_reloc
{
  char r_vaddr[4];
  char r_symndx[4];
  char r_offset[4];
  char r_type[2];
  char r_stuff[2];
};

#define RELOC struct external_reloc
#define RELSZ 16




