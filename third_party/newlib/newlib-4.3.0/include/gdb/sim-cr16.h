/* This file defines the interface between the cr16 simulator and gdb.

   Copyright 2008-2013 Free Software Foundation, Inc.

   This file is part of GDB.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License 
   along with this program; if not, see <http://www.gnu.org/licenses/>.  */

#if !defined (SIM_CR16_H)
#define SIM_CR16_H

#ifdef __cplusplus
extern "C" { // }
#endif

enum
  {
    SIM_CR16_MEMORY_UNIFIED = 0x00000000,
    SIM_CR16_MEMORY_INSN    = 0x10000000,
    SIM_CR16_MEMORY_DATA    = 0x10000000,
    SIM_CR16_MEMORY_DMAP    = 0x10000000,
    SIM_CR16_MEMORY_IMAP    = 0x10000000
  };

extern unsigned long sim_cr16_translate_dmap_addr
  (unsigned long offset,
   int nr_bytes,
   unsigned long *phys,
   void *regcache,
   unsigned long (*dmap_register) (void *regcache, int reg_nr));

extern unsigned long sim_cr16_translate_imap_addr
  (unsigned long offset,
   int nr_bytes,
   unsigned long *phys,
   void *regcache,
   unsigned long (*imap_register) (void *regcache, int reg_nr));

extern unsigned long sim_cr16_translate_addr
  (unsigned long vaddr,
   int nr_bytes,
   unsigned long *phys,
   void *regcache,
   unsigned long (*dmap_register) (void *regcache, int reg_nr),
   unsigned long (*imap_register) (void *regcache, int reg_nr));


/* The simulator makes use of the following register information. */

enum sim_cr16_regs
{
  SIM_CR16_R0_REGNUM,
  SIM_CR16_R1_REGNUM,
  SIM_CR16_R2_REGNUM,
  SIM_CR16_R3_REGNUM,
  SIM_CR16_R4_REGNUM,
  SIM_CR16_R5_REGNUM,
  SIM_CR16_R6_REGNUM,
  SIM_CR16_R7_REGNUM,
  SIM_CR16_R8_REGNUM,
  SIM_CR16_R9_REGNUM,
  SIM_CR16_R10_REGNUM,
  SIM_CR16_R11_REGNUM,
  SIM_CR16_R12_REGNUM,
  SIM_CR16_R13_REGNUM,
  SIM_CR16_R14_REGNUM,
  SIM_CR16_R15_REGNUM,

  SIM_CR16_PC_REGNUM,
  SIM_CR16_ISP_REGNUM,
  SIM_CR16_USP_REGNUM,
  SIM_CR16_INTBASE_REGNUM,
  SIM_CR16_PSR_REGNUM,
  SIM_CR16_CFG_REGNUM,
  SIM_CR16_DBS_REGNUM,
  SIM_CR16_DCR_REGNUM,
  SIM_CR16_DSR_REGNUM,
  SIM_CR16_CAR0_REGNUM,
  SIM_CR16_CAR1_REGNUM
};
  
enum
{
  SIM_CR16_NR_R_REGS = 16,
  SIM_CR16_NR_A_REGS = 2,
  SIM_CR16_NR_IMAP_REGS = 2,
  SIM_CR16_NR_DMAP_REGS = 4,
  SIM_CR16_NR_CR_REGS = 11
};

#ifdef __cplusplus
}
#endif

#endif
