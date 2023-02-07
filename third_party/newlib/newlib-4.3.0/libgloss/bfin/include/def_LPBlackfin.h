/*
 * The authors hereby grant permission to use, copy, modify, distribute,
 * and license this software and its documentation for any purpose, provided
 * that existing copyright notices are retained in all copies and that this
 * notice is included verbatim in any distributions. No written agreement,
 * license, or royalty fee is required for any of the authorized uses.
 * Modifications to this software may be copyrighted by their authors
 * and need not follow the licensing terms described here, provided that
 * the new terms are clearly indicated on the first page of each file where
 * they apply.
 */

/************************************************************************
 *
 * def_LPBlackfin.h
 *
 * (c) Copyright 2001-2009 Analog Devices, Inc.  All rights reserved.
 *
 ************************************************************************/

/* LP Blackfin CORE REGISTER BIT & ADDRESS DEFINITIONS FOR ADSP-BF532 */

#ifndef _DEF_LPBLACKFIN_H
#define _DEF_LPBLACKFIN_H

#ifdef _MISRA_RULES
#pragma diag(push)
#pragma diag(suppress:misra_rule_19_4)
#pragma diag(suppress:misra_rule_19_7)
#endif /* _MISRA_RULES */


#if !defined(__ADSPLPBLACKFIN__)
#warning def_LPBlackfin.h should only be included for 532 compatible chips.
#endif
/* ensure macro params bracketed to avoid unexpected evaluations. (GA), MISRA Rule 19.10 */
#ifdef _MISRA_RULES
#define MK_BMSK_( x ) (1ul<<(x))    /* Make a bit mask from a bit position */
#else
#define MK_BMSK_( x ) (1<<(x))    /* Make a bit mask from a bit position */
#endif /* _MISRA_RULES */

/*********************************************************************************** */
/* System Register Bits */
/*********************************************************************************** */

/*************************************************** */
/*   ASTAT register */
/*************************************************** */

/* definitions of ASTAT bit positions */
#define ASTAT_AZ_P         0x00000000                  /* Result of last ALU0 or shifter operation is zero */
#define ASTAT_AN_P         0x00000001                  /* Result of last ALU0 or shifter operation is negative */
#define ASTAT_CC_P         0x00000005                  /* Condition Code, used for holding comparison results */
#define ASTAT_AQ_P         0x00000006                  /* Quotient Bit */
#define ASTAT_RND_MOD_P    0x00000008                  /* Rounding mode, set for biased, clear for unbiased */
#define ASTAT_AC0_P        0x0000000C                  /* Result of last ALU0 operation generated a carry */
#define ASTAT_AC0_COPY_P   0x00000002                  /* Result of last ALU0 operation generated a carry */
#define ASTAT_AC1_P        0x0000000D                  /* Result of last ALU1 operation generated a carry */
#define ASTAT_AV0_P        0x00000010                  /* Result of last ALU0 or MAC0 operation overflowed, sticky for MAC */
#define ASTAT_AV0S_P       0x00000011                  /* Sticky version of ASTAT_AV0  */
#define ASTAT_AV1_P        0x00000012                  /* Result of last MAC1 operation overflowed, sticky for MAC */
#define ASTAT_AV1S_P       0x00000013                  /* Sticky version of ASTAT_AV1  */
#define ASTAT_V_P          0x00000018		       /* Result of last ALU0 or MAC0 operation overflowed */
#define ASTAT_V_COPY_P     0x00000003                  /* Result of last ALU0 or MAC0 operation overflowed */
#define ASTAT_VS_P         0x00000019		       /* Sticky version of ASTAT_V */

/* ** Masks */
#define ASTAT_AZ           MK_BMSK_(ASTAT_AZ_P)        /* Result of last ALU0 or shifter operation is zero */
#define ASTAT_AN           MK_BMSK_(ASTAT_AN_P)        /* Result of last ALU0 or shifter operation is negative */
#define ASTAT_AC0          MK_BMSK_(ASTAT_AC0_P)       /* Result of last ALU0 operation generated a carry */
#define ASTAT_AC0_COPY     MK_BMSK_(ASTAT_AC0_COPY_P)  /* Result of last ALU0 operation generated a carry */
#define ASTAT_AC1          MK_BMSK_(ASTAT_AC1_P)       /* Result of last ALU0 operation generated a carry */
#define ASTAT_AV0          MK_BMSK_(ASTAT_AV0_P)       /* Result of last ALU0 or MAC0 operation overflowed, sticky for MAC */
#define ASTAT_AV1          MK_BMSK_(ASTAT_AV1_P)       /* Result of last MAC1 operation overflowed, sticky for MAC */
#define ASTAT_CC           MK_BMSK_(ASTAT_CC_P)        /* Condition Code, used for holding comparison results */
#define ASTAT_AQ           MK_BMSK_(ASTAT_AQ_P)        /* Quotient Bit */
#define ASTAT_RND_MOD      MK_BMSK_(ASTAT_RND_MOD_P)   /* Rounding mode, set for biased, clear for unbiased */
#define ASTAT_V            MK_BMSK_(ASTAT_V_P)         /* Overflow Bit */
#define ASTAT_V_COPY       MK_BMSK_(ASTAT_V_COPY_P)    /* Overflow Bit */

/*************************************************** */
/*   SEQSTAT register */
/*************************************************** */

/* ** Bit Positions */
#define SEQSTAT_EXCAUSE0_P      0x00000000     /* Last exception cause bit 0 */
#define SEQSTAT_EXCAUSE1_P      0x00000001  /* Last exception cause bit 1 */
#define SEQSTAT_EXCAUSE2_P      0x00000002  /* Last exception cause bit 2 */
#define SEQSTAT_EXCAUSE3_P      0x00000003  /* Last exception cause bit 3 */
#define SEQSTAT_EXCAUSE4_P      0x00000004  /* Last exception cause bit 4 */
#define SEQSTAT_EXCAUSE5_P      0x00000005  /* Last exception cause bit 5 */
#define SEQSTAT_IDLE_REQ_P      0x0000000C  /* Pending idle mode request, set by IDLE instruction */
#define SEQSTAT_SFTRESET_P      0x0000000D  /* Indicates whether the last reset was a software reset (=1) */
#define SEQSTAT_HWERRCAUSE0_P   0x0000000E  /* Last hw error cause bit 0 */
#define SEQSTAT_HWERRCAUSE1_P   0x0000000F  /* Last hw error cause bit 1 */
#define SEQSTAT_HWERRCAUSE2_P   0x00000010  /* Last hw error cause bit 2 */
#define SEQSTAT_HWERRCAUSE3_P   0x00000011  /* Last hw error cause bit 3 */
#define SEQSTAT_HWERRCAUSE4_P   0x00000012  /* Last hw error cause bit 4 */
#define SEQSTAT_HWERRCAUSE5_P   0x00000013  /* Last hw error cause bit 5 */
#define SEQSTAT_HWERRCAUSE6_P   0x00000014  /* Last hw error cause bit 6 */
#define SEQSTAT_HWERRCAUSE7_P   0x00000015  /* Last hw error cause bit 7 */
/* ** Masks */
/* Exception cause */
#define SEQSTAT_EXCAUSE        ( MK_BMSK_(SEQSTAT_EXCAUSE0_P ) | \
                                 MK_BMSK_(SEQSTAT_EXCAUSE1_P ) | \
                                 MK_BMSK_(SEQSTAT_EXCAUSE2_P ) | \
                                 MK_BMSK_(SEQSTAT_EXCAUSE3_P ) | \
                                 MK_BMSK_(SEQSTAT_EXCAUSE4_P ) | \
                                 MK_BMSK_(SEQSTAT_EXCAUSE5_P ) )

/* Indicates whether the last reset was a software reset (=1) */
#define SEQSTAT_SFTRESET       MK_BMSK_(SEQSTAT_SFTRESET_P )

/* Last hw error cause */
#define SEQSTAT_HWERRCAUSE     ( MK_BMSK_(SEQSTAT_HWERRCAUSE0_P ) | \
                                 MK_BMSK_(SEQSTAT_HWERRCAUSE1_P ) | \
                                 MK_BMSK_(SEQSTAT_HWERRCAUSE2_P ) | \
                                 MK_BMSK_(SEQSTAT_HWERRCAUSE3_P ) | \
                                 MK_BMSK_(SEQSTAT_HWERRCAUSE4_P ) )

/*************************************************** */
/*   SYSCFG register */
/*************************************************** */

/* ** Bit Positions */
#define SYSCFG_SSSTEP_P         0x00000000              /* Supervisor single step, when set it forces an exception for each instruction executed */
#define SYSCFG_CCEN_P           0x00000001              /* Enable cycle counter (=1) */
#define SYSCFG_SNEN_P           0x00000002              /* Self nesting Interrupt Enable */

/* ** Masks */
#define SYSCFG_SSSTEP         MK_BMSK_(SYSCFG_SSSTEP_P )   /* Supervisor single step, when set it forces an exception for each instruction executed */
#define SYSCFG_CCEN           MK_BMSK_(SYSCFG_CCEN_P )     /* Enable cycle counter (=1) */
#define SYSCFG_SNEN	       MK_BMSK_(SYSCFG_SNEN_P)      /* Self Nesting Interrupt Enable */
/* Backward-compatibility for typos in prior releases */
#define SYSCFG_SSSSTEP         SYSCFG_SSSTEP
#define SYSCFG_CCCEN           SYSCFG_CCEN

/*********************************************************************************** */
/* Core MMR Register Map */
/*********************************************************************************** */

/* Data Cache & SRAM Memory  (0xFFE00000 - 0xFFE00404) */


#define SRAM_BASE_ADDRESS	   0xFFE00000  /* SRAM Base Address Register */
#define DMEM_CONTROL           0xFFE00004  /* Data memory control */
#define DCPLB_STATUS		   0xFFE00008  /* Data Cache Programmable Look-Aside Buffer Status */
#define DCPLB_FAULT_STATUS     0xFFE00008  /* "" (older define) */
#define DCPLB_FAULT_ADDR       0xFFE0000C  /* Data Cache Programmable Look-Aside Buffer Fault Address */
#define DCPLB_ADDR0            0xFFE00100  /* Data Cache Protection Lookaside Buffer 0 */
#define DCPLB_ADDR1            0xFFE00104  /* Data Cache Protection Lookaside Buffer 1 */
#define DCPLB_ADDR2            0xFFE00108  /* Data Cache Protection Lookaside Buffer 2 */
#define DCPLB_ADDR3            0xFFE0010C  /* Data Cacheability Protection Lookaside Buffer 3 */
#define DCPLB_ADDR4            0xFFE00110  /* Data Cacheability Protection Lookaside Buffer 4 */
#define DCPLB_ADDR5            0xFFE00114  /* Data Cacheability Protection Lookaside Buffer 5 */
#define DCPLB_ADDR6            0xFFE00118  /* Data Cacheability Protection Lookaside Buffer 6 */
#define DCPLB_ADDR7            0xFFE0011C  /* Data Cacheability Protection Lookaside Buffer 7 */
#define DCPLB_ADDR8            0xFFE00120  /* Data Cacheability Protection Lookaside Buffer 8 */
#define DCPLB_ADDR9            0xFFE00124  /* Data Cacheability Protection Lookaside Buffer 9 */
#define DCPLB_ADDR10           0xFFE00128  /* Data Cacheability Protection Lookaside Buffer 10 */
#define DCPLB_ADDR11           0xFFE0012C  /* Data Cacheability Protection Lookaside Buffer 11 */
#define DCPLB_ADDR12           0xFFE00130  /* Data Cacheability Protection Lookaside Buffer 12 */
#define DCPLB_ADDR13           0xFFE00134  /* Data Cacheability Protection Lookaside Buffer 13 */
#define DCPLB_ADDR14           0xFFE00138  /* Data Cacheability Protection Lookaside Buffer 14 */
#define DCPLB_ADDR15           0xFFE0013C  /* Data Cacheability Protection Lookaside Buffer 15 */
#define DCPLB_DATA0            0xFFE00200  /* Data Cache 0 Status */
#define DCPLB_DATA1            0xFFE00204  /* Data Cache 1 Status */
#define DCPLB_DATA2            0xFFE00208  /* Data Cache 2 Status */
#define DCPLB_DATA3            0xFFE0020C  /* Data Cache 3 Status */
#define DCPLB_DATA4            0xFFE00210  /* Data Cache 4 Status */
#define DCPLB_DATA5            0xFFE00214  /* Data Cache 5 Status */
#define DCPLB_DATA6            0xFFE00218  /* Data Cache 6 Status */
#define DCPLB_DATA7            0xFFE0021C  /* Data Cache 7 Status */
#define DCPLB_DATA8            0xFFE00220  /* Data Cache 8 Status */
#define DCPLB_DATA9            0xFFE00224  /* Data Cache 9 Status */
#define DCPLB_DATA10           0xFFE00228  /* Data Cache 10 Status */
#define DCPLB_DATA11           0xFFE0022C  /* Data Cache 11 Status */
#define DCPLB_DATA12           0xFFE00230  /* Data Cache 12 Status */
#define DCPLB_DATA13           0xFFE00234  /* Data Cache 13 Status */
#define DCPLB_DATA14           0xFFE00238  /* Data Cache 14 Status */
#define DCPLB_DATA15           0xFFE0023C  /* Data Cache 15 Status */
#define DTEST_COMMAND          0xFFE00300  /* Data Test Command Register */
#define DTEST_DATA0            0xFFE00400  /* Data Test Data Register */
#define DTEST_DATA1            0xFFE00404  /* Data Test Data Register */

/* Instruction Cache & SRAM Memory  (0xFFE01004 - 0xFFE01404) */

#define IMEM_CONTROL           0xFFE01004  /* Instruction Memory Control */
#define ICPLB_STATUS		   0xFFE01008 /* Instruction Cache miss status */
#define CODE_FAULT_STATUS      0xFFE01008  /* "" (older define) */
#define ICPLB_FAULT_ADDR	   0xFFE0100C  /* Instruction Cache miss address */
#define CODE_FAULT_ADDR        0xFFE0100C  /* "" (older define) */
#define ICPLB_ADDR0            0xFFE01100  /* Instruction Cacheability Protection Lookaside Buffer 0 */
#define ICPLB_ADDR1            0xFFE01104  /* Instruction Cacheability Protection Lookaside Buffer 1 */
#define ICPLB_ADDR2            0xFFE01108  /* Instruction Cacheability Protection Lookaside Buffer 2 */
#define ICPLB_ADDR3            0xFFE0110C  /* Instruction Cacheability Protection Lookaside Buffer 3 */
#define ICPLB_ADDR4            0xFFE01110  /* Instruction Cacheability Protection Lookaside Buffer 4 */
#define ICPLB_ADDR5            0xFFE01114  /* Instruction Cacheability Protection Lookaside Buffer 5 */
#define ICPLB_ADDR6            0xFFE01118  /* Instruction Cacheability Protection Lookaside Buffer 6 */
#define ICPLB_ADDR7            0xFFE0111C  /* Instruction Cacheability Protection Lookaside Buffer 7 */
#define ICPLB_ADDR8            0xFFE01120  /* Instruction Cacheability Protection Lookaside Buffer 8 */
#define ICPLB_ADDR9            0xFFE01124  /* Instruction Cacheability Protection Lookaside Buffer 9 */
#define ICPLB_ADDR10           0xFFE01128  /* Instruction Cacheability Protection Lookaside Buffer 10 */
#define ICPLB_ADDR11           0xFFE0112C  /* Instruction Cacheability Protection Lookaside Buffer 11 */
#define ICPLB_ADDR12           0xFFE01130  /* Instruction Cacheability Protection Lookaside Buffer 12 */
#define ICPLB_ADDR13           0xFFE01134  /* Instruction Cacheability Protection Lookaside Buffer 13 */
#define ICPLB_ADDR14           0xFFE01138  /* Instruction Cacheability Protection Lookaside Buffer 14 */
#define ICPLB_ADDR15           0xFFE0113C  /* Instruction Cacheability Protection Lookaside Buffer 15 */
#define ICPLB_DATA0            0xFFE01200  /* Instruction Cache 0 Status */
#define ICPLB_DATA1            0xFFE01204  /* Instruction Cache 1 Status */
#define ICPLB_DATA2            0xFFE01208  /* Instruction Cache 2 Status */
#define ICPLB_DATA3            0xFFE0120C  /* Instruction Cache 3 Status */
#define ICPLB_DATA4            0xFFE01210  /* Instruction Cache 4 Status */
#define ICPLB_DATA5            0xFFE01214  /* Instruction Cache 5 Status */
#define ICPLB_DATA6            0xFFE01218  /* Instruction Cache 6 Status */
#define ICPLB_DATA7            0xFFE0121C  /* Instruction Cache 7 Status */
#define ICPLB_DATA8            0xFFE01220  /* Instruction Cache 8 Status */
#define ICPLB_DATA9            0xFFE01224  /* Instruction Cache 9 Status */
#define ICPLB_DATA10           0xFFE01228  /* Instruction Cache 10 Status */
#define ICPLB_DATA11           0xFFE0122C  /* Instruction Cache 11 Status */
#define ICPLB_DATA12           0xFFE01230  /* Instruction Cache 12 Status */
#define ICPLB_DATA13           0xFFE01234  /* Instruction Cache 13 Status */
#define ICPLB_DATA14           0xFFE01238  /* Instruction Cache 14 Status */
#define ICPLB_DATA15           0xFFE0123C  /* Instruction Cache 15 Status */
#define ITEST_COMMAND          0xFFE01300  /* Instruction Test Command Register */
#define ITEST_DATA0            0xFFE01400  /* Instruction Test Data Register */
#define ITEST_DATA1            0xFFE01404  /* Instruction Test Data Register */

/* Event/Interrupt Controller Registers   (0xFFE02000 - 0xFFE02110) */

#define EVT0                   0xFFE02000  /* Event Vector 0 ESR Address */
#define EVT1                   0xFFE02004  /* Event Vector 1 ESR Address */
#define EVT2                   0xFFE02008  /* Event Vector 2 ESR Address */
#define EVT3                   0xFFE0200C  /* Event Vector 3 ESR Address */
#define EVT4                   0xFFE02010  /* Event Vector 4 ESR Address */
#define EVT5                   0xFFE02014  /* Event Vector 5 ESR Address */
#define EVT6                   0xFFE02018  /* Event Vector 6 ESR Address */
#define EVT7                   0xFFE0201C  /* Event Vector 7 ESR Address */
#define EVT8                   0xFFE02020  /* Event Vector 8 ESR Address */
#define EVT9                   0xFFE02024  /* Event Vector 9 ESR Address */
#define EVT10                  0xFFE02028  /* Event Vector 10 ESR Address */
#define EVT11                  0xFFE0202C  /* Event Vector 11 ESR Address */
#define EVT12                  0xFFE02030  /* Event Vector 12 ESR Address */
#define EVT13                  0xFFE02034  /* Event Vector 13 ESR Address */
#define EVT14                  0xFFE02038  /* Event Vector 14 ESR Address */
#define EVT15                  0xFFE0203C  /* Event Vector 15 ESR Address */
#define IMASK                  0xFFE02104  /* Interrupt Mask Register */
#define IPEND                  0xFFE02108  /* Interrupt Pending Register */
#define ILAT                   0xFFE0210C  /* Interrupt Latch Register */
#define IPRIO                  0xFFE02110  /* Core Interrupt Priority Register */

/* Core Timer Registers     (0xFFE03000 - 0xFFE0300C) */

#define TCNTL                  0xFFE03000  /* Core Timer Control Register */
#define TPERIOD                0xFFE03004  /* Core Timer Period Register */
#define TSCALE                 0xFFE03008  /* Core Timer Scale Register */
#define TCOUNT                 0xFFE0300C  /* Core Timer Count Register */

/* Debug/MP/Emulation Registers     (0xFFE05000 - 0xFFE05008) */
#define DSPID                  0xFFE05000  /* DSP Processor ID Register for MP implementations */

#define DBGSTAT                0xFFE05008  /* Debug Status Register */


/* Trace Buffer Registers     (0xFFE06000 - 0xFFE06100) */

#define TBUFCTL                0xFFE06000  /* Trace Buffer Control Register */
#define TBUFSTAT               0xFFE06004  /* Trace Buffer Status Register */
#define TBUF                   0xFFE06100  /* Trace Buffer */

/* Watchpoint Control Registers (0xFFE07000 - 0xFFE07200) */

#define WPIACTL                0xFFE07000  /* Watchpoint Instruction Address Control Register  */
#define WPIA0                  0xFFE07040  /* Watchpoint Instruction Address Register 0 */
#define WPIA1                  0xFFE07044  /* Watchpoint Instruction Address Register 1 */
#define WPIA2                  0xFFE07048  /* Watchpoint Instruction Address Register 2 */
#define WPIA3                  0xFFE0704C  /* Watchpoint Instruction Address Register 3 */
#define WPIA4                  0xFFE07050  /* Watchpoint Instruction Address Register 4 */
#define WPIA5                  0xFFE07054  /* Watchpoint Instruction Address Register 5 */
#define WPIACNT0               0xFFE07080  /* Watchpoint Instruction Address Count Register 0 */
#define WPIACNT1               0xFFE07084  /* Watchpoint Instruction Address Count Register 1 */
#define WPIACNT2               0xFFE07088  /* Watchpoint Instruction Address Count Register 2 */
#define WPIACNT3               0xFFE0708C  /* Watchpoint Instruction Address Count Register 3 */
#define WPIACNT4               0xFFE07090  /* Watchpoint Instruction Address Count Register 4 */
#define WPIACNT5               0xFFE07094  /* Watchpoint Instruction Address Count Register 5 */
#define WPDACTL                0xFFE07100  /* Watchpoint Data Address Control Register */
#define WPDA0                  0xFFE07140  /* Watchpoint Data Address Register 0  */
#define WPDA1                  0xFFE07144  /* Watchpoint Data Address Register 1 */
#define WPDACNT0               0xFFE07180  /* Watchpoint Data Address Count Value Register 0 */
#define WPDACNT1               0xFFE07184  /* Watchpoint Data Address Count Value Register 1 */
#define WPSTAT                 0xFFE07200  /* Watchpoint Status Register */

/* Performance Monitor Registers    (0xFFE08000 - 0xFFE08104) */

#define PFCTL                  0xFFE08000  /* Performance Monitor Control Register */
#define PFCNTR0                0xFFE08100  /* Performance Monitor Counter Register 0 */
#define PFCNTR1                0xFFE08104  /* Performance Monitor Counter Register 1 */


/*********************************************************************************** */
/* Core MMR Register Bits */
/*********************************************************************************** */

/*************************************************** */
/*   EVT registers (ILAT, IMASK, and IPEND). */
/*************************************************** */

/* ** Bit Positions */
#define EVT_EMU_P            0x00000000  /* Emulator interrupt bit position */
#define EVT_RST_P            0x00000001  /* Reset interrupt bit position */
#define EVT_NMI_P            0x00000002  /* Non Maskable interrupt bit position */
#define EVT_EVX_P            0x00000003  /* Exception bit position */
#define EVT_IRPTEN_P         0x00000004  /* Global interrupt enable bit position */
#define EVT_IVHW_P           0x00000005  /* Hardware Error interrupt bit position */
#define EVT_IVTMR_P          0x00000006  /* Timer interrupt bit position */
#define EVT_IVG7_P           0x00000007  /* IVG7 interrupt bit position */
#define EVT_IVG8_P           0x00000008  /* IVG8 interrupt bit position */
#define EVT_IVG9_P           0x00000009  /* IVG9 interrupt bit position */
#define EVT_IVG10_P          0x0000000a  /* IVG10 interrupt bit position */
#define EVT_IVG11_P          0x0000000b  /* IVG11 interrupt bit position */
#define EVT_IVG12_P          0x0000000c  /* IVG12 interrupt bit position */
#define EVT_IVG13_P          0x0000000d  /* IVG13 interrupt bit position */
#define EVT_IVG14_P          0x0000000e  /* IVG14 interrupt bit position */
#define EVT_IVG15_P          0x0000000f  /* IVG15 interrupt bit position */

/* ** Masks */
#define EVT_EMU              MK_BMSK_(EVT_EMU_P   ) /* Emulator interrupt mask */
#define EVT_RST              MK_BMSK_(EVT_RST_P   ) /* Reset interrupt mask */
#define EVT_NMI              MK_BMSK_(EVT_NMI_P   ) /* Non Maskable interrupt mask */
#define EVT_EVX              MK_BMSK_(EVT_EVX_P   ) /* Exception mask */
#define EVT_IRPTEN           MK_BMSK_(EVT_IRPTEN_P) /* Global interrupt enable mask */
#define EVT_IVHW             MK_BMSK_(EVT_IVHW_P  ) /* Hardware Error interrupt mask */
#define EVT_IVTMR            MK_BMSK_(EVT_IVTMR_P ) /* Timer interrupt mask */
#define EVT_IVG7             MK_BMSK_(EVT_IVG7_P  ) /* IVG7 interrupt mask */
#define EVT_IVG8             MK_BMSK_(EVT_IVG8_P  ) /* IVG8 interrupt mask */
#define EVT_IVG9             MK_BMSK_(EVT_IVG9_P  ) /* IVG9 interrupt mask */
#define EVT_IVG10            MK_BMSK_(EVT_IVG10_P ) /* IVG10 interrupt mask */
#define EVT_IVG11            MK_BMSK_(EVT_IVG11_P ) /* IVG11 interrupt mask */
#define EVT_IVG12            MK_BMSK_(EVT_IVG12_P ) /* IVG12 interrupt mask */
#define EVT_IVG13            MK_BMSK_(EVT_IVG13_P ) /* IVG13 interrupt mask */
#define EVT_IVG14            MK_BMSK_(EVT_IVG14_P ) /* IVG14 interrupt mask */
#define EVT_IVG15            MK_BMSK_(EVT_IVG15_P ) /* IVG15 interrupt mask */

/*************************************************** */
/*   DMEM_CONTROL Register */
/*************************************************** */
/* ** Bit Positions */
#define ENDM_P						 0x00			/* (doesn't really exist) Enable Data Memory L1 */
#define DMCTL_ENDM_P				 ENDM_P		/* "" (older define) */

#define ENDCPLB_P					 0x01			/* Enable DCPLBS */
#define DMCTL_ENDCPLB_P			 ENDCPLB_P  /* "" (older define) */
#if defined(__ADSPBF50x__)
#define DMC_P						 0x03			/* L1 Data Memory Configure bit   */
#else
#define DMC0_P						 0x02			/* L1 Data Memory Configure bit 0 */
#define DMC1_P						 0x03			/* L1 Data Memory Configure bit 1 */
#define DMCTL_DMC0_P				 DMC0_P		/* "" (older define) */
#define DMCTL_DMC1_P				 DMC1_P		/* "" (older define) */
#endif
#define DCBS_P						 0x04			/* L1 Data Cache Bank Select */
#define PORT_PREF0_P				 0x12			/* DAG0 Port Preference */
#define PORT_PREF1_P				 0x13			/* DAG1 Port Preference */

/* ** Masks */
#define ENDM                   0x00000001   /* (doesn't really exist) Enable Data Memory L1 */
#define ENDCPLB                0x00000002   /* Enable DCPLB */
#define ASRAM_BSRAM            0x00000000
#define ACACHE_BSRAM           0x00000008
#define ACACHE_BCACHE          0x0000000C
#define DCBS                   0x00000010   /*  L1 Data Cache Bank Select */
#define PORT_PREF0			   0x00001000   /* DAG0 Port Preference */
#define PORT_PREF1			   0x00002000   /* DAG1 Port Preference */

/* IMEM_CONTROL Register */
/* ** Bit Positions */
#define ENICPLB_P					 0x01  /* Enable ICPLB */
#define IMCTL_ENICPLB_P				 0x01  /* "" (older define) */
#define IMC_P						 0x02  /* Enable  */
#define IMCTL_IMC_P					 0x02  /* Configure L1 code memory as cache (0=SRAM) */
#define ILOC0_P						 0x03  /* Lock Way 0 */
#define ILOC1_P						 0x04  /* Lock Way 1 */
#define ILOC2_P						 0x05  /* Lock Way 2 */
#define ILOC3_P						 0x06  /* Lock Way 3 */
#define LRUPRIORST_P				 0x0D  /* Least Recently Used Replacement Priority */
/* ** Masks */
#define ENICPLB                0x00000002  /* Enable ICPLB */
#define IMC                    0x00000004  /* Configure L1 code memory as cache (0=SRAM) */
#define ILOC0				   0x00000008  /* Lock Way 0 */
#define ILOC1				   0x00000010  /* Lock Way 1 */
#define ILOC2				   0x00000020  /* Lock Way 2 */
#define ILOC3				   0x00000040  /* Lock Way 3 */
#define LRUPRIORST			   0x00002000  /* Least Recently Used Replacement Priority */

/* TCNTL Masks */
#define TMPWR                  0x00000001  /* Timer Low Power Control, 0=low power mode, 1=active state */
#define TMREN                  0x00000002  /* Timer enable, 0=disable, 1=enable */
#define TAUTORLD               0x00000004  /* Timer auto reload */
#define TINT                   0x00000008  /* Timer generated interrupt 0=no interrupt has been generated, 1=interrupt has been generated (sticky) */

/* TCNTL Bit Positions */
#define TMPWR_P                 0x00000000  /* Timer Low Power Control, 0=low power mode, 1=active state */
#define TMREN_P                 0x00000001  /* Timer enable, 0=disable, 1=enable */
#define TAUTORLD_P              0x00000002  /* Timer auto reload */
#define TINT_P                  0x00000003  /* Timer generated interrupt 0=no interrupt has been generated, 1=interrupt has been generated (sticky) */

/* DCPLB_DATA and ICPLB_DATA Registers - bit positions */
#define CPLB_VALID_P            0  /* 0=invalid entry, 1=valid entry */
#define CPLB_LOCK_P             1  /* 0=entry may be replaced, 1=entry locked */
#define CPLB_USER_RD_P          2  /* 0=no read access, 1=read access allowed (user mode) */
#define CPLB_PORTPRIO_P         9  /* 0=low priority port, 1= high priority port */
/*** ICPLB_DATA only */
#define CPLB_LRUPRIO_P          8  /* 0=can be replaced by any line, 1=priority for non-replacement */
/*** DCPLB_DATA only */
#define CPLB_USER_WR_P          3  /* 0=no write access, 0=write access allowed (user mode) */
#define CPLB_SUPV_WR_P          4  /* 0=no write access, 0=write access allowed (supervisor mode) */
#define CPLB_DIRTY_P            7  /* 1=dirty, 0=clean */
#define CPLB_L1_CHBL_P          12 /* 0=non-cacheable in L1, 1=cacheable in L1 */
#define CPLB_WT_P               14 /* 0=write-back, 1=write-through */
#define CPLB_L1_AOW_P           15 /* 0=do not allocate cache lines on write-through writes,  */
                                   /* 1= allocate cache lines on write-through writes. */

/* DCPLB_DATA and ICPLB_DATA Registers - Masks */
#define CPLB_VALID             0x00000001  /* 0=invalid entry, 1=valid entry */
#define CPLB_LOCK              0x00000002  /* 0=entry may be replaced, 1=entry locked */
#define CPLB_USER_RD           0x00000004  /* 0=no read access, 1=read access allowed (user mode) */
#define PAGE_SIZE_1KB          0x00000000  /* 1 KB page size */
#define PAGE_SIZE_4KB          0x00010000  /* 4 KB page size */
#define PAGE_SIZE_1MB          0x00020000  /* 1 MB page size */
#define PAGE_SIZE_4MB          0x00030000  /* 4 MB page size */
#define CPLB_PORTPRIO          0x00000200  /* 0=low priority port, 1= high priority port */
#define CPLB_L1_CHBL           0x00001000  /* 0=non-cacheable in L1, 1=cacheable in L1 */
/*** ICPLB_DATA only */
#define CPLB_LRUPRIO           0x00000100  /* 0=can be replaced by any line, 1=priority for non-replacement */
/*** DCPLB_DATA only */
#define CPLB_USER_WR           0x00000008  /* 0=no write access, 0=write access allowed (user mode) */
#define CPLB_SUPV_WR           0x00000010  /* 0=no write access, 0=write access allowed (supervisor mode) */
#define CPLB_DIRTY             0x00000080  /* 1=dirty, 0=clean */
#define CPLB_L1_AOW            0x00008000  /* 0=do not allocate cache lines on write-through writes,  */
                                           /* 1= allocate cache lines on write-through writes. */
#define CPLB_WT                0x00004000  /* 0=write-back, 1=write-through */



/* ITEST_COMMAND and DTEST_COMMAND Registers */
/*** Masks */
#define TEST_READ			   0x00000000  /* Read Access */
#define TEST_WRITE			   0x00000002  /* Write Access */
#define TEST_TAG			   0x00000000  /* Access TAG */
#define TEST_DATA			   0x00000004  /* Access DATA */
#define TEST_DW0			   0x00000000  /* Select Double Word 0 */
#define TEST_DW1			   0x00000008  /* Select Double Word 1 */
#define TEST_DW2			   0x00000010  /* Select Double Word 2 */
#define TEST_DW3			   0x00000018  /* Select Double Word 3 */
#define TEST_MB0			   0x00000000  /* Select Mini-Bank 0 */
#define TEST_MB1			   0x00010000  /* Select Mini-Bank 1 */
#define TEST_MB2			   0x00020000  /* Select Mini-Bank 2 */
#define TEST_MB3			   0x00030000  /* Select Mini-Bank 3 */
/* ensure macro params bracketed to avoid unexpected evaluations. (GA) MISRA Rule 19.10 */
#ifdef _MISRA_RULES
#define TEST_SET(x)		       (((x) << 5) & 0x03E0u)  /* Set Index 0->31 */
#else
#define TEST_SET(x)		       (((x) << 5) & 0x03E0)  /* Set Index 0->31 */
#endif /* _MISRA_RULES */
#define TEST_WAY0			   0x00000000  /* Access Way0 */
#define TEST_WAY1			   0x04000000  /* Access Way1 */
/*** ITEST_COMMAND only */
#define TEST_WAY2			   0x08000000  /* Access Way2 */
#define TEST_WAY3			   0x0C000000  /* Access Way3 */
/*** DTEST_COMMAND only */
#define TEST_BNKSELA		   0x00000000  /* Access SuperBank A */
#define TEST_BNKSELB		   0x00800000  /* Access SuperBank B */

#ifdef _MISRA_RULES
#pragma diag(pop)
#endif /* _MISRA_RULES */

#endif /* _DEF_LPBLACKFIN_H */
