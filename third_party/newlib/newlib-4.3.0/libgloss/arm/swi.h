#include "arm.h"
#include <_ansi.h>

/* SWI numbers for RDP (Demon) monitor.  */
#define SWI_WriteC                 0x0
#define SWI_Write0                 0x2
#define SWI_ReadC                  0x4
#define SWI_CLI                    0x5
#define SWI_GetEnv                 0x10
#define SWI_Exit                   0x11
#define SWI_EnterOS                0x16

#define SWI_GetErrno               0x60
#define SWI_Clock                  0x61
#define SWI_Time                   0x63
#define SWI_Remove                 0x64
#define SWI_Rename                 0x65
#define SWI_Open                   0x66

#define SWI_Close                  0x68
#define SWI_Write                  0x69
#define SWI_Read                   0x6a
#define SWI_Seek                   0x6b
#define SWI_Flen                   0x6c

#define SWI_IsTTY                  0x6e
#define SWI_TmpNam                 0x6f
#define SWI_InstallHandler         0x70
#define SWI_GenerateError          0x71


/* Now the SWI numbers and reason codes for RDI (Angel) monitors.  */
#if defined (SEMIHOST_V2) \
    && defined (SEMIHOST_V2_MIXED_MODE) \
    && !defined (THUMB_VXM)
  #define AngelSWI_ARM			0xE10F0070 /* HLT #0xF000 A32.  */
  #ifdef __thumb__
    #define AngelSWI			0xBABC /* HLT #0x3c T32.  */
  #else /* __thumb__.  */
    #define AngelSWI			AngelSWI_ARM
  #endif /* __thumb__.  */
#else  /* SEMIHOST_V2.  */
  #define AngelSWI_ARM			0x123456 /* SVC A32.  */
  #ifdef __thumb__
    #define AngelSWI			0xAB /* SVC T32.  */
  #else /* __thumb__.  */
    #define AngelSWI			AngelSWI_ARM
  #endif /* __thumb__.  */
#endif /* SEMIHOST_V2.  */

/* For thumb only architectures use the BKPT instruction instead of SWI.  */
#ifdef THUMB_VXM
  #define AngelSWIInsn			"bkpt"
  #define AngelSWIAsm(IMM)		bkpt IMM
#elif defined (SEMIHOST_V2) && defined (SEMIHOST_V2_MIXED_MODE)
  /* This is actually encoding the HLT instruction, however we don't have
     support for this in older assemblers.  So we have to encode the
     instruction manually.  */
  #define AngelSWIInsn			".inst"
  #define AngelSWIAsm(IMM)		.inst IMM
#else
  #define AngelSWIInsn			"swi"
  #define AngelSWIAsm(IMM)		swi IMM
#endif

/* The reason codes:  */
#define AngelSWI_Reason_Open			0x01
#define AngelSWI_Reason_Close			0x02
#define AngelSWI_Reason_WriteC			0x03
#define AngelSWI_Reason_Write0			0x04
#define AngelSWI_Reason_Write			0x05
#define AngelSWI_Reason_Read			0x06
#define AngelSWI_Reason_ReadC			0x07
#define AngelSWI_Reason_IsError			0x08
#define AngelSWI_Reason_IsTTY			0x09
#define AngelSWI_Reason_Seek			0x0A
#define AngelSWI_Reason_FLen			0x0C
#define AngelSWI_Reason_TmpNam			0x0D
#define AngelSWI_Reason_Remove			0x0E
#define AngelSWI_Reason_Rename			0x0F
#define AngelSWI_Reason_Clock			0x10
#define AngelSWI_Reason_Time			0x11
#define AngelSWI_Reason_System			0x12
#define AngelSWI_Reason_Errno			0x13
#define AngelSWI_Reason_GetCmdLine		0x15
#define AngelSWI_Reason_HeapInfo		0x16
#define AngelSWI_Reason_EnterSVC		0x17
#define AngelSWI_Reason_ReportException		0x18
#define AngelSWI_Reason_ReportExceptionExtended 0x20
#define AngelSWI_Reason_Elapsed			0x30
#define AngelSWI_Reason_TickFreq		0x31
#define ADP_Stopped_ApplicationExit		((2 << 16) + 38)
#define ADP_Stopped_RunTimeError		((2 << 16) + 35)

/* Semihosting feature magic numbers.  */
#define NUM_SHFB_MAGIC			4
#define SHFB_MAGIC_0			0x53
#define SHFB_MAGIC_1			0x48
#define SHFB_MAGIC_2			0x46
#define SHFB_MAGIC_3			0x42

/* Semihosting extensions.  */
#define SH_EXT_EXIT_EXTENDED_BITNUM	0x0
#define SH_EXT_STDOUT_STDERR_BITNUM	0x1

#if !defined (__ASSEMBLER__)
extern int _get_semihosting_exts (char*, int, int);
extern int _has_ext_exit_extended (void);
extern int _has_ext_stdout_stderr (void);
#endif

#if defined(ARM_RDI_MONITOR) && !defined(__ASSEMBLER__)

static inline int
do_AngelSWI (int reason, void * arg)
{
  int value;
  asm volatile ("mov r0, %1; mov r1, %2; " AngelSWIInsn " %a3; mov %0, r0"
       : "=r" (value) /* Outputs */
       : "r" (reason), "r" (arg), "i" (AngelSWI) /* Inputs */
       : "r0", "r1", "r2", "r3", "ip", "lr", "memory", "cc"
		/* Clobbers r0 and r1, and lr if in supervisor mode */);
                /* Accordingly to page 13-77 of ARM DUI 0040D other registers
                   can also be clobbered.  Some memory positions may also be
                   changed by a system call, so they should not be kept in
                   registers. Note: we are assuming the manual is right and
                   Angel is respecting the APCS.  */
  return value;
}

#endif
