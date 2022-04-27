ENTRY(ram32_start) /* coreboot uses the ELF entrypoint */

PHDRS
{
  ram  PT_LOAD FILEHDR PHDRS ;
  note PT_NOTE               ;
}

/* Loaders like to put stuff in low memory (< 1M), so we don't use it. */
ram_min = 1M;

SECTIONS
{
  /* Mapping the program headers and note into RAM makes the file smaller. */
  . = ram_min;
  . += SIZEOF_HEADERS;
  .note : { *(.note) } :note :ram

  /* These sections are mapped into RAM from the file. Omitting :ram from
     later sections avoids emitting empty sections in the final binary.       */
  data_start = .;
  .rodata : { *(.rodata .rodata.*) } :ram
  . = ALIGN(4K);
  text_start = .;
  .text   : { *(.text .text.*)     }
  .text32 : { *(.text32)           }
  . = ALIGN(4K);
  text_end = .;
  .data   : { *(.data .data.*)     }
  data_size = . - data_start;

  /* The BSS section isn't mapped from file data. It is just zeroed in RAM. */
  .bss : {
    bss_start = .;
    *(.bss .bss.*)
    bss_size = . - bss_start;
  }

  /* Our stack grows down and is page-aligned. TODO: Add stack guard pages. */
  .stack (NOLOAD) : ALIGN(4K) { . += 128K; }
  stack_start = .;
  /* ram32.s only maps the first 2 MiB, and that must include the stack. */
  ASSERT((. <= 2M), "Stack overflows initial identity-mapped memory region")

  /* Strip symbols from the output binary (comment out to get symbols) */
  /DISCARD/ : {
    *(.symtab)
    *(.strtab)
  }
}
