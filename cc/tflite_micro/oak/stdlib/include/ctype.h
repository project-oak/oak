//  Copyright 2022 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef THIRD_PARTY_NANOLIBC_C_INCLUDE_CTYPE_H_
#define THIRD_PARTY_NANOLIBC_C_INCLUDE_CTYPE_H_

#include <stdint.h>
#include <sys/_cdefs.h>

__BEGIN_DECLS

#define NNLC_ISALNUM 0x1
#define NNLC_ISALPHA 0x2
#define NNLC_ISASCII 0x4
#define NNLC_ISBLANK 0x8
#define NNLC_ISCNTRL 0x10
#define NNLC_ISDIGIT 0x20
#define NNLC_ISGRAPH 0x40
#define NNLC_ISLOWER 0x80
#define NNLC_ISPRINT 0x100
#define NNLC_ISPUNCT 0x200
#define NNLC_ISSPACE 0x400
#define NNLC_ISUPPER 0x800
#define NNLC_ISXDIGIT 0x1000

extern uint16_t nnlc_ctype_table[256];

#define isalnum(c) ((nnlc_ctype_table[0xff & (uint8_t)(c)] & NNLC_ISALNUM) != 0)
#define isalpha(c) ((nnlc_ctype_table[0xff & (uint8_t)(c)] & NNLC_ISALPHA) != 0)
#define isascii(c) ((nnlc_ctype_table[0xff & (uint8_t)(c)] & NNLC_ISASCII) != 0)
#define isblank(c) ((nnlc_ctype_table[0xff & (uint8_t)(c)] & NNLC_ISBLANK) != 0)
#define iscntrl(c) ((nnlc_ctype_table[0xff & (uint8_t)(c)] & NNLC_ISCNTRL) != 0)
#define isdigit(c) ((nnlc_ctype_table[0xff & (uint8_t)(c)] & NNLC_ISDIGIT) != 0)
#define isgraph(c) ((nnlc_ctype_table[0xff & (uint8_t)(c)] & NNLC_ISGRAPH) != 0)
#define islower(c) ((nnlc_ctype_table[0xff & (uint8_t)(c)] & NNLC_ISLOWER) != 0)
#define isprint(c) ((nnlc_ctype_table[0xff & (uint8_t)(c)] & NNLC_ISPRINT) != 0)
#define ispunct(c) ((nnlc_ctype_table[0xff & (uint8_t)(c)] & NNLC_ISPUNCT) != 0)
#define isspace(c) ((nnlc_ctype_table[0xff & (uint8_t)(c)] & NNLC_ISSPACE) != 0)
#define isupper(c) ((nnlc_ctype_table[0xff & (uint8_t)(c)] & NNLC_ISUPPER) != 0)
#define isxdigit(c) \
  ((nnlc_ctype_table[0xff & (uint8_t)(c)] & NNLC_ISXDIGIT) != 0)

// Not MT-safe.
extern int nnlc_ctype_temp;
#define tolower(c)        \
  (nnlc_ctype_temp = (c), \
   isupper(nnlc_ctype_temp) ? nnlc_ctype_temp - 'A' + 'a' : nnlc_ctype_temp)
#define toupper(c)        \
  (nnlc_ctype_temp = (c), \
   islower(nnlc_ctype_temp) ? nnlc_ctype_temp - 'a' + 'A' : nnlc_ctype_temp)
#define toascii(c) ((c)&0x7f)

__END_DECLS

#endif  // THIRD_PARTY_NANOLIBC_C_INCLUDE_CTYPE_H_
