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

/*
 * Implementation of stdlib.h/unistd.h functions.
 */

#include <limits.h>
#include <ctype.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

/* Oak modification: START */
// #include "third_party/nanolibc/c/libc_internals.h"

// void abort() { exit(-1); }

// void exit(int status) {
//   __nnlc_internal_data.sysdeps->exit(status);

//   /* runtime's exit() should not return */
//   fprintf(stderr, "exit() failed!!! Infinite loop...\n");
//   while (1) continue;
// }

// unsigned int sleep(unsigned int seconds) {
//   return __nnlc_internal_data.sysdeps->usleep(seconds * 1000000ULL);
// }

// unsigned int usleep(unsigned int useconds) {
//   return __nnlc_internal_data.sysdeps->usleep(useconds);
// }
/* Oak modification: END */

/*
 * string -> int conversions
 *
 * for all strtol variants, we use the same template source file
 */

#define _STRTOX_FNAME strtol
#define _STRTOX_SIGNED_TNAME long int
#define _STRTOX_VARIANT_UNSIGNED 0
#define _STRTOX_INTMIN LONG_MIN
#define _STRTOX_INTMAX LONG_MAX
#include "strtox.c"
#undef _STRTOX_FNAME
#undef _STRTOX_SIGNED_TNAME
#undef _STRTOX_VARIANT_UNSIGNED
#undef _STRTOX_INTMIN
#undef _STRTOX_INTMAX

#define _STRTOX_FNAME strtoll
#define _STRTOX_SIGNED_TNAME long long int
#define _STRTOX_VARIANT_UNSIGNED 0
#define _STRTOX_INTMIN LLONG_MIN
#define _STRTOX_INTMAX LLONG_MAX
#include "strtox.c"
#undef _STRTOX_FNAME
#undef _STRTOX_SIGNED_TNAME
#undef _STRTOX_VARIANT_UNSIGNED
#undef _STRTOX_INTMIN
#undef _STRTOX_INTMAX

#define _STRTOX_FNAME strtoul
#define _STRTOX_SIGNED_TNAME long int
#define _STRTOX_VARIANT_UNSIGNED 1
#define _STRTOX_INTMIN ULONG_MIN
#define _STRTOX_INTMAX ULONG_MAX
#include "strtox.c"
#undef _STRTOX_FNAME
#undef _STRTOX_SIGNED_TNAME
#undef _STRTOX_VARIANT_UNSIGNED
#undef _STRTOX_INTMIN
#undef _STRTOX_INTMAX

#define _STRTOX_FNAME strtoull
#define _STRTOX_SIGNED_TNAME long long int
#define _STRTOX_VARIANT_UNSIGNED 1
#define _STRTOX_INTMIN ULLONG_MIN
#define _STRTOX_INTMAX ULLONG_MAX
#include "strtox.c"
#undef _STRTOX_FNAME
#undef _STRTOX_SIGNED_TNAME
#undef _STRTOX_VARIANT_UNSIGNED
#undef _STRTOX_INTMIN
#undef _STRTOX_INTMAX

long int atol(const char *nptr) { return strtol(nptr, NULL, 10); }
