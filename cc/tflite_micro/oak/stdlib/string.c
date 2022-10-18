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
 * Implementation of libC string.h functions.
 */

#include <stddef.h>
#include <ctype.h>
#include <stdlib.h>
/* Oak modification: START */
// #include <string.h>
/* Oak modification: END */

/* These are weak symbols, so that we continue using gnu-efi's version
 * when we link against it */
int memcmp(const void *p1, const void *p2, size_t n)
    __attribute__ ((weak));
void *memcpy(void *dstpp, const void *srcpp, size_t n)
    __attribute__ ((weak));
void *memmove(void *dstpp, const void *srcpp, size_t n)
    __attribute__ ((weak));
void *memset(void *dstpp, int c, size_t n)
    __attribute__ ((weak));

/* Highly NON optimized, but simple */
int memcmp(const void *p1, const void *p2, size_t n) {
  const char *s1 = p1;
  const char *s2 = p2;

  while (n > 0) {
    if (*s1 != *s2) return *s1 - *s2;

    s1++;
    s2++;
    n--;
  }

  return 0;
}

/* Highly NON optimized, but simple */
void *memcpy(void *dstpp, const void *srcpp, size_t n) {
  char *d = dstpp;
  const char *s = srcpp;

  while (n > 0) {
    *d++ = *s++;
    n--;
  }

  return dstpp;
}

/* Highly NON optimized, but simple */
void *memmove(void *dstpp, const void *srcpp, size_t n) {
  if (dstpp <= srcpp) {
    return memcpy(dstpp, srcpp, n);
  }
  char *d = dstpp + n;
  const char *s = srcpp + n;

  while (n > 0) {
    *--d = *--s;
    n--;
  }

  return dstpp;
}

/* Highly NON optimized, but simple */
void *memset(void *dstpp, int c, size_t n) {
  char *d = dstpp;

  while (n > 0) {
    *d++ = c;
    n--;
  }

  return dstpp;
}

const void *rawmemchr(const void *spp, int c) {
  const unsigned char *s = spp;

  while (*s != (unsigned char)c) s++;

  return s;
}

void *memchr(const void *spp, int c, size_t n) {
  const unsigned char *s = spp;

  while (n-- != 0) {
    if (*s == (unsigned char)c) {
      return (void*)s;
    }
    s++;
  }

  return NULL;
}

int strcmp(const char *p1, const char *p2) {
  const unsigned char *s1 = (const unsigned char *)p1;
  const unsigned char *s2 = (const unsigned char *)p2;

  while (1) {
    const unsigned char c1 = *s1++;
    const unsigned char c2 = *s2++;
    if ((c1 == '\0') || (c1 != c2)) return (c1 - c2);
  }

  /* not reached */
  return 0;
}

/* Highly NON optimized, but simple */
int strncmp(const char *p1, const char *p2, size_t n) {
  const unsigned char *s1 = (const unsigned char *)p1;
  const unsigned char *s2 = (const unsigned char *)p2;

  while (n > 0) {
    const unsigned char c1 = *s1++;
    const unsigned char c2 = *s2++;
    if ((c1 == '\0') || (c1 != c2)) return (c1 - c2);
    n--;
  }

  return 0;
}

char *strcpy(char *dest, const char *src) {
  char *d = dest;
  const char *s = src;

  while (*s) *d++ = *s++;

  *d = '\0';
  return dest;
}

/* strncpy borrowed from Linux man pages 3.35 */
char *strncpy(char *dest, const char *src, size_t n) {
  size_t i;

  for (i = 0; i < n && src[i] != '\0'; i++) dest[i] = src[i];
  for (; i < n; i++) dest[i] = '\0';

  return dest;
}

/* Highly NON optimized, but simple */
size_t strlen(const char *s) {
  size_t i;
  for (i = 0; *s; ++s, ++i) continue;
  return i;
}

char *strchr(const char *s, int i) {
  for (; *s; ++s)
    if (*s == i) return (char *)s;

  return NULL;
}

char *strrchr(const char *s, int i) {
  const char *last = NULL;

  for (; *s; ++s)
    if (*s == i) last = s;

  return (char *)last;
}

const char *strstr(const char *haystack, const char *needle) {
  const char *h = haystack;
  const char *n = needle;
  const char *found = NULL;

  if (*needle == '\0') return haystack;

  while (*h) {
    if ((found != NULL) && (*h != *n)) {
      found = NULL;
      n = needle;
    }

    if (*h == *n) {
      if (found == NULL) found = h;
      n++;
      if (*n == '\0') return found;
    }

    h++;
  }

  return NULL;
}

/* strspn borrowed from eglibc 2.17 */
size_t strspn(const char *s, const char *accept) {
  const char *p;
  const char *a;
  size_t count = 0;

  for (p = s; *p != '\0'; ++p) {
    for (a = accept; *a != '\0'; ++a)
      if (*p == *a) break;
    if (*a == '\0')
      return count;
    else
      ++count;
  }

  return count;
}

/* Naive O(M*N) implementation, good enough if "accept" is small */
const char *strpbrk(const char *s, const char *accept) {
  while (*s != '\0') {
    const char *a = accept;
    while (*a != '\0')
      if (*a++ == *s) return s;
    ++s;
  }

  return NULL;
}

/* strtok_r borrowed from eglibc 2.17's strtok */
char *strtok_r(char *s, const char *delim, char **saveptr) {
  char *token;

  if (s == NULL) s = *saveptr;

  /* Scan leading delimiters.  */
  s += strspn(s, delim);
  if (*s == '\0') {
    *saveptr = s;
    return NULL;
  }

  /* Find the end of the token.  */
  token = s;
  s = (char *)strpbrk(token, delim);
  if (s == NULL) {
    /* This token finishes the string.  */
    *saveptr = (char *)rawmemchr(token, '\0');
  } else {
    /* Terminate the token and make *saveptr point past it.  */
    *s = '\0';
    *saveptr = s + 1;
  }
  return token;
}

char *strtok(char *s, const char *delim) {
  static char *global_saveptr = NULL;
  return strtok_r(s, delim, &global_saveptr);
}

/* Oak modification: START */
// char *strdup(const char *s) {
//   const size_t len = strlen(s);
//   char *result = malloc(len+1);
//   if (NULL != result) {
//     strcpy(result, s);
//   }
//   return result;
// }

// char *strndup(const char *s, size_t n) {
//   size_t len = strlen(s);
//   if (n < len) {
//     len = n;
//   }
//   char *result = malloc(len+1);
//   if (NULL != result) {
//     memcpy(result, s, len);
//     result[len] = '\0';
//   }
//   return result;
// }

// int errno = 0; /* NOT MT-aware/MT-safe */
/* Oak modification: END */

char *strerror(int errnum) {
  if (errnum == 0) return "no error";
  return "unexpected error";
}