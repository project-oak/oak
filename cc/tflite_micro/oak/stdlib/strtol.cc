/*
 * Copyright (c) 1992 The Regents of the University of California.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include <ctype.h>
#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdlib.h>
#include <wchar.h>

template <typename T, T Min, T Max, typename CharT>
T StrToI(const CharT* nptr, CharT** endptr, int base) {
  // Ensure that base is between 2 and 36 inclusive, or the special value of 0.
  if (base < 0 || base == 1 || base > 36) {
    if (endptr != nullptr) *endptr = const_cast<CharT*>(nptr);
    errno = EINVAL;
    return 0;
  }

  // Skip white space and pick up leading +/- sign if any.
  // If base is 0, allow 0x for hex and 0 for octal, else
  // assume decimal; if base is already 16, allow 0x.
  const CharT* s = nptr;
  int c;
  do {
    c = *s++;
  } while (isspace(c));
  int neg;
  if (c == '-') {
    neg = 1;
    c = *s++;
  } else {
    neg = 0;
    if (c == '+') c = *s++;
  }
  if ((base == 0 || base == 16) && c == '0' && (*s == 'x' || *s == 'X') && isxdigit(s[1])) {
    c = s[1];
    s += 2;
    base = 16;
  }
  if ((base == 0 || base == 2) && c == '0' && (*s == 'b' || *s == 'B') && isdigit(s[1])) {
    c = s[1];
    s += 2;
    base = 2;
  }
  if (base == 0) base = (c == '0') ? 8 : 10;

  // We always work in the negative space because the most negative value has a
  // larger magnitude than the most positive value.
  T cutoff = Min / base;
  int cutlim = -(Min % base);
  // Non-zero if any digits consumed; negative to indicate overflow/underflow.
  int any = 0;
  T acc = 0;
  for (; ; c = *s++) {
    if (isdigit(c)) {
      c -= '0';
    } else if (isalpha(c)) {
      c -= isupper(c) ? 'A' - 10 : 'a' - 10;
    } else {
      break;
    }
    if (c >= base) break;
    if (any < 0) continue;
    if (acc < cutoff || (acc == cutoff && c > cutlim)) {
      any = -1;
      acc = Min;
      errno = ERANGE;
    } else {
      any = 1;
      acc *= base;
      acc -= c;
    }
  }
  if (endptr != nullptr) *endptr = const_cast<CharT*>(any ? s - 1 : nptr);
  if (!neg) {
    if (acc == Min) {
      errno = ERANGE;
      acc = Max;
    } else {
      acc = -acc;
    }
  }
  return acc;
}

template <typename T, T Max, typename CharT>
T StrToU(const CharT* nptr, CharT** endptr, int base) {
  if (base < 0 || base == 1 || base > 36) {
    if (endptr != nullptr) *endptr = const_cast<CharT*>(nptr);
    errno = EINVAL;
    return 0;
  }

  const CharT* s = nptr;
  int c;
  do {
    c = *s++;
  } while (isspace(c));
  int neg;
  if (c == '-') {
    neg = 1;
    c = *s++;
  } else {
    neg = 0;
    if (c == '+') c = *s++;
  }
  if ((base == 0 || base == 16) && c == '0' && (*s == 'x' || *s == 'X') && isxdigit(s[1])) {
    c = s[1];
    s += 2;
    base = 16;
  }
  if ((base == 0 || base == 2) && c == '0' && (*s == 'b' || *s == 'B') && isdigit(s[1])) {
    c = s[1];
    s += 2;
    base = 2;
  }
  if (base == 0) base = (c == '0') ? 8 : 10;

  T cutoff = Max / static_cast<T>(base);
  int cutlim = Max % static_cast<T>(base);
  T acc = 0;
  int any = 0;
  for (; ; c = *s++) {
    if (isdigit(c)) {
      c -= '0';
    } else if (isalpha(c)) {
      c -= isupper(c) ? 'A' - 10 : 'a' - 10;
    } else {
      break;
    }
    if (c >= base) break;
    if (any < 0) continue;
    if (acc > cutoff || (acc == cutoff && c > cutlim)) {
      any = -1;
      acc = Max;
      errno = ERANGE;
    } else {
      any = 1;
      acc *= base;
      acc += c;
    }
  }
  if (neg && any > 0) acc = -acc;
  if (endptr != nullptr) *endptr = const_cast<CharT*>(any ? s - 1 : nptr);
  return acc;
}

int atoi(const char* s) {
  return strtol(s, nullptr, 10);
}

long atol(const char* s) {
  return strtol(s, nullptr, 10);
}

long long atoll(const char* s) {
  return strtoll(s, nullptr, 10);
}

intmax_t strtoimax(const char* s, char** end, int base) {
  return StrToI<intmax_t, INTMAX_MIN, INTMAX_MAX, char>(s, end, base);
}

intmax_t wcstoimax(const wchar_t* s, wchar_t** end, int base) {
  return StrToI<intmax_t, INTMAX_MIN, INTMAX_MAX, wchar_t>(s, end, base);
}

long strtol(const char* s, char** end, int base) {
  return StrToI<long, LONG_MIN, LONG_MAX, char>(s, end, base);
}

long wcstol(const wchar_t* s, wchar_t** end, int base) {
  return StrToI<long, LONG_MIN, LONG_MAX, wchar_t>(s, end, base);
}

long long strtoll(const char* s, char** end, int base) {
  return StrToI<long long, LLONG_MIN, LLONG_MAX, char>(s, end, base);
}

long long wcstoll(const wchar_t* s, wchar_t** end, int base) {
  return StrToI<long long, LLONG_MIN, LLONG_MAX, wchar_t>(s, end, base);
}

unsigned long strtoul(const char* s, char** end, int base) {
  return StrToU<unsigned long, ULONG_MAX, char>(s, end, base);
}

unsigned long wcstoul(const wchar_t* s, wchar_t** end, int base) {
  return StrToU<unsigned long, ULONG_MAX, wchar_t>(s, end, base);
}

unsigned long long strtoull(const char* s, char** end, int base) {
  return StrToU<unsigned long long, ULLONG_MAX, char>(s, end, base);
}

unsigned long long wcstoull(const wchar_t* s, wchar_t** end, int base) {
  return StrToU<unsigned long long, ULLONG_MAX, wchar_t>(s, end, base);
}

uintmax_t strtoumax(const char* s, char** end, int base) {
  return StrToU<uintmax_t, UINTMAX_MAX, char>(s, end, base);
}

uintmax_t wcstoumax(const wchar_t* s, wchar_t** end, int base) {
  return StrToU<uintmax_t, UINTMAX_MAX, wchar_t>(s, end, base);
}
