/*
 * Copyright 2019 The Project Oak Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef OAK_MODULE_PLACEHOLDERS_H_
#define OAK_MODULE_PLACEHOLDERS_H_

#include <assert.h>
#include <math.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

// When Emscripten generates a Wasm file from TensorFlow, it leaves unresolved symbols 
// (imported functions), and these symbols prevend running TensorFlow in the Oak Runtime.
// So we currently patch these unresolved symbols with non-functional implementations.
// TODO: These placeholders should be deleted after resolving:
// https://github.com/project-oak/oak/issues/482
#define PLACEHOLDER(ret, name, ...) ret name(__VA_ARGS__) { abort(); }

extern "C" {

int __syscall5(int, int) { return NULL; }
int __syscall192(int, int) { return NULL; }
int __syscall194(int, int) { return NULL; }

int fstat(int, struct stat*) { return NULL; }
ssize_t lgetxattr(const char*, const char*, void*, size_t) { return NULL; }
ssize_t listxattr(const char*, char*, size_t) { return NULL; }

void* dlopen(const char*, int) { return NULL; }
long sysconf(int) { return NULL; }

int clock_gettime(clockid_t, struct timespec*) { return NULL; }
int nanosleep(const struct timespec*, struct timespec*) { return NULL; }

double round(double x) { return __builtin_round(x); }
float roundf(float x) { return __builtin_roundf(x); }

// The implementation was taken from:
// https://github.com/m-labs/compiler-rt-lm32/blob/06cc76fb7060dcd822cd67ca9affef9cadf8c443/lib/powidf2.c#L19-L34
double __powidf2(double a, int b) {
  const int recip = b < 0;
  double r = 1;
  while (1) {
    if (b & 1) r *= a;
    b /= 2;
    if (b == 0) break;
    a *= a;
  }
  return recip ? 1 / r : r;
}

int pthread_cond_destroy(pthread_cond_t*) { return NULL; }
int pthread_cond_init(pthread_cond_t*, const pthread_condattr_t*) { return NULL; }
int pthread_create(pthread_t*, const pthread_attr_t*, void* (*)(void*), void*) { return NULL; }
int pthread_equal(pthread_t, pthread_t) { return NULL; }
void pthread_exit(void*) { exit(0); }
int pthread_join(pthread_t, void**) { return NULL; }
int pthread_setcancelstate(int, int*) { return NULL; }

}  // extern "C"

#endif  // OAK_MODULE_PLACEHOLDERS_H_
