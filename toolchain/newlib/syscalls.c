//
// Copyright 2023 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

#include <errno.h>
#include <reent.h>
#include <sys/stat.h>
#include <sys/types.h>

static long __syscall0(long n) {
  unsigned long ret;
  asm volatile("syscall" : "=a"(ret) : "a"(n) : "rcx", "r11", "memory");
  return ret;
}

static long __syscall3(long n, long a1, long a2, long a3) {
  unsigned long ret;
  asm volatile("syscall" : "=a"(ret) : "a"(n), "D"(a1), "S"(a2), "d"(a3) : "rcx", "r11", "memory");
  return ret;
}

static long __syscall6(long n, long a1, long a2, long a3, long a4, long a5, long a6) {
  unsigned long ret;
  register long r10 asm("r10") = a4;
  register long r8 asm("r8") = a5;
  register long r9 asm("r9") = a6;
  asm volatile("syscall"
               : "=a"(ret)
               : "a"(n), "D"(a1), "S"(a2), "d"(a3), "r"(r10), "r"(r8), "r"(r9)
               : "rcx", "r11", "memory");
  return ret;
}

void _exit(int rc) {
  __syscall0(60);
  for (;;) {
  }
}

ssize_t _read_r(struct _reent* reent, int fd, void* buf, size_t len) {
  int ret = __syscall3(0, fd, (long)buf, len);

  if (ret < 0) {
    reent->_errno = ret;
    return -1;
  }
  return ret;
}

ssize_t _write_r(struct _reent* reent, int fd, const void* buf, size_t len) {
  int ret = __syscall3(1, fd, (long)buf, len);

  if (ret < 0) {
    reent->_errno = ret;
    return -1;
  }
  return ret;
}

ssize_t _lseek_r(struct _reent* reent, int fd, _off_t ptr, int dir) {
  reent->_errno = ENOSYS;
  return -1;
}

void* mmap(void* addr, int len, int prot, int flags, int fd, int offset) {
  return __syscall6(9, (long)addr, len, prot, flags, fd, offset);
}

void* _sbrk_r(struct _reent* reent, ptrdiff_t incr) {
  extern char end asm("_end");  // symbol provided by the linker
  static char* heap_end;

  if (heap_end == NULL) {
    // If we haven't initialized the heap at all yet, let's start at the next 2 MiB page boundary
    // after `_end`.
    heap_end = &end;

    if ((int)heap_end % 0x200000 != 0) {
      heap_end += 0x200000 - (int)heap_end % 0x200000;
    }
  }

  // We only increment in chunks of 2 MiB.
  if (incr % 0x200000 != 0) {
    incr += 0x200000 - incr % 0x200000;
  }

  char* prev_heap_end = heap_end;

  if (mmap(heap_end, incr,
           0x1 | 0x2,           // PROT_READ | PROT_WRITE
           0x02 | 0x10 | 0x20,  // MAP_PRIVATE | MAP_FIXED | MAP_ANONYMOUS
           -1, 0) != heap_end) {
    reent->_errno = ENOMEM;
    return -1;
  }

  heap_end += incr;

  return prev_heap_end;
}

int _open_r(struct _reent* reent, const char* file, int flags, int mode) {
  reent->_errno = ENOSYS;
  return -1;
}

int _close_r(struct _reent* reent, int fd) {
  reent->_errno = ENOSYS;
  return -1;
}

int _fstat_r(struct _reent* reent, int fd, struct stat* s) {
  reent->_errno = ENOSYS;
  return -1;
}

int _isatty_r(struct _reent* reent, int fd) {
  reent->_errno = ENOSYS;
  return -1;
}

int _getpid_r(struct _reent* reent) {
  reent->_errno = ENOSYS;
  return -1;
}

int _kill_r(struct _reent* reent, int pid, int signal) {
  reent->_errno = ENOSYS;
  return -1;
}

int getentropy(void* ptr, size_t n) { return -1; }
