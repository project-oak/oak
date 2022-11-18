/*
 * Copyright 2022 The Project Oak Authors
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

#include <sys/syscall.h>

	.text
	.globl _start
	.type _start,@function
_start:
	xorl %ebp, %ebp
	movq %rdx, %r9
	popq %rsi
	movq %rsp, %rdx

	andq  $~15, %rsp
	pushq %rax

	pushq %rsp

	/* Oak TF Runtime dones't have __libc_start_main, jump to model app's main(). */
	call main

	/* Gracefully shut freestanding binary program down on Linux. */
	mov %eax,%edi
	mov $SYS_exit,%eax
	syscall

	.data
	.globl __data_start
__data_start:
	.long 0
	.weak data_start
	data_start = __data_start
