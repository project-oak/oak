#
# Copyright 2023 The Project Oak Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

.text
.global _start

_start:
    movq $0, %rbp
    pushq %rbp
    pushq %rbp
    movq %rsp, %rbp

    call _init

    # argc = 0, argv = NULL, envp = NULL
    xor %rdi, %rdi
    xor %rsi, %rsi
    xor %rdx, %rdx
    call main
    mov %rax, %rdi # rdi = rax
    call _exit

3:
    nop
    jmp 3b