#!/bin/bash
set -o errexit
set -o xtrace

external/clang_llvm/bin/clang "$@"
