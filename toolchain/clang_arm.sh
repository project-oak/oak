#!/bin/bash
set -o errexit

external/clang_arm/bin/clang "$@"
