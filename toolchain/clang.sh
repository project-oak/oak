#!/bin/bash
set -o errexit

external/clang/bin/clang "$@"
