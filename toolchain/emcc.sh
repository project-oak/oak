#!/bin/bash
set -o errexit

external/emsdk/emsdk/upstream/emscripten/emcc "$@"
