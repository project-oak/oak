#!/bin/bash
set -o errexit

# These flags are necessary to prevent Emscripten from creating `~/.emscripten`,
# `~/.emscripten_cache.lock` and `~/.emscripten_sanity_wasm` files in the 
# `~` directory, that doesn't exist inside a non-root Docker container.
EMSDK='/usr/local/emsdk/'
EM_CONFIG="${EMSDK}/.emscripten"
EM_CACHE="${EMSDK}/.emscripten_cache"
if [[ -n "${EM_CONFIG}" ]]; then
  export EM_CONFIG="${EM_CONFIG}"
  export EMCC_SKIP_SANITY_CHECK=1
fi
if [[ -n "${EM_CACHE}" ]]; then
  export EM_CACHE="${EM_CACHE}"
  export EM_EXCLUSIVE_CACHE_ACCESS=1
fi

external/emsdk/emsdk/upstream/emscripten/emar "$@"
