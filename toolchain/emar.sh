#!/bin/bash
set -o errexit

# These flags are necessary to prevent Emscripten from creating `~/.emscripten`
# and `~/.emscripten_cache.lock` files in the `~` directory,
# that doesn't exist inside a non-root Docker container.
if [[ -n '/tmp/.emscripten' ]]; then
  export EM_CONFIG='/tmp/.emscripten'
fi
if [[ -n '/tmp/.emscripten_cache' ]]; then
  export EM_CACHE='/tmp/.emscripten_cache'
  export EM_EXCLUSIVE_CACHE_ACCESS=1
fi

external/emsdk/emsdk/upstream/emscripten/emar "$@"
