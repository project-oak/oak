# wac - WebAssembly in C

A Minimal WebAssembly interpreter written in C. Supports the
WebAssembly MVP (minimum viable product) version of the WebAssembly
specification.

There are two different builds of wac:

* **wac**: (WebAssembly in C) Minimal client with an interactive REPL
  mode. Designed to run standalone wasm files compiled with
  `wast2wasm` or `wasm-as`. Passes most spec tests apart from some
  multi-module import/export tests.
* **wace**: (WebAssembly in C with Emscripten) Client with host
  library/memory integration. Designed to run wasm code that has been
  built with Emscripten (using `-s SIDE_MODULE=1 -s LEGALIZE_JS_FFI=0`).

## Prerequisites

To build wac and wace you need a 32-bit version of gcc and 32-bit
versions of SDL2 and libedit. On 64-bit Ubuntu/Debian these can be
installed like this:

```
dpkg --add-architecture i386
apt-get update
apt-get install lib32gcc-4.9-dev libSDL2-dev:i386 libedit-dev:i386
```

To compile wast source files to binary wasm modules you will need the
wasm-as tool from [Binaryen](https://github.com/WebAssembly/binaryen).
To compile C programs to wasm modules you will need a [patched version
of emscripten](https://github.com/kanaka/emscripten), the [incoming
branch of fastcomp](https://github.com/kripken/emscripten-fastcomp)
and the [master branch of
binaryen](https://github.com/WebAssembly/binaryen).

As an alternative to downloading and building the above tools, the
`kanaka/emscripten` docker image (1.7GB) has 32-bit gcc
compiler/libraries, patched emscripten, and binaryen preinstalled. The
docker image can be started with appropriate file mounts like this:

```
docker run -v `pwd`:/wac -w /wac -it kanaka/emscripten bash
```

All the build commands below can be run within the docker container.


## wac usage

Build wac:

```bash
$ make wac
```

Use `wasm-as` to compile a simple wast program to a wasm:

```bash
$ make examples_wast/arith.wasm
```

Now load the compiled wasm file and invoke some functions:

```bash
$./wac examples_wast/arith.wasm add 2 3
0x5:i32
$./wac examples_wast/arith.wasm mul 7 8
0x38:i32
```

wac also supports a very simple REPL (read-eval-print-loop) mode that
runs commands in the form of `FUNC ARG...`:

```
$ ./wac --repl examples_wast/arith.wasm
> sub 10 5
0x5:i32
> div 13 4
0x3:i32
```

## wace usage

Build wace:

```bash
$ make wace
```

Use emscripten/binaryen to compile some simple C programs and run them
using wace:

```bash
$ make examples_c/hello1.wasm
$ ./wace examples_c/hello1.wasm
hello world

$ make examples_c/hello2.wasm
$ ./wace examples_c/hello2.wasm
hello malloc people
```

Use emscripten/binaryen to compile some C SDL programs and run them
using wace:

```bash
$ make examples_c/hello_sdl.wasm
$ ./wace examples_c/hello_sdl.wasm
INFO: OpenGL shaders: ENABLED
INFO: Created renderer: opengl
# Blue Window displayed for 2 seconds
Done.

$ make examples_c/triangle.wasm
$ ./wace examples_c/triangle.wasm
# A colorfully shaded triangle is rendered

$ make examples_c/hello_owl/hello_owl.wasm
$ ./wace examples_c/hello_owl/hello_owl.wasm
# An Owl image displayed for 2 seconds
```

## Running WebAssembly spec tests

wac includes a `runtest.py` test driver which can be used for running
tests from the WebAssembly specification.

Check out the spec:

```
git clone https://github.com/WebAssembly/spec
```

You will need `wast2wasm` to compile the spec tests. Check-out and
build [wabt](https://github.com/WebAssembly/wabt) (wabbit):

```
git clone --recursive https://github.com/WebAssembly/wabt
make -C wabt gcc-release
```

Run the `func.wast` test file (to test function calls) from the spec:

```
./runtest.py --wast2wasm ./wabt/out/gcc/Release/wast2wasm --interpreter ./wac spec/test/core/func.wast
```


## License

MPL-2.0
