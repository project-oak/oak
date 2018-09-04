##########################################################
# User configurable build options

# WARNING: GPL license implications from using READLINE
USE_READLINE ?=

CFLAGS ?= -O2

EXTRA_WAC_LIBS ?=
EXTRA_WACE_LIBS ?=

##########################################################

CC = gcc -std=gnu99 -m32
EMCC = emcc $(CFLAGS) -s WASM=1 -s SIDE_MODULE=1 -s LEGALIZE_JS_FFI=0

WAC_LIBS = m dl $(RL_LIBRARY) $(EXTRA_WAC_LIBS)
WACE_LIBS = m dl $(RL_LIBRARY) SDL2 SDL2_image GL glut $(EXTRA_WACE_LIBS)

ifeq (,$(USE_READLINE))
    RL_LIBRARY ?= edit
else
    RL_LIBRARY ?= readline
    CFLAGS += -DUSE_READLINE=1
endif

# Basic build rules
thunks.c:
	python ./gen_thunks.py

%.a: %.o
	ar rcs $@ $^

%.o: %.c
	$(CC) -c $(filter %.c,$^) -o $@

# Additional dependencies
util.o: util.h
wa.o: wa.h util.h
thunks.o: thunks.h
wa.a: util.o thunks.o


wac: wac.c wa.a
	$(CC) -rdynamic $^ -o $@ $(foreach l,$(WAC_LIBS),-l$(l))

wace: wace.c wa.a
	$(CC) -rdynamic $^ -o $@ $(foreach l,$(WACE_LIBS),-l$(l))


.PHONY:
clean:
	rm -f *.o *.a wac wace wace-sdl.c \
	    examples_c/*.js examples_c/*.html \
	    examples_c/*.wasm examples_c/*.wast \
	    examples_wast/*.wasm

##########################################################

# Wast example build rules
examples_wast/%.wasm: examples_wast/%.wast
	wasm-as $< -o $@


# General C example build rules
examples_c/%.wasm: examples_c/%.c
	$(EMCC) -I examples_c/include -s USE_SDL=2 $< -o $@

.SECONDARY:
examples_c/%.wast: examples_c/%.wasm
	wasm-dis $< -o $@

examples_c/%: examples_c/%.c
	$(CC) $< -o $@ -lSDL2 -lSDL2_image -lGL -lglut

