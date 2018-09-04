CC = emcc
all: hello_owl.c
	$(CC) hello_owl.c -O2 -s USE_SDL=2 -s USE_SDL_IMAGE=2 -s SDL2_IMAGE_FORMATS='["png"]' --preload-file assets -o hello_owl.html
