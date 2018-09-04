#include <stdio.h>
#include <SDL2/SDL.h>
//#include <emscripten.h>
#include <unistd.h>
#include <stdlib.h>

int main()
{
  SDL_LogSetAllPriority(SDL_LOG_PRIORITY_DEBUG);
  SDL_Init(SDL_INIT_VIDEO);

  SDL_Window *window;
  SDL_Renderer *renderer;

  SDL_CreateWindowAndRenderer(320, 200, 0, &window, &renderer);

  int result = 0;

  /**
   * Set up a blue background
   */
  SDL_SetRenderDrawColor(renderer, 128, 128, 255, 255);
  SDL_RenderClear(renderer);

  /**
   * Show what is in the renderer
   */
  SDL_RenderPresent(renderer);

  SDL_Delay(2000);

  printf("Done.\n");

  return 0;
}

