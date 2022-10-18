#include "tflite_micro.h"

#include <stdint.h>

int main(int argc, char* argv[]) {
  if (tflite_init(nullptr, 0, nullptr, 0) == 0) {
    while (true) {
      tflite_run(nullptr, 0, nullptr, nullptr);
    }
  }

  return 0;
}