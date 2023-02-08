/*
 * Copyright 2023 The Project Oak Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <stdio.h>
#include <unistd.h>

constexpr int CHANNEL_FD = 10;

int main(int argc, char* argv[]) {
  char buf;

  fprintf(stderr, "In main!\n");

  while (true) {
    if (read(CHANNEL_FD, &buf, sizeof(buf)) != 1) {
      return -1;
    }

    if (write(CHANNEL_FD, &buf, sizeof(buf)) != 1) {
      return -1;
    }
  }

  return 0;
}
