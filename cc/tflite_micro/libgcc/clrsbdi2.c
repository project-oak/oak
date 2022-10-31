/*
 * Copyright 2022 The Project Oak Authors
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

// Count the number of leading redundant sign bits.
// Used by CountLeadingSignBits in TFLM kernels.
int __clrsbdi2(long long x) {
  int ret;

  if (x < 0LL)
    x = ~x;

  if (x == 0LL)
    return 8 * sizeof(x) - 1;

  ret = __builtin_clzll((unsigned long long)x);
  return ret - 1;
}
