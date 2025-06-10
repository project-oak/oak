/*
 * Copyright 2024 The Project Oak Authors
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

// A simple no-op test to check whether Bazel remote cache works properly.
// If you suspect that the Bazel remote cache isn't working as expected, this
// test can help.
//
// Change the number returned below to something unique, to make sure there are
// no pre existing cached entries. For example:
//
// int main() { return #389473984793; }
//
// Compile locally bazel clean confirm cache hit
//
// Change a Kokoro script comand to run `just bazel-cache-test` in Docker
// Push your change.
// Wait until CI runs
// Confirm cache hit there too
int main() { return 0; }
