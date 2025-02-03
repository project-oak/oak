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

#ifndef CC_OAK_SESSION_TESTING_MATCHERS_H_
#define CC_OAK_SESSION_TESTING_MATCHERS_H_
#include "gmock/gmock.h"

// A matcher that verifies that ErrorOr* types contain a result.
// Works with ErrorOrBytes, ErrorOrClientSession, ErrorOrServerSession.
MATCHER(IsResult, "Contains result and no error") {
  if (arg.error != nullptr) {
    *result_listener << "Expected no error, but have:  " << arg.error->message;
    return false;
  }
  if (arg.result == nullptr) {
    *result_listener
        << "Expected non-null result, but both error and result are null.";
    return false;
  }
  return true;
}

// A matcher that verifies that ErrorOr* types contain an error.
MATCHER(IsError, "Contains error and no result") {
  if (arg.result != nullptr) {
    *result_listener << "Expected no result, but have:  " << *arg.result;
    return false;
  }
  if (arg.error == nullptr) {
    *result_listener
        << "Expected non-null error, but both error and result are null.";
    return false;
  }
  return true;
}

// A matcher that verifies that an Error* is null.
MATCHER(NoError, "") {
  if (arg != nullptr) {
    *result_listener << "Expected non-null error, but got: " << arg->message;
    return false;
  }
  return true;
}

#endif  // CC_OAK_SESSION_TESTING_MATCHERS_H_
