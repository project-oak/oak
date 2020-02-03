/*
 * Copyright 2020 The Project Oak Authors
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

#include "oak/common/hmac.h"

#include "gtest/gtest.h"

namespace oak {
namespace utils {

// Reference:
// https://gchq.github.io/CyberChef/#recipe=HMAC(%7B'option':'UTF8','string':''%7D,'SHA256')From_Hex('None')To_Hex('%5C%5Cx')
TEST(Hmac, EmptyKeyEmptyMessage) {
  auto out = hmac_sha256("", "").ValueOrDie();
  ASSERT_EQ(
      "\xb6\x13\x67\x9a\b\x14\xd9\xec\x77\x2f\x95\xd7\x78\xc3\x5f\xc5\xff\x16\x97\xc4\x93\x71\x56"
      "\x53\xc6\xc7\x12\x14\x42\x92\xc5\xad",
      out);
}

// Reference:
// https://gchq.github.io/CyberChef/#recipe=HMAC(%7B'option':'UTF8','string':''%7D,'SHA256')From_Hex('None')To_Hex('%5C%5Cx')&input=dGVzdC1tZXNzYWdl
TEST(Hmac, EmptyKeyNonemptyMessage) {
  auto out = hmac_sha256("", "test-message").ValueOrDie();
  ASSERT_EQ(
      "\x88\xf9\xb4\x1c\xe3\x7a\x83\x87\xcd\x42\x5b\x46\x1a\x79\x59\xf3\x28\x3d\xb8\x49\x4a\x61\xdb"
      "\x44\xb3\x41\x18\x9d\xd7\xd2\x35\x96",
      out);
}

// Reference:
// https://gchq.github.io/CyberChef/#recipe=HMAC(%7B'option':'UTF8','string':'test-key'%7D,'SHA256')From_Hex('None')To_Hex('%5C%5Cx')
TEST(Hmac, NonemptyKeyEmptyMessage) {
  auto out = hmac_sha256("test-key", "").ValueOrDie();
  ASSERT_EQ(
      "\x27\x11\xcc\x23\xe9\xab\x1b\x8a\x9b\xc0\xfe\x99\x12\x38\xda\x92\x67\x16\x24\xa9\xeb\xda\xf1"
      "\xc1\xab\xec\x06\xe7\xe9\xa1\x4f\x9b",
      out);
}

// Reference:
// https://gchq.github.io/CyberChef/#recipe=HMAC(%7B'option':'UTF8','string':'test-key'%7D,'SHA256')From_Hex('None')To_Hex('%5C%5Cx')&input=dGVzdC1tZXNzYWdl
TEST(Hmac, NonemptyKeyNonemptyMessage) {
  auto out = hmac_sha256("test-key", "test-message").ValueOrDie();
  ASSERT_EQ(
      "\xf8\xc2\xbb\x87\xc1\x76\x08\xc9\x03\x8e\xab\x4e\x92\xef\x27\x75\xe4\x26\x29\xc9\x39\xd6\xfd"
      "\x33\x90\xd4\x2f\x80\xaf\x6b\xb7\x12",
      out);
}

}  // namespace utils
}  // namespace oak
