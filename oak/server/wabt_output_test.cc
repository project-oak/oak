/*
 * Copyright 2019 The Project Oak Authors
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

#include "oak/server/wabt_output.h"

#include "gtest/gtest.h"

TEST(WabtOutput, KindName) {
  std::stringstream ss;
  ss << wabt::ExternalKind::Func;
  EXPECT_EQ("func", ss.str());
}

TEST(WabtOutput, TypeName) {
  std::stringstream ss;
  ss << wabt::Type::F32;
  EXPECT_EQ("f32", ss.str());
}

TEST(WabtOutput, TypeVector) {
  std::stringstream ss;
  std::vector<wabt::Type> vec0 = {};
  std::vector<wabt::Type> vec1 = {wabt::Type::I32};
  std::vector<wabt::Type> vec3 = {wabt::Type::Func, wabt::Type::I32, wabt::Type::F32};
  ss << vec0 << "|" << vec1 << "|" << vec3;
  EXPECT_EQ("()|(i32)|(func, i32, f32)", ss.str());
}

TEST(WabtOutput, FuncSignature) {
  std::stringstream ss;
  wabt::interp::FuncSignature sig0;
  wabt::interp::FuncSignature sig1{{wabt::Type::I32}, {wabt::Type::I32}};
  wabt::interp::FuncSignature sig2{{wabt::Type::I32, wabt::Type::F32}, {wabt::Type::I32}};
  ss << sig0 << "|" << sig1 << "|" << sig2;
  EXPECT_EQ("() -> ()|(i32) -> (i32)|(i32, f32) -> (i32)", ss.str());
}
