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

#include "oak/common/app_config.h"

#include <fstream>
#include <memory>

#include "absl/memory/memory.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"

namespace oak {

namespace {

// Fixture class for testing `ApplicationConfiguration` correctness.
class ApplicationConfigurationTest : public ::testing::Test {
 protected:
  void TearDown() override {
    // Clean up temporary files.
    std::remove(kTmpFilename.c_str());
  }

  std::unique_ptr<ApplicationConfiguration> ConfigFrom(const std::string& filename) {
    std::ifstream ifs(filename.c_str(), std::ios::in | std::ios::binary);
    EXPECT_TRUE(ifs.is_open()) << "failed to open " << filename;
    std::stringstream ss;
    ss << ifs.rdbuf();
    ifs.close();

    auto config = absl::make_unique<ApplicationConfiguration>();
    google::protobuf::TextFormat::MergeFromString(ss.str(), config.get());
    return config;
  }

  const std::string kTmpFilename = "oak/common/testdata/tmp.bin";
};

TEST_F(ApplicationConfigurationTest, Default) {
  std::unique_ptr<ApplicationConfiguration> got = DefaultConfig("<bytes>");
  std::unique_ptr<ApplicationConfiguration> want =
      ConfigFrom("oak/common/testdata/barenode.textproto");
  ASSERT_EQ(want->DebugString(), got->DebugString());
  ASSERT_EQ(true, ValidApplicationConfig(*got));
}

TEST_F(ApplicationConfigurationTest, ReadWriteFile) {
  std::ifstream existing_file(kTmpFilename, std::ifstream::in);
  ASSERT_FALSE(existing_file.is_open());
  std::unique_ptr<ApplicationConfiguration> want = DefaultConfig("<bytes>");
  WriteConfigToFile(want.get(), kTmpFilename);
  std::unique_ptr<ApplicationConfiguration> got = ReadConfigFromFile(kTmpFilename);
  ASSERT_EQ(want->DebugString(), got->DebugString());
  ASSERT_EQ(true, ValidApplicationConfig(*got));
}

TEST_F(ApplicationConfigurationTest, DefaultPlusLogging) {
  std::unique_ptr<ApplicationConfiguration> got = DefaultConfig("<bytes>");
  AddLoggingToConfig(got.get());
  std::unique_ptr<ApplicationConfiguration> want =
      ConfigFrom("oak/common/testdata/lognode.textproto");
  ASSERT_EQ(want->DebugString(), got->DebugString());
  ASSERT_EQ(true, ValidApplicationConfig(*got));
}

TEST_F(ApplicationConfigurationTest, DefaultPlusStorage) {
  std::unique_ptr<ApplicationConfiguration> got = DefaultConfig("<bytes>");
  AddStorageToConfig(got.get(), "localhost:8888");
  std::unique_ptr<ApplicationConfiguration> want =
      ConfigFrom("oak/common/testdata/storagenode.textproto");
  ASSERT_EQ(want->DebugString(), got->DebugString());
  ASSERT_EQ(true, ValidApplicationConfig(*got));
}

TEST_F(ApplicationConfigurationTest, DefaultPlusGrpcPort) {
  std::unique_ptr<ApplicationConfiguration> got = DefaultConfig("<bytes>");
  SetGrpcPortInConfig(got.get(), 8888);
  std::unique_ptr<ApplicationConfiguration> want =
      ConfigFrom("oak/common/testdata/grpcport.textproto");
  ASSERT_EQ(want->DebugString(), got->DebugString());
  ASSERT_EQ(true, ValidApplicationConfig(*got));
}

TEST_F(ApplicationConfigurationTest, InvalidGrpcPort) {
  std::unique_ptr<ApplicationConfiguration> config = DefaultConfig("<bytes>");
  SetGrpcPortInConfig(config.get(), 53);  // <= 1023 not allowed
  ASSERT_EQ(false, ValidApplicationConfig(*config));
}

TEST_F(ApplicationConfigurationTest, Valid) {
  auto config = ConfigFrom("oak/common/testdata/default.textproto");
  ASSERT_EQ(true, ValidApplicationConfig(*config));
}

TEST_F(ApplicationConfigurationTest, DuplicateConfigName) {
  auto config = ConfigFrom("oak/common/testdata/dup_config_name.textproto");
  ASSERT_EQ(false, ValidApplicationConfig(*config));
}

TEST_F(ApplicationConfigurationTest, MultipleLogNodes) {
  // Two log configs are OK.
  auto config = ConfigFrom("oak/common/testdata/two_log.textproto");
  ASSERT_EQ(true, ValidApplicationConfig(*config));
}

TEST_F(ApplicationConfigurationTest, NoWasmCode) {
  auto config = ConfigFrom("oak/common/testdata/missing_wasm.textproto");
  ASSERT_EQ(false, ValidApplicationConfig(*config));
}

TEST_F(ApplicationConfigurationTest, DuplicateWasmName) {
  auto config = ConfigFrom("oak/common/testdata/dup_wasm.textproto");
  ASSERT_EQ(false, ValidApplicationConfig(*config));
}

TEST_F(ApplicationConfigurationTest, EmptyWasmEntrypoint) {
  auto config = ConfigFrom("oak/common/testdata/no_wasm_main.textproto");
  ASSERT_EQ(false, ValidApplicationConfig(*config));
}

}  // namespace

}  // namespace oak
