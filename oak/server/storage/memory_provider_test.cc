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

#include "oak/server/storage/memory_provider.h"

#include <memory>

#include "absl/memory/memory.h"
#include "gtest/gtest.h"

namespace oak {

// Test fixture that pre-populates a MemoryProvider with:
//  "test-00" : { "key0" => "value0", "key1" => "value1" }
class PopulatedMemoryProvider : public ::testing::Test {
 protected:
  void SetUp() override {
    StorageWriteRequest req;
    req.set_storage_id("test-00");
    StorageWriteResponse rsp;
    req.set_datum_name("key0");
    req.set_datum_value("value0");
    EXPECT_TRUE(mem_.Write(&req, &rsp).ok());
    req.set_datum_name("key1");
    req.set_datum_value("value1");
    EXPECT_TRUE(mem_.Write(&req, &rsp).ok());
  }

  MemoryProvider mem_;
};

TEST(MemoryStorage, ReadStorageIDAbsent) {
  MemoryProvider mem;
  StorageReadRequest req;
  req.set_storage_id("absent");
  req.set_datum_name("key0");
  StorageReadResponse rsp;
  grpc::Status status = mem.Read(&req, &rsp);
  ASSERT_EQ(grpc::StatusCode::NOT_FOUND, status.error_code());
}

TEST_F(PopulatedMemoryProvider, ReadKeyAbsent) {
  StorageReadRequest req;
  req.set_storage_id("test-00");
  req.set_datum_name("key2");
  StorageReadResponse rsp;
  grpc::Status status = mem_.Read(&req, &rsp);
  ASSERT_EQ(grpc::StatusCode::NOT_FOUND, status.error_code());
}

TEST_F(PopulatedMemoryProvider, ReadOK) {
  StorageReadRequest req;
  req.set_storage_id("test-00");
  req.set_datum_name("key0");
  StorageReadResponse rsp;
  EXPECT_TRUE(mem_.Read(&req, &rsp).ok());
  EXPECT_EQ("value0", rsp.datum_value());
}

TEST_F(PopulatedMemoryProvider, DeleteOK) {
  {
    StorageDeleteRequest req;
    req.set_storage_id("test-00");
    req.set_datum_name("key0");
    StorageDeleteResponse rsp;
    EXPECT_TRUE(mem_.Delete(&req, &rsp).ok());
  }
  {
    StorageReadRequest req;
    req.set_storage_id("test-00");
    req.set_datum_name("key0");
    StorageReadResponse rsp;
    grpc::Status status = mem_.Read(&req, &rsp);
    ASSERT_EQ(grpc::StatusCode::NOT_FOUND, status.error_code());
  }
}

TEST_F(PopulatedMemoryProvider, DeleteStorageIDAbsent) {
  StorageDeleteRequest req;
  req.set_storage_id("test-99");
  req.set_datum_name("key0");
  StorageDeleteResponse rsp;
  grpc::Status status = mem_.Delete(&req, &rsp);
  ASSERT_EQ(grpc::StatusCode::NOT_FOUND, status.error_code());
}

TEST_F(PopulatedMemoryProvider, WriteThenRead) {
  {
    StorageWriteRequest req;
    req.set_storage_id("test-00");
    StorageWriteResponse rsp;
    req.set_datum_name("key7");
    req.set_datum_value("value7");
    EXPECT_TRUE(mem_.Write(&req, &rsp).ok());
  }
  {
    StorageReadRequest req;
    req.set_storage_id("test-00");
    req.set_datum_name("key7");
    StorageReadResponse rsp;
    EXPECT_TRUE(mem_.Read(&req, &rsp).ok());
    EXPECT_EQ("value7", rsp.datum_value());
  }
}

TEST_F(PopulatedMemoryProvider, WriteThenReadNewStorageID) {
  {
    StorageWriteRequest req;
    req.set_storage_id("test-01");
    StorageWriteResponse rsp;
    req.set_datum_name("key7");
    req.set_datum_value("value7");
    EXPECT_TRUE(mem_.Write(&req, &rsp).ok());
  }
  {
    StorageReadRequest req;
    req.set_storage_id("test-01");
    req.set_datum_name("key7");
    StorageReadResponse rsp;
    EXPECT_TRUE(mem_.Read(&req, &rsp).ok());
    EXPECT_EQ("value7", rsp.datum_value());
  }
}

TEST(MemoryStorage, TransactionBeginUnimplemented) {
  std::unique_ptr<MemoryProvider> mem = absl::make_unique<MemoryProvider>();
  StorageBeginRequest req;
  req.set_storage_id("storage_id_0");
  StorageBeginResponse rsp;
  grpc::Status status = mem->Begin(&req, &rsp);
  ASSERT_EQ(grpc::StatusCode::UNIMPLEMENTED, status.error_code());
}

TEST(MemoryStorage, TransactionRollbackUnimplemented) {
  std::unique_ptr<MemoryProvider> mem = absl::make_unique<MemoryProvider>();
  StorageRollbackRequest req;
  req.set_storage_id("storage_id_0");
  StorageRollbackResponse rsp;
  grpc::Status status = mem->Rollback(&req, &rsp);
  ASSERT_EQ(grpc::StatusCode::UNIMPLEMENTED, status.error_code());
}

TEST(MemoryStorage, TransactionCommitUnimplemented) {
  std::unique_ptr<MemoryProvider> mem = absl::make_unique<MemoryProvider>();
  StorageCommitRequest req;
  req.set_storage_id("storage_id_0");
  StorageCommitResponse rsp;
  grpc::Status status = mem->Commit(&req, &rsp);
  ASSERT_EQ(grpc::StatusCode::UNIMPLEMENTED, status.error_code());
}

}  // namespace oak
