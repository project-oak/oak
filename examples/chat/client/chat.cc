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

#include <cstdlib>
#include <memory>
#include <string>
#include <thread>

#include "absl/base/thread_annotations.h"
#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/memory/memory.h"
#include "absl/strings/escaping.h"
#include "absl/synchronization/mutex.h"
#include "asylo/util/logging.h"
#include "examples/chat/proto/chat.grpc.pb.h"
#include "examples/chat/proto/chat.pb.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"
#include "oak/client/manager_client.h"
#include "oak/common/nonce_generator.h"
#include "oak/common/utils.h"

ABSL_FLAG(std::string, manager_address, "127.0.0.1:8888",
          "Address of the Oak Manager to connect to");
ABSL_FLAG(std::string, module, "", "File containing the compiled WebAssembly module");
ABSL_FLAG(std::string, app_address, "",
          "Address of the Oak Application to connect to (empty to create a new application)");
ABSL_FLAG(std::string, room_id, "",
          "Base64-encoded room ID to join (only used if room_name is blank)");
ABSL_FLAG(std::string, handle, "", "User handle to display");

// RoomId type holds binary data (non-UTF-8, may have embedded NULs).
using RoomId = std::string;

using ::oak::examples::chat::Chat;
using ::oak::examples::chat::CreateRoomRequest;
using ::oak::examples::chat::DestroyRoomRequest;
using ::oak::examples::chat::Message;
using ::oak::examples::chat::SendMessageRequest;
using ::oak::examples::chat::SubscribeRequest;

// Toy thread-safe class for (copyable) value types.
template <typename T>
class Safe {
 public:
  Safe(const T& val) : val_(val) {}
  T get() const LOCKS_EXCLUDED(mu_) {
    absl::ReaderMutexLock lock(&mu_);
    return T(val_);
  }
  void set(const T& val) LOCKS_EXCLUDED(mu_) {
    absl::MutexLock lock(&mu_);
    val_ = val;
  }

 private:
  mutable absl::Mutex mu_;  // protects val_
  T val_ GUARDED_BY(mu_);
};

void Prompt(const std::string& user_handle) { std::cout << user_handle << "> "; }

void ListenLoop(Chat::Stub* stub, const RoomId& room_id, const std::string& user_handle,
                std::shared_ptr<Safe<bool>> done) {
  grpc::ClientContext context;
  SubscribeRequest req;
  req.set_room_id(room_id);
  auto reader = stub->Subscribe(&context, req);
  if (reader == nullptr) {
    LOG(QFATAL) << "Could not call Subscribe";
  }
  Message msg;
  while (reader->Read(&msg)) {
    std::cout << msg.user_handle() << ": " << msg.text() << "\n";
    if (done->get()) {
      break;
    }
  }
  done->set(true);
  std::cout << "\n\nRoom " << room_id << " closed.\n\n";
}

void SendLoop(Chat::Stub* stub, const RoomId& room_id, const std::string& user_handle,
              std::shared_ptr<Safe<bool>> done) {
  // Re-use the same SendMessageRequest object for each message.
  SendMessageRequest req;
  req.set_room_id(room_id);

  Message* msg = req.mutable_message();
  msg->set_user_handle(user_handle);

  google::protobuf::Empty rsp;

  Prompt(user_handle);
  std::string text;
  while (std::getline(std::cin, text)) {
    if (done->get()) {
      break;
    }
    grpc::ClientContext context;
    msg->set_text(text);
    grpc::Status status = stub->SendMessage(&context, req, &rsp);
    if (!status.ok()) {
      LOG(WARNING) << "Could not SendMessage(): " << status.error_code() << ": "
                   << status.error_message();
      break;
    }
    Prompt(user_handle);
  }
  done->set(true);
  std::cout << "\n\nLeaving room " << room_id << ".\n\n";
}

void Chat(Chat::Stub* stub, const RoomId& room_id, const std::string& user_handle) {
  // TODO: make both loops notice immediately when done is true.
  auto done = std::make_shared<Safe<bool>>(false);

  // Start a separate thread for incoming messages.
  std::thread listener([stub, room_id, &user_handle, done] {
    LOG(INFO) << "New thread for incoming messages in room ID " << absl::Base64Escape(room_id);
    ListenLoop(stub, room_id, user_handle, done);
    LOG(INFO) << "Incoming message thread done";
  });
  listener.detach();

  std::cout << "\n\n\n";
  SendLoop(stub, room_id, user_handle, done);
}

// RAII class to handle creation/destruction of an Oak Application instance.
class OakApplication {
 public:
  // Caller should ensure that the manager_client outlives this object.
  OakApplication(oak::ManagerClient* manager_client, const std::string& module)
      : manager_client_(manager_client) {
    // Load the Oak Module to execute. This needs to be compiled from Rust to WebAssembly
    // separately.
    LOG(INFO) << "Creating application";
    std::string module_bytes = oak::utils::read_file(module);

    // Build an application configuration including logging.
    std::unique_ptr<oak::ApplicationConfiguration> config = oak::DefaultConfig(module_bytes);
    AddLoggingToConfig(config.get());

    std::unique_ptr<oak::CreateApplicationResponse> create_application_response =
        manager_client_->CreateApplication(std::move(config));
    if (create_application_response == nullptr) {
      LOG(QFATAL) << "Failed to create application";
    }

    application_id_ = create_application_response->application_id();
    std::stringstream ss;
    ss << "127.0.0.1:" << create_application_response->grpc_port();
    addr_ = ss.str();
  }

  ~OakApplication() {
    LOG(INFO) << "Terminating application id=" << application_id_;
    manager_client_->TerminateApplication(application_id_);
  }

  const std::string& Id() const { return application_id_; }
  const std::string& Addr() const { return addr_; }

 private:
  oak::ManagerClient* manager_client_;
  std::string application_id_;
  std::string addr_;
};

// RAII class to handle creation/destruction of a chat room.
class Room {
 public:
  // Caller should ensure stub outlives this object.
  Room(Chat::Stub* stub) : stub_(stub) {
    oak::NonceGenerator<64> generator;
    grpc::ClientContext context;
    CreateRoomRequest req;
    auto room_id = generator.NextNonce();
    auto room_id_string = std::string(room_id.begin(), room_id.end());
    req_.set_room_id(room_id_string);
    auto admin_token = generator.NextNonce();
    req_.set_admin_token(std::string(admin_token.begin(), admin_token.end()));
    google::protobuf::Empty rsp;
    grpc::Status status = stub_->CreateRoom(&context, req_, &rsp);
    if (!status.ok()) {
      LOG(QFATAL) << "Could not CreateRoom('" << absl::Base64Escape(room_id_string)
                  << "'): " << status.error_code() << ": " << status.error_message();
    }
  }
  ~Room() {
    LOG(INFO) << "Destroying room";
    grpc::ClientContext context;
    DestroyRoomRequest req;
    req.set_admin_token(req_.admin_token());
    google::protobuf::Empty rsp;
    grpc::Status status = stub_->DestroyRoom(&context, req, &rsp);
    if (!status.ok()) {
      LOG(WARNING) << "Could not DestroyRoom(): " << status.error_code() << ": "
                   << status.error_message();
    }
  }
  const RoomId& Id() const { return req_.room_id(); }

 private:
  Chat::Stub* stub_;
  CreateRoomRequest req_;
};

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  std::unique_ptr<oak::ManagerClient> manager_client;
  std::string addr = absl::GetFlag(FLAGS_app_address);
  std::string application_id;
  std::unique_ptr<OakApplication> application;

  if (addr.empty()) {
    // Connect to the Oak Manager and create the Oak Application.
    manager_client = absl::make_unique<oak::ManagerClient>(grpc::CreateChannel(
        absl::GetFlag(FLAGS_manager_address), grpc::InsecureChannelCredentials()));
    application =
        absl::make_unique<OakApplication>(manager_client.get(), absl::GetFlag(FLAGS_module));
    application_id = application->Id();
    addr = application->Addr();
    LOG(INFO) << "Connecting to new Oak Application id=" << application_id << " at " << addr;
  } else {
    LOG(INFO) << "Connecting to existing Oak Application at " << addr;
  }

  // Connect to the Oak Application.
  oak::ApplicationClient::InitializeAssertionAuthorities();
  auto stub = Chat::NewStub(oak::ApplicationClient::CreateChannel(addr));
  if (stub == nullptr) {
    LOG(QFATAL) << "Failed to create application stub";
  }

  RoomId room_id;
  if (!absl::Base64Unescape(absl::GetFlag(FLAGS_room_id), &room_id)) {
    LOG(QFATAL) << "Failed to parse --room_id as base 64";
  }
  std::unique_ptr<Room> room;
  if (room_id.empty()) {
    room = absl::make_unique<Room>(stub.get());
    room_id = room->Id();
    LOG(INFO) << "Join this room with --app_address=" << addr
              << " --room_id=" << absl::Base64Escape(room_id);
  }

  // Calculate a user handle.
  std::string user_handle = absl::GetFlag(FLAGS_handle);
  if (user_handle.empty()) {
    user_handle = std::getenv("USER");
  }
  if (user_handle.empty()) {
    user_handle = "<anonymous>";
  }

  // Main chat loop.
  Chat(stub.get(), room_id, user_handle);

  return EXIT_SUCCESS;
}
