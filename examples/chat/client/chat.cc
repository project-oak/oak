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

#include <thread>

#include "absl/base/thread_annotations.h"
#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/synchronization/mutex.h"
#include "examples/chat/proto/chat.grpc.pb.h"
#include "examples/chat/proto/chat.pb.h"
#include "glog/logging.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"
#include "oak/common/nonce_generator.h"

ABSL_FLAG(bool, test, false, "Run a non-interactive version of chat application for testing");
ABSL_FLAG(std::string, address, "localhost:8080", "Address of the Oak application to connect to");
ABSL_FLAG(std::string, room_id, "",
          "Base64-encoded room ID to join (only used if room_name is blank)");
ABSL_FLAG(std::string, handle, "", "User handle to display");
ABSL_FLAG(std::string, ca_cert, "", "Path to the PEM-encoded CA root certificate");

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
    LOG(FATAL) << "Could not call Subscribe";
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
  // TODO(#746): make both loops notice immediately when done is true.
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
      LOG(FATAL) << "Could not CreateRoom('" << absl::Base64Escape(room_id_string)
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

  std::string address = absl::GetFlag(FLAGS_address);
  std::string ca_cert = oak::ApplicationClient::LoadRootCert(absl::GetFlag(FLAGS_ca_cert));
  LOG(INFO) << "Connecting to Oak Application: " << address;

  // TODO(#488): Use the token provided on command line for authorization and labelling of data.
  oak::label::Label label = oak::PublicUntrustedLabel();
  // Connect to the Oak Application.
  auto stub = Chat::NewStub(oak::ApplicationClient::CreateChannel(
      address, oak::ApplicationClient::GetTlsChannelCredentials(ca_cert), label));
  if (stub == nullptr) {
    LOG(FATAL) << "Failed to create application stub";
  }

  if (absl::GetFlag(FLAGS_test)) {
    // Disable interactive behaviour.
    return EXIT_SUCCESS;
  }

  RoomId room_id;
  if (!absl::Base64Unescape(absl::GetFlag(FLAGS_room_id), &room_id)) {
    LOG(FATAL) << "Failed to parse --room_id as base 64";
  }
  std::unique_ptr<Room> room;
  if (room_id.empty()) {
    room = absl::make_unique<Room>(stub.get());
    room_id = room->Id();
    LOG(INFO) << "Join this room with --address=" << address
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
