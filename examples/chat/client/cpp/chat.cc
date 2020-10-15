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
// TODO: Replace this bearer token mechanism with a public / private key pair.
ABSL_FLAG(std::string, room_access_token, "", "Base64-encoded room access token to join");
ABSL_FLAG(std::string, handle, "", "User handle to display");
ABSL_FLAG(std::string, ca_cert, "", "Path to the PEM-encoded CA root certificate");

// RoomToken type holds binary data (non-UTF-8, may have embedded NULs).
using RoomToken = std::string;

using ::oak::examples::chat::Chat;
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

// The current chat room is implicitly encoded as part of the gRPC stub.
void ListenLoop(Chat::Stub* stub, const std::string& user_handle,
                std::shared_ptr<Safe<bool>> done) {
  grpc::ClientContext context;
  SubscribeRequest req;
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
  std::cout << "\n\nRoom closed.\n\n";
}

// The current chat room is implicitly encoded as part of the gRPC stub.
void SendLoop(Chat::Stub* stub, const std::string& user_handle, std::shared_ptr<Safe<bool>> done) {
  // Re-use the same SendMessageRequest object for each message.
  SendMessageRequest req;

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
      LOG(WARNING) << "Could not SendMessage(): " << oak::status_code_to_string(status.error_code())
                   << ": " << status.error_message();
      break;
    }
    Prompt(user_handle);
  }
  done->set(true);
  std::cout << "\n\nLeaving room.\n\n";
}

// The current chat room is implicitly encoded as part of the gRPC stub.
void Chat(Chat::Stub* stub, const std::string& user_handle) {
  // TODO(#746): make both loops notice immediately when done is true.
  auto done = std::make_shared<Safe<bool>>(false);

  // Start a separate thread for incoming messages.
  std::thread listener([stub, &user_handle, done] {
    LOG(INFO) << "New thread for incoming messages in room";
    ListenLoop(stub, user_handle, done);
    LOG(INFO) << "Incoming message thread done";
  });
  listener.detach();

  std::cout << "\n\n\n";
  SendLoop(stub, user_handle, done);
}

// Create a gRPC stub for an application, with the provided room access token, which will be used as
// confidentiality label for any messages sent, and also to authenticate to the application in order
// to read messages sent by other clients.
std::unique_ptr<Chat::Stub> create_stub(std::string address, std::string ca_cert,
                                        std::string room_access_token) {
  auto call_credentials =
      oak::ApplicationClient::authorization_bearer_token_call_credentials(room_access_token);
  // Connect to the Oak Application.
  auto stub = Chat::NewStub(oak::ApplicationClient::CreateChannel(
      address, oak::ApplicationClient::GetTlsChannelCredentials(ca_cert), call_credentials));
  if (stub == nullptr) {
    LOG(FATAL) << "Failed to create application stub";
  }
  return stub;
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  std::string address = absl::GetFlag(FLAGS_address);
  std::string ca_cert = oak::ApplicationClient::LoadRootCert(absl::GetFlag(FLAGS_ca_cert));
  LOG(INFO) << "Connecting to Oak Application: " << address;

  RoomToken room_access_token;
  if (!absl::Base64Unescape(absl::GetFlag(FLAGS_room_access_token), &room_access_token)) {
    LOG(FATAL) << "Failed to parse --room_access_token as base64";
  }

  std::unique_ptr<Chat::Stub> stub;

  // If no room access token was provided, create a new `Room` object, which internally generates a
  // fresh room access token, creates a gRPC stub based on it, and makes this stub available to the
  // rest of this method.
  //
  // If a room access token was provided, directly create a gRPC stub with it.
  if (room_access_token.empty()) {
    oak::NonceGenerator<64> generator;
    auto room_access_token_bytes = generator.NextNonce();
    room_access_token = std::string(room_access_token_bytes.begin(), room_access_token_bytes.end());
    LOG(INFO) << "Join this room with --address=" << address
              << " --room_access_token=" << absl::Base64Escape(room_access_token);
  }

  stub = create_stub(address, ca_cert, room_access_token);

  if (absl::GetFlag(FLAGS_test)) {
    // Disable interactive behaviour, and just attempt to send a pre-defined message.

    SendMessageRequest req;
    Message* msg = req.mutable_message();
    msg->set_user_handle("test user");
    msg->set_text("test message");

    google::protobuf::Empty rsp;

    grpc::ClientContext context;
    grpc::Status status = stub->SendMessage(&context, req, &rsp);
    if (!status.ok()) {
      LOG(FATAL) << "Could not SendMessage(): " << oak::status_code_to_string(status.error_code())
                 << ": " << status.error_message();
    }

    return EXIT_SUCCESS;
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
  // The current chat room is implicitly encoded as part of the gRPC stub created earlier.
  Chat(stub.get(), user_handle);

  return EXIT_SUCCESS;
}
