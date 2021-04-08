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

#include <openssl/evp.h>

#include <iomanip>
#include <thread>

#include "absl/base/thread_annotations.h"
#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/strings/escaping.h"
#include "absl/synchronization/mutex.h"
#include "examples/chat/proto/chat.grpc.pb.h"
#include "examples/chat/proto/chat.pb.h"
#include "glog/logging.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"
#include "oak_abi/proto/identity.pb.h"

ABSL_FLAG(bool, test, false, "Run a non-interactive version of chat application for testing");
ABSL_FLAG(std::string, address, "localhost:8080", "Address of the Oak application to connect to");
ABSL_FLAG(std::string, room_secret_path, "",
          "Path to a PEM file containing the private key for joining the room");
ABSL_FLAG(std::string, handle, "", "User handle to display");
ABSL_FLAG(std::string, ca_cert_path, "", "Path to the PEM-encoded CA root certificate");

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

// Print incoming messages sent to the chat room, authenticating with the room private key which is
// implicitly encoded as part of the gRPC stub.
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

// Wait for user input and send each message to the chat room, with the room public key label which
// is implicitly encoded as part of the gRPC stub.
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

// Create a gRPC stub for an application, with the provided signed challenge, which will be used for
// adding a confidentiality label to any messages sent, and also to authenticate to the application
// in order to read messages sent by other clients.
std::unique_ptr<Chat::Stub> create_stub(std::string address, std::string ca_cert_path,
                                        oak::identity::SignedChallenge signed_challenge) {
  oak::label::Label label = oak::PublicKeyIdentityLabel(signed_challenge.public_key());
  // Connect to the Oak Application.
  auto stub = Chat::NewStub(oak::ApplicationClient::CreatePrivateChannel(
      address, oak::ApplicationClient::GetTlsChannelCredentials(ca_cert_path), label,
      signed_challenge));
  if (stub == nullptr) {
    LOG(FATAL) << "Failed to create application stub";
  }
  return stub;
}

int main(int argc, char** argv) {
  absl::ParseCommandLine(argc, argv);

  std::string address = absl::GetFlag(FLAGS_address);
  std::string ca_cert_path =
      oak::ApplicationClient::LoadRootCert(absl::GetFlag(FLAGS_ca_cert_path));
  LOG(INFO) << "Connecting to Oak Application: " << address;

  std::string room_secret_path = absl::GetFlag(FLAGS_room_secret_path);
  std::unique_ptr<oak::KeyPair> key_pair;

  // TODO(#1905): A secure mechanism for sharing and retrieving the private key is needed. In the
  // meantime, we use `room_secret` to pass in a file containing the private key. If no room secret
  // is provided, we create a fresh private/public key pair, and store the private key in a file for
  // later use.
  if (room_secret_path.empty()) {
    key_pair = oak::KeyPair::Generate();
    oak::ApplicationClient::StoreKeyPair(key_pair, "chat-room.key");
  } else {
    key_pair = oak::ApplicationClient::LoadKeyPair(room_secret_path);
  }

  // Use the room's secret to sign the challenge required for authenticating the client.
  oak::identity::SignedChallenge signed_challenge =
      oak::ApplicationClient::SignChallenge(key_pair, oak::kOakChallenge);

  std::unique_ptr<Chat::Stub> stub;
  stub = create_stub(address, ca_cert_path, signed_challenge);

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
