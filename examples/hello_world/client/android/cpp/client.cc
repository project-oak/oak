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

#include <android/log.h>
#include <jni.h>
#include <string>

#include "examples/hello_world/proto/hello_world.grpc.pb.h"
#include "examples/hello_world/proto/hello_world.pb.h"
#include "examples/utils/utils.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"
#include "oak/client/manager_client.h"

extern "C" {

#define APPNAME "Oak JNI"
#define JNI_LOG(MSG) __android_log_print(ANDROID_LOG_INFO, APPNAME, MSG);

using ::oak::examples::hello_world::HelloRequest;
using ::oak::examples::hello_world::HelloResponse;
using ::oak::examples::hello_world::HelloWorld;

// Global channel storage.
std::unique_ptr<HelloWorld::Stub> kChannel;

// JNI initialization function.
JNIEXPORT jint JNI_OnLoad(JavaVM* vm, void* reserved) {
  JNI_LOG("gRPC channel has been created");
  return JNI_VERSION_1_6;
}

// Create gRPC channel to the `jaddress`.
// Underscores in Java packages should be followed by `1`.
// https://stackoverflow.com/questions/16069209/invoking-jni-functions-in-android-package-name-containing-underscore
JNIEXPORT void JNICALL Java_com_google_oak_hello_1world_MainActivity_createChannel(
    JNIEnv* env, jobject /*this*/, jstring jaddress) {
  oak::ApplicationClient::InitializeAssertionAuthorities();

  auto address = env->GetStringUTFChars(jaddress, 0);
  kChannel = HelloWorld::NewStub(oak::ApplicationClient::CreateChannel(address));
  JNI_LOG("gRPC channel has been created");
}

// Send `jname` message to the gRPC channel `kChannel`.
JNIEXPORT jstring JNICALL Java_com_google_oak_hello_1world_MainActivity_sayHello(JNIEnv* env,
                                                                                 jobject /*this*/,
                                                                                 jstring jname) {
  grpc::ClientContext context;
  HelloRequest request;
  HelloResponse response;

  auto name = env->GetStringUTFChars(jname, 0);
  request.set_greeting(name);
  grpc::Status status = kChannel->SayHello(&context, request, &response);
  JNI_LOG("Hello message has been sent");
  if (!status.ok()) {
    std::stringstream warning;
    warning << "Warning: Could not call SayHello('" << name << "'): " << status.error_code() << ": "
            << status.error_message();
    return env->NewStringUTF(warning.str().c_str());
  }
  return env->NewStringUTF(response.reply().c_str());
}

}  // extern "C"
