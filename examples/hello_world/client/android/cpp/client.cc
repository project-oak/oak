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

#include <jni.h>
#include <string>

#include "asylo/util/logging.h"
#include "examples/hello_world/proto/hello_world.grpc.pb.h"
#include "examples/hello_world/proto/hello_world.pb.h"
#include "examples/utils/utils.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"
#include "oak/client/manager_client.h"

extern "C"
//JNIEXPORT jobject
//JNIEXPORT jstring
//JNIEXPORT jint

using ::oak::examples::hello_world::HelloRequest;
using ::oak::examples::hello_world::HelloResponse;
using ::oak::examples::hello_world::HelloWorld;

// Global channel storage.
std::unordered_map<jint, HelloWorld::Stub*> CHANNEL_MAP;

jint Java_com_google_oak_hello_world_MainActivity_createChannel(
    JNIEnv* env, jobject /* this */, jstring jaddress) {
  jint channel_handle;
  
  auto address = env->GetStringUTFChars(jaddress, 0);
  auto channel = HelloWorld::NewStub(
      oak::ApplicationClient::CreateChannel(address));

  return channel_handle;
}

jstring Java_com_google_oak_hello_world_MainActivity_sayHello(
    JNIEnv* env, jobject /* this */, jint handle, jstring jname) {
  auto it = CHANNEL_MAP.find(handle);
  if (it != CHANNEL_MAP.end()) {
    auto channel = it->second;
    auto name = env->GetStringUTFChars(jname, 0);

    grpc::ClientContext context;
    HelloRequest request;
    HelloResponse response;
    request.set_greeting(name);
    grpc::Status status = channel->SayHello(&context, request, &response);
    if (!status.ok()) {
      std::stringstream warning;
      warning << "Warning: Could not call SayHello('" << name << "'): "
              << status.error_code() << ": " << status.error_message();
      return env->NewStringUTF(warning.str().c_str());
    }
    return env->NewStringUTF(response.reply().c_str());
  }
  else {
    return env->NewStringUTF("Error: Wrong channel handle");
  }
}
