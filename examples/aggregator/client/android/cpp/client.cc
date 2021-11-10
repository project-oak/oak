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

#include <android/log.h>
#include <jni.h>

#include "examples/aggregator/proto/aggregator.grpc.pb.h"
#include "examples/aggregator/proto/aggregator.pb.h"
#include "include/grpcpp/grpcpp.h"
#include "oak/client/application_client.h"

extern "C" {

#define APPNAME "Oak JNI"
#define JNI_LOG(ARGS...) __android_log_print(ANDROID_LOG_INFO, APPNAME, ARGS);

using ::oak::examples::aggregator::Aggregator;
using ::oak::examples::aggregator::Sample;

// Global channel storage.
std::unique_ptr<Aggregator::Stub> kChannel;

// JNI initialization function.
JNIEXPORT jint JNI_OnLoad(JavaVM* vm, void* reserved) {
  JNI_LOG("gRPC channel has been created");
  return JNI_VERSION_1_6;
}

// Create gRPC channel to the `jaddress`.
JNIEXPORT void JNICALL Java_com_google_oak_aggregator_MainActivity_createChannel(JNIEnv* env,
                                                                                 jobject /*this*/,
                                                                                 jstring jaddress,
                                                                                 jstring jca_cert) {
  auto address = env->GetStringUTFChars(jaddress, 0);
  auto ca_cert = env->GetStringUTFChars(jca_cert, 0);
  // Label corresponding to the hash of the WebAssembly module that implements the aggregator logic.
  //
  // The intention is that only such module will be able to declassify the data sent over gRPC.
  // When a new version of the aggregator module is "released", this value needs to be changed to
  // reflect the hash of the new module.
  //
  // The particular value corresponds to the hash on the `aggregator.wasm` line in
  // https://github.com/project-oak/oak/blob/hashes/reproducibility_index.
  oak::label::Label label = oak::WebAssemblyModuleHashLabel(
      absl::HexStringToBytes("e3122754992a7c2de11f315e7af86a07a10899393787d91daeaffe7b8b5a74d1"));
  kChannel = Aggregator::NewStub(oak::ApplicationClient::CreateChannel(
      address, oak::ApplicationClient::GetTlsChannelCredentials(ca_cert), label));
  JNI_LOG("gRPC channel has been created");
}

// Send data sample to the gRPC channel `kChannel`.
JNIEXPORT jboolean JNICALL Java_com_google_oak_aggregator_MainActivity_submitSample(
    JNIEnv* env, jobject /*this*/, jstring jbucket, jobject jindices, jobject jvalues) {
  // Get Java classes and methods.
  jclass ArrayListClass = env->FindClass("java/util/ArrayList");
  jmethodID GetMethod = env->GetMethodID(ArrayListClass, "get", "(I)Ljava/lang/Object;");
  jmethodID SizeMethod = env->GetMethodID(ArrayListClass, "size", "()I");

  jclass IntegerClass = env->FindClass("java/lang/Integer");
  jmethodID IntValueMethod = env->GetMethodID(IntegerClass, "intValue", "()I");

  jclass FloatClass = env->FindClass("java/lang/Float");
  jmethodID FloatValueMethod = env->GetMethodID(FloatClass, "floatValue", "()F");

  // Create a gRPC message.
  grpc::ClientContext context;
  JNI_LOG("Submitting sample:");
  Sample request;
  google::protobuf::Empty response;

  // Get Bucket ID.
  auto bucket = env->GetStringUTFChars(jbucket, 0);
  JNI_LOG("  bucket: %s", bucket);
  request.set_bucket(bucket);

  // Get indices.
  JNI_LOG("  indices:");
  size_t indices_size = static_cast<size_t>(env->CallIntMethod(jindices, SizeMethod));
  for (size_t index_key = 0; index_key < indices_size; index_key++) {
    jobject jindex = env->CallObjectMethod(jindices, GetMethod, index_key);
    int index = env->CallIntMethod(jindex, IntValueMethod);
    JNI_LOG("    - %d", index);
    request.mutable_data()->add_indices(index);
    env->DeleteLocalRef(jindex);
  }

  // Get values
  JNI_LOG("  values:");
  size_t values_size = static_cast<size_t>(env->CallIntMethod(jvalues, SizeMethod));
  for (size_t value_key = 0; value_key < values_size; value_key++) {
    jobject jvalue = env->CallObjectMethod(jvalues, GetMethod, value_key);
    float value = env->CallFloatMethod(jvalue, FloatValueMethod);
    JNI_LOG("    - %.2f", value);
    request.mutable_data()->add_values(value);
    env->DeleteLocalRef(jvalue);
  }

  // Clear class references.
  env->DeleteLocalRef(ArrayListClass);
  env->DeleteLocalRef(IntegerClass);
  env->DeleteLocalRef(FloatClass);

  // Submit sample.
  grpc::Status status = kChannel->SubmitSample(&context, request, &response);
  if (status.ok()) {
    JNI_LOG("Sample has been submitted");
    return true;
  } else {
    JNI_LOG("Could not submit sample: %d : %s", status.error_code(),
            status.error_message().c_str());
    return false;
  }
}

}  // extern "C"
