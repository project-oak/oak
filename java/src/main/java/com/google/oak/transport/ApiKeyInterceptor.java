//
// Copyright 2022 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

package com.google.oak.transport;

import io.grpc.CallOptions;
import io.grpc.Channel;
import io.grpc.ClientCall;
import io.grpc.ClientInterceptor;
import io.grpc.ForwardingClientCall;
import io.grpc.Metadata;
import io.grpc.MethodDescriptor;

/** gRPC client interceptor that adds an API key to each outgoing request. */
public class ApiKeyInterceptor implements ClientInterceptor {
  // HTTP/gRPC header for Google API keys.
  // https://cloud.google.com/apis/docs/system-parameters
  // https://cloud.google.com/docs/authentication/api-keys
  private static final String API_KEY_HEADER = "x-goog-api-key";

  private final String apiKey;

  private static final Metadata.Key<String> API_KEY_METADATA_HEADER =
      Metadata.Key.of(API_KEY_HEADER, Metadata.ASCII_STRING_MARSHALLER);

  public ApiKeyInterceptor(String apiKey) {
    this.apiKey = apiKey;
  }

  @Override
  public <ReqT, RespT> ClientCall<ReqT, RespT> interceptCall(
      MethodDescriptor<ReqT, RespT> method, CallOptions callOptions, Channel next) {
    ClientCall<ReqT, RespT> call = next.newCall(method, callOptions);

    call = new ForwardingClientCall.SimpleForwardingClientCall<ReqT, RespT>(call) {
      @Override
      public void start(Listener<RespT> responseListener, Metadata headers) {
        if (apiKey != null && !apiKey.isEmpty()) {
          headers.put(API_KEY_METADATA_HEADER, apiKey);
        }
        super.start(responseListener, headers);
      }
    };
    return call;
  }
}
