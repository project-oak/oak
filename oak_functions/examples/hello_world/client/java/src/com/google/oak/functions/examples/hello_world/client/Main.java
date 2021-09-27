//
// Copyright 2021 The Project Oak Authors
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

package com.google.oak.functions.examples.hello_world.client;

import static java.nio.charset.StandardCharsets.UTF_8;

import com.google.oak.functions.client.AttestationClient;
import com.google.protobuf.ByteString;
import java.util.logging.Level;
import java.util.logging.Logger;
import oak.functions.invocation.Request;
import oak.functions.invocation.Response;

public class Main {
  private static Logger logger = Logger.getLogger(Main.class.getName());

  private static final String CLIENT_HELLO_WORLD = "Client Hello World";
  private static final String SERVER_HELLO_WORLD = "Server Hello World";

  public static void main(String[] args) throws Exception {
    AttestationClient client = new AttestationClient();
    client.attest("http://localhost:8080");

    byte[] requestBody = CLIENT_HELLO_WORLD.getBytes(UTF_8);
    Request request = Request.newBuilder().setBody(ByteString.copyFrom(requestBody)).build();
    Response response = client.send(request);
    ByteString responseBody = response.getBody().substring(0, (int) response.getLength());
    String decodedResponse = responseBody.toStringUtf8();

    if (decodedResponse.equals(SERVER_HELLO_WORLD)) {
      logger.log(Level.INFO, "Client received the expected response: " + decodedResponse);
    } else {
      logger.log(Level.INFO,
          String.format("Expected pattern %s, received %s.", SERVER_HELLO_WORLD, decodedResponse));
      System.exit(1);
    }
  }
}
