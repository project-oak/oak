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

package com.google.oak.functions.examples.weather_lookup.client;

import com.google.oak.functions.client.AttestationClient;
import com.google.protobuf.ByteString;
import oak.functions.invocation.Request;
import oak.functions.invocation.Response;
import java.nio.charset.StandardCharsets;
import java.util.logging.Level;
import java.util.logging.Logger;

public class Main {
    private static Logger logger = Logger.getLogger(Main.class.getName());
    private static final String EXPECTED_RESPONSE = "{\"temperature_degrees\":-10}";

    public static void main(String[] args) throws Exception {
        AttestationClient client = new AttestationClient("localhost:8080");

        byte[] requestBody = "{\"lat\":52,\"lon\":0}".getBytes();
        Request request = Request.newBuilder().setBody(ByteString.copyFrom(requestBody)).build();
        Response response = client.send(request);
        ByteString responseBody = response.getBody().substring(0, (int)response.getLength());
        String decodedResponse = responseBody.toStringUtf8();
        
        if (EXPECTED_RESPONSE.equals(decodedResponse)) {
            logger.log(Level.INFO, "Client received the expected response: " + decodedResponse);
        } else {
            logger.log(Level.INFO, String.format("Expected %s, received %s.", EXPECTED_RESPONSE, decodedResponse));
            System.exit(1);
        }
    }
}
