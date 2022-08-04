/*
 * Copyright 2021 The Project Oak Authors
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

package com.google.oak.functions.android.client;

import static java.nio.charset.StandardCharsets.UTF_8;

import android.app.Activity;
import android.graphics.Color;
import android.os.Bundle;
import android.util.Log;
import android.widget.Button;
import android.widget.EditText;
import android.widget.TextView;
import com.google.common.base.VerifyException;
import com.google.oak.functions.client.AttestationClient;
import io.grpc.ManagedChannel;
import io.grpc.ManagedChannelBuilder;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;

/** Main class for the Oak Functions Client application. */
public class MainActivity extends Activity {
  private static final long CONNECTION_TIMEOUT_SECONDS = 5;

  /** Handles initial setup on creation of the activity. */
  @Override
  public void onCreate(Bundle savedInstanceState) {
    super.onCreate(savedInstanceState);

    Log.v("Oak", "Start application");
    setContentView(R.layout.activity_main);

    Button invokeButton = findViewById(R.id.invokeButton);
    invokeButton.setOnClickListener(v -> onClick());

    // Set default URI of the Oak Functions application.
    // https://pantheon.corp.google.com/run/detail/europe-west2/weather-lookup-endpoint/general?project=oak-ci
    EditText uriInput = findViewById(R.id.uriInput);
    uriInput.setText(R.string.service_uri);

    // Set default request payload.
    EditText requestInput = findViewById(R.id.requestInput);
    requestInput.setText(R.string.test_request);
  }

  /** Handles click events from the `invokeButton`. */
  public void onClick() {
    EditText uriInput = findViewById(R.id.uriInput);
    String uri = uriInput.getText().toString();

    EditText requestInput = findViewById(R.id.requestInput);
    byte[] request = requestInput.getText().toString().getBytes(UTF_8);

    TextView resultTextView = findViewById(R.id.resultTextView);
    try {
      // Create a gRPC channel.
      URL parsedUrl = new URL(uri);
      ManagedChannelBuilder builder =
          ManagedChannelBuilder.forAddress(parsedUrl.getHost(), parsedUrl.getPort()).usePlaintext();
      builder = AttestationClient.addApiKey(builder, getString(R.string.api_key));
      ManagedChannel channel = builder.build();

      // Attest a gRPC channel.
      AttestationClient client = new AttestationClient();
      client.attest(channel);

      // Send a request.
      AttestationClient.Response response = client.send(request);

      // Receive a response.
      AttestationClient.StatusCode responseStatus = response.getStatus();
      if (responseStatus != AttestationClient.StatusCode.SUCCESS) {
        throw new VerifyException(
            String.format("Couldn't receive response: %s", responseStatus.name()));
      }

      byte[] responseBody = Arrays.copyOfRange(response.getBody(), 0, (int) response.getLength());
      String decodedResponse = new String(responseBody, StandardCharsets.UTF_8);

      Log.v("Oak", "Received response: " + decodedResponse);
      resultTextView.setTextColor(Color.GREEN);
      resultTextView.setText(decodedResponse);
    } catch (Exception e) {
      if (e instanceof InterruptedException) {
        // Restore interrupted status.
        Thread.currentThread().interrupt();
      }
      Log.v("Oak", "Error: " + e);
      resultTextView.setTextColor(Color.RED);
      resultTextView.setText(e.toString());
    }
  }
}
