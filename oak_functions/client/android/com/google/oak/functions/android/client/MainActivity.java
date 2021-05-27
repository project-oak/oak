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

import android.app.Activity;
import android.content.Context;
import android.graphics.Color;
import android.os.Bundle;
import android.os.Handler;
import android.os.HandlerThread;
import android.util.Log;
import android.widget.Button;
import android.widget.EditText;
import android.widget.TextView;
import com.google.oak.functions.android.client.R;
import com.google.oak.functions.client.AttestationClient;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.lang.Runnable;
import java.lang.ref.WeakReference;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Optional;
import java.util.stream.Collectors;

/** Main class for the Oak Functions Client application. */
public class MainActivity extends Activity {
  private HandlerThread backgroundHandlerThread;
  private Handler backgroundHandler;
  private String rpcAddress;

  /** Handles initial setup on creation of the activity. */
  @Override
  public void onCreate(Bundle savedInstanceState) {
    super.onCreate(savedInstanceState);

    Log.v("Oak", "Start application");
    setContentView(R.layout.activity_main);

    HandlerThread backgroundHandlerThread = new HandlerThread("Background");
    backgroundHandlerThread.start();
    backgroundHandler = new Handler(backgroundHandlerThread.getLooper());

    Button invokeButton = findViewById(R.id.invokeButton);
    invokeButton.setOnClickListener(v -> onClick());

    // Set default URI of a Cloud Run application:
    // https://pantheon.corp.google.com/run/detail/europe-west2/oak-functions-weather-lookup/metrics?project=oak-ci
    EditText uriInput = findViewById(R.id.uriInput);
    uriInput.setText("oak-functions-weather-lookup-62sa4xcfia-nw.a.run.app:443");

    // Set default request payload.
    EditText requestInput = findViewById(R.id.requestInput);
    requestInput.setText("{\"lat\":52,\"lon\":0}");
  }

  @Override
  public void onDestroy() {
    backgroundHandlerThread.quit();
    super.onDestroy();
  }

  /** Handles click events from the `invokeButton`. */
  public void onClick() {
    EditText uriInput = findViewById(R.id.uriInput);
    String uri = uriInput.getText().toString();

    EditText requestInput = findViewById(R.id.requestInput);
    String request = requestInput.getText().toString();

    TextView resultTextView = findViewById(R.id.resultTextView);
    try {
      AttestationClient client = new AttestationClient(uri);
      byte[] response = client.Send(request.getBytes());
      String decodedResponse = new String(response, StandardCharsets.UTF_8);

      Log.v("Oak", "Received response: " + decodedResponse);
      resultTextView.setTextColor(Color.GREEN);
      resultTextView.setText(decodedResponse);
    } catch (Exception e) {
      Log.v("Oak", "Error: " + e);
      resultTextView.setTextColor(Color.RED);
      resultTextView.setText(e.toString());
      return;
    }
  }
}
