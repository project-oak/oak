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

package com.google.oak.aggregator;

import android.app.Activity;
import android.os.Bundle;
import android.util.Log;
import android.widget.Button;
import android.widget.EditText;
import android.widget.TextView;
import com.google.oak.aggregator.R;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Optional;
import java.util.stream.Collectors;

/** Main class for the Oak Android "Aggregator" application. */
public class MainActivity extends Activity {
  static {
    // Load native library.
    System.loadLibrary("client_app");
  }

  /** Handles initial setup on creation of the activity. */
  @Override
  public void onCreate(Bundle savedInstanceState) {
    super.onCreate(savedInstanceState);

    Log.v("Oak", "Start application");
    setContentView(R.layout.activity_main);

    Button submitButton = findViewById(R.id.submitButton);
    submitButton.setOnClickListener(v -> onClick());

    // Set default values.
    EditText bucketInput = findViewById(R.id.bucketInput);
    bucketInput.setText("android-test");

    EditText firstKeyInput = findViewById(R.id.firstKeyInput);
    firstKeyInput.setText("1");
    EditText firstValueInput = findViewById(R.id.firstValueInput);
    firstValueInput.setText("10");

    EditText secondKeyInput = findViewById(R.id.secondKeyInput);
    secondKeyInput.setText("2");
    EditText secondValueInput = findViewById(R.id.secondValueInput);
    secondValueInput.setText("20");

    EditText thirdKeyInput = findViewById(R.id.thirdKeyInput);
    thirdKeyInput.setText("3");
    EditText thirdValueInput = findViewById(R.id.thirdValueInput);
    thirdValueInput.setText("30");

    // Set default address (static IP of the Aggregator in Google Cloud).
    // https://developer.android.com/studio/run/emulator-networking
    EditText addressInput = findViewById(R.id.addressInput);
    // IP address was reserved on Google Cloud:
    // https://pantheon.corp.google.com/networking/addresses/list?project=oak-ci
    addressInput.setText("35.246.87.178:8080");
  }

  /** Handles click events from the submitButton. */
  public void onClick() {
    EditText addressInput = findViewById(R.id.addressInput);
    String address = addressInput.getText().toString();

    if (!address.equals(rpcAddress)) {
      Optional<String> caCert = getCaCertificate();
      if (!caCert.isPresent()) {
        // TODO(#991): Notify user of failure.
        return;
      }
      Log.v("Oak", "Create channel to: " + address);
      createChannel(address, caCert.get());
      rpcAddress = address;
    }

    Log.v("Oak", "Submit Sample");

    EditText bucketInput = findViewById(R.id.bucketInput);
    String bucket = bucketInput.getText().toString();

    ArrayList<Integer> indices = new ArrayList<Integer>();
    ArrayList<Float> values = new ArrayList<Float>();

    EditText firstKeyInput = findViewById(R.id.firstKeyInput);
    indices.add(Integer.parseInt(firstKeyInput.getText().toString()));
    EditText firstValueInput = findViewById(R.id.firstValueInput);
    values.add(Float.parseFloat(firstValueInput.getText().toString()));

    EditText secondKeyInput = findViewById(R.id.secondKeyInput);
    indices.add(Integer.parseInt(secondKeyInput.getText().toString()));
    EditText secondValueInput = findViewById(R.id.secondValueInput);
    values.add(Float.parseFloat(secondValueInput.getText().toString()));

    EditText thirdKeyInput = findViewById(R.id.thirdKeyInput);
    indices.add(Integer.parseInt(thirdKeyInput.getText().toString()));
    EditText thirdValueInput = findViewById(R.id.thirdValueInput);
    values.add(Float.parseFloat(thirdValueInput.getText().toString()));

    // TODO(#988): Move blocking call out of UI thread.
    submitSample(bucket, indices, values);
  }

  /** Gets the custom CA certificate from the assets folder. */
  private Optional<String> getCaCertificate() {
    try {
      return Optional.of(new BufferedReader(new InputStreamReader(getAssets().open("ca.pem")))
                             .lines()
                             .collect(Collectors.joining("\n")));
    } catch (Exception exception) {
      Log.w("Oak", "getCaCertificate", exception);
      return Optional.empty();
    }
  }

  private native void createChannel(String address, String caCert);
  private native void submitSample(
      String bucket, ArrayList<Integer> indices, ArrayList<Float> values);

  private String rpcAddress;
}
