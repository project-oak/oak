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

import java.util.ArrayList;

import android.app.Activity;
import android.os.Bundle;
import android.util.Log;
import android.widget.Button;
import android.widget.EditText;
import android.widget.TextView;

import com.google.oak.aggregator.R;

/*
 * Main class for the Oak Android "Aggregator" application.
 */
public class MainActivity extends Activity {
  static {
    // Load native library.
    System.loadLibrary("client_app");
  }

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

  public void onClick() {
    EditText addressInput = findViewById(R.id.addressInput);
    String address = addressInput.getText().toString();

    if (!address.equals(rpcAddress)) {
      Log.v("Oak", "Create channel to: " + address);
      createChannel(address);
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

    submitSample(bucket, indices, values);
  }

  // TODO(#717): Use Java version of gRPC without invoking JNI.
  private native void createChannel(String address);
  private native void submitSample(
      String bucket, ArrayList<Integer> indices, ArrayList<Float> values);

  private String rpcAddress;
}
