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
import android.content.Context;
import android.graphics.Color;
import android.os.Bundle;
import android.os.Handler;
import android.os.HandlerThread;
import android.util.Log;
import android.widget.Button;
import android.widget.EditText;
import android.widget.TextView;
import com.google.oak.aggregator.R;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.lang.Runnable;
import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.Optional;
import java.util.stream.Collectors;

/** Main class for the Oak Android "Aggregator" application. */
public class MainActivity extends Activity {
  private HandlerThread backgroundHandlerThread;
  private Handler backgroundHandler;
  private String rpcAddress;

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

    HandlerThread backgroundHandlerThread = new HandlerThread("Background");
    backgroundHandlerThread.start();
    backgroundHandler = new Handler(backgroundHandlerThread.getLooper());

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

  @Override
  public void onDestroy() {
    backgroundHandlerThread.quit();
    super.onDestroy();
  }

  /** Handles click events from the submitButton. */
  public void onClick() {
    EditText addressInput = findViewById(R.id.addressInput);
    String address = addressInput.getText().toString();

    EditText bucketInput = findViewById(R.id.bucketInput);
    String bucket = bucketInput.getText().toString();

    ArrayList<Integer> indices = new ArrayList<Integer>();
    ArrayList<Float> values = new ArrayList<Float>();

    TextView resultTextView = findViewById(R.id.resultTextView);
    resultTextView.setText("");
    
    try {
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
    } catch (NumberFormatException e) {
      resultTextView.setTextColor(Color.RED);
      resultTextView.setText("Invalid Data!");
      return;
    }

    boolean initializeChannel = !address.equals(rpcAddress);
    if (initializeChannel) {
      rpcAddress = address;
    }

    backgroundHandler.post(new AggregatorWorker(getApplicationContext(), address, initializeChannel,
        bucket, indices, values, resultTextView));
  }

  /** Worker to perform blocking tasks on the background HandlerThread. */
  private static class AggregatorWorker implements Runnable {
    private Context context;
    private String address;
    private boolean initializeChannel;
    private String bucket;
    ArrayList<Integer> indices;
    ArrayList<Float> values;
    private WeakReference<TextView> target;

    private AggregatorWorker(Context context, String address, boolean initializeChannel,
        String bucket, ArrayList<Integer> indices, ArrayList<Float> values, TextView target) {
      this.context = context;
      this.address = address;
      this.initializeChannel = initializeChannel;
      this.bucket = bucket;
      this.indices = indices;
      this.values = values;
      this.target = new WeakReference(target);
    }

    @Override
    public void run() {
      if (submitData()) {
        TextView resultTextView = target.get();
        if (resultTextView != null) {
          resultTextView.post(new Runnable() {
            @Override
            public void run() {
              resultTextView.setTextColor(Color.GREEN);
              resultTextView.setText("Success!");
            }
          });
        }
      } else {
        TextView resultTextView = target.get();
        if (resultTextView != null) {
          resultTextView.post(new Runnable() {
            @Override
            public void run() {
              resultTextView.setTextColor(Color.RED);
              resultTextView.setText("Unexpected Error!");
            }
          });
        }
      }
    }

    /** Submits the data using the native client and returns whether it succeeded. */
    private boolean submitData() {
      if (initializeChannel) {
        Optional<String> caCert = getCaCertificate();
        if (!caCert.isPresent()) {
          return false;
        }
        Log.v("Oak", "Create channel to: " + address);
        createChannel(address, caCert.get());
      }

      Log.v("Oak", "Submit Sample");
      return submitSample(bucket, indices, values);
    }

    /** Gets the custom CA certificate from the assets folder. */
    private Optional<String> getCaCertificate() {
      try {
        return Optional.of(
            new BufferedReader(new InputStreamReader(context.getAssets().open("ca.pem")))
                .lines()
                .collect(Collectors.joining("\n")));
      } catch (Exception exception) {
        Log.w("Oak", "getCaCertificate", exception);
        return Optional.empty();
      }
    }
  }

  private static native void createChannel(String address, String caCert);
  private static native boolean submitSample(
      String bucket, ArrayList<Integer> indices, ArrayList<Float> values);
}
