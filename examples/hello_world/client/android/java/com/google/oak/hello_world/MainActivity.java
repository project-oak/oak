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

package com.google.oak.hello_world;

import android.app.Activity;
import android.os.Bundle;
import android.util.Log;
import android.widget.Button;
import android.widget.TextView;
import android.widget.EditText;

import com.google.oak.hello_world.R;

/*
 * Main class for the Oak Android "Hello, World" app.
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
    
    Button helloButton = findViewById(R.id.helloButton);
    helloButton.setOnClickListener(v -> onClick());

    // Set default address.
    // Android emulator forwards `10.0.2.2` to the host machine.
    EditText addressInput = findViewById(R.id.addressInput);
    addressInput.setText("10.0.2.2:8888");
  }

  @Override
  public void onDestroy() {
    super.onDestroy();
  }

  public void onClick() {
    EditText addressInput = findViewById(R.id.addressInput);
    String address = addressInput.getText().toString();

    if (address != rpcAddress) {
      Log.v("Oak", "Create channel to: " + address);
      createChannel(address);
      rpcAddress = address;
    }

    Log.v("Oak", "Say Hello");
    TextView helloTextView = findViewById(R.id.helloTextView);
    String responce = sayHello("World");
    Log.v("Oak", "Responce is: " + responce);
    helloTextView.setText(responce);
  }

  private native void createChannel(String address);
  private native String sayHello(String name);

  private String rpcAddress;
}
