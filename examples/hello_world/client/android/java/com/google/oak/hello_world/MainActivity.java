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

import com.google.oak.hello_world.R;

/*
 * Main class for the Oak Android "Hello, World" app.
 */
public class MainActivity extends Activity {
  @Override
  public void onCreate(Bundle savedInstanceState) {
    super.onCreate(savedInstanceState);
    
    Log.v("Oak", "Hello, World!");
    setContentView(R.layout.activity_main);
    
    Button helloButton = findViewById(R.id.helloButton);
    TextView helloTextView = findViewById(R.id.helloTextView);
    
    //channelHandle = createChannel("127.0.0.1");
    //helloButton.setOnClickListener(
    //    v -> helloTextView.setText(sayHello("World")));
  }

  //public void onClick() {
  //  String response = sayHello("World");
  //}

  //private native int createChannel(String address);
  //private native String sayHello(String name);

  private int channelHandle;
}
