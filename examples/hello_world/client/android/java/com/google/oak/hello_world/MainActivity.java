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
import android.widget.EditText;
import android.widget.TextView;
import io.grpc.ManagedChannel;
import io.grpc.okhttp.OkHttpChannelBuilder;
import java.io.InputStream;
import java.security.KeyStore;
import java.security.cert.Certificate;
import java.security.cert.CertificateFactory;
import java.util.Optional;
import javax.net.ssl.SSLContext;
import javax.net.ssl.SSLSocketFactory;
import javax.net.ssl.TrustManagerFactory;

/** Main activity for the Oak Android "Hello, World" app. */
public class MainActivity extends Activity {
  /** Handles initial setup on creation of the activity. */
  @Override
  public void onCreate(Bundle savedInstanceState) {
    super.onCreate(savedInstanceState);

    Log.v("Oak", "Start application");
    setContentView(R.layout.activity_main);

    Button helloButton = findViewById(R.id.helloButton);
    helloButton.setOnClickListener(v -> helloButtonOnClick());

    // Set default address.
    // Android emulator forwards `10.0.2.2` to the host machine.
    // https://developer.android.com/studio/run/emulator-networking
    EditText addressInput = findViewById(R.id.addressInput);
    addressInput.setText("10.0.2.2:8080");
  }

  /** Handles click events from the helloButton. */
  public void helloButtonOnClick() {
    EditText addressInput = findViewById(R.id.addressInput);
    String address = addressInput.getText().toString();
    Log.v("Oak", "Say Hello");
    TextView helloTextView = findViewById(R.id.helloTextView);

    // TODO(#988): Move blocking call out of UI thread.
    Optional<String> reply = sayHello(address, "World");
    if (reply.isPresent()) {
      Log.v("Oak", "Response is: " + reply.get());
      helloTextView.setText(reply.get());
    } else {
      helloTextView.setText("Unexpected Error!");
    }
  }

  /** Calls the sayHello gRPC endpoint and returns the reply. */
  private Optional<String> sayHello(String address, String name) {
    try {
      return Optional.of(HelloWorldGrpc.newBlockingStub(createChannel(address))
                             .sayHello(HelloRequest.newBuilder().setGreeting(name).build())
                             .getReply());
    } catch (Exception exception) {
      Log.e("Oak", "Exception", exception);
      return Optional.empty();
    }
  }

  /** Creates a TLS channel. */
  private ManagedChannel createChannel(String address) throws Exception {
    return OkHttpChannelBuilder.forTarget(address)
        .useTransportSecurity()
        .sslSocketFactory(getSocketFactory())
        .build();
  }

  /** Gets a socket factory configured with a custom CA certificate to trust. */
  private SSLSocketFactory getSocketFactory() throws Exception {
    InputStream rawCertificate = getAssets().open("ca.pem");
    Certificate certificate =
        CertificateFactory.getInstance("X.509").generateCertificate(rawCertificate);
    KeyStore keyStore = KeyStore.getInstance(KeyStore.getDefaultType());
    // No stored keystore file or password.
    keyStore.load(null, null);
    keyStore.setCertificateEntry("local_ca", certificate);
    TrustManagerFactory trustManagerFactory =
        TrustManagerFactory.getInstance(TrustManagerFactory.getDefaultAlgorithm());
    trustManagerFactory.init(keyStore);
    // Using TLSv1.2, as TLSv1.3 requires minSdkVersion of 29.
    // Reference: https://developer.android.com/reference/javax/net/ssl/SSLContext
    SSLContext tlsContext = SSLContext.getInstance("TLSv1.2");
    // Use highest priority KeyManager and default SecureRandom implementation.
    tlsContext.init(null, trustManagerFactory.getTrustManagers(), null);
    return tlsContext.getSocketFactory();
  }
}
