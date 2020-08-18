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
import android.content.Context;
import android.graphics.Color;
import android.os.Bundle;
import android.os.Handler;
import android.os.HandlerThread;
import android.util.Log;
import android.widget.Button;
import android.widget.EditText;
import android.widget.TextView;
import com.google.oak.label.Label;
import io.grpc.ManagedChannel;
import io.grpc.Metadata;
import io.grpc.okhttp.OkHttpChannelBuilder;
import io.grpc.stub.MetadataUtils;
import java.io.InputStream;
import java.lang.Runnable;
import java.lang.ref.WeakReference;
import java.security.KeyStore;
import java.security.cert.Certificate;
import java.security.cert.CertificateFactory;
import java.util.Optional;
import javax.net.ssl.SSLContext;
import javax.net.ssl.SSLSocketFactory;
import javax.net.ssl.TrustManagerFactory;

/** Main activity for the Oak Android "Hello, World" app. */
public class MainActivity extends Activity {
  // Keep in sync with /oak_runtime/src/node/grpc/server/mod.rs.
  private static final String OAK_LABEL_GRPC_METADATA_KEY = "x-oak-label-bin";

  private HandlerThread backgroundHandlerThread;
  private Handler backgroundHandler;

  /** Handles initial setup on creation of the activity. */
  @Override
  public void onCreate(Bundle savedInstanceState) {
    super.onCreate(savedInstanceState);

    Log.v("Oak", "Start application");
    setContentView(R.layout.activity_main);

    HandlerThread backgroundHandlerThread = new HandlerThread("Background");
    backgroundHandlerThread.start();
    backgroundHandler = new Handler(backgroundHandlerThread.getLooper());

    Button helloButton = findViewById(R.id.helloButton);
    helloButton.setOnClickListener(v -> helloButtonOnClick());

    // Set default address.
    // Android emulator forwards `10.0.2.2` to the host machine.
    // https://developer.android.com/studio/run/emulator-networking
    EditText addressInput = findViewById(R.id.addressInput);
    addressInput.setText("10.0.2.2:8080");
  }

  @Override
  public void onDestroy() {
    backgroundHandlerThread.quit();
    super.onDestroy();
  }

  /** Handles click events from the helloButton. */
  public void helloButtonOnClick() {
    EditText addressInput = findViewById(R.id.addressInput);
    String address = addressInput.getText().toString();
    Log.v("Oak", "Say Hello");
    TextView helloTextView = findViewById(R.id.helloTextView);
    backgroundHandler.post(new HelloWorker(getApplicationContext(), address, helloTextView));
  }

  /** Worker to perform blocking tasks on the background HandlerThread. */
  private static class HelloWorker implements Runnable {
    private static final String NAME = "World";

    private Context context;
    private String address;
    private WeakReference<TextView> target;

    private HelloWorker(Context context, String address, TextView target) {
      this.context = context;
      this.address = address;
      this.target = new WeakReference(target);
    }

    @Override
    public void run() {
      Optional<String> reply = sayHello();
      if (reply.isPresent()) {
        Log.v("Oak", "Response is: " + reply.get());
        TextView helloTextView = target.get();
        if (helloTextView != null) {
          helloTextView.post(() -> {
            helloTextView.setTextColor(Color.GREEN);
            helloTextView.setText(reply.get());
          });
        }
      } else {
        TextView helloTextView = target.get();
        helloTextView.post(() -> {
          helloTextView.setTextColor(Color.RED);
          helloTextView.setText("Unexpected Error!");
        });
      }
    }

    /** Calls the sayHello gRPC endpoint and returns the reply. */
    private Optional<String> sayHello() {
      try {
        return Optional.of(HelloWorldGrpc.newBlockingStub(createChannel(address))
                               .sayHello(HelloRequest.newBuilder().setGreeting(NAME).build())
                               .getReply());
      } catch (Exception exception) {
        Log.e("Oak", "Exception", exception);
        return Optional.empty();
      }
    }

    /** Creates a TLS channel. */
    private ManagedChannel createChannel(String address) throws Exception {
      return OkHttpChannelBuilder.forTarget(address)
          .intercept(MetadataUtils.newAttachHeadersInterceptor(getPublicUntrustedLabelMetadata()))
          .useTransportSecurity()
          .sslSocketFactory(getSocketFactory())
          .build();
    }

    /** Gets the metadata associated with the empty label (public/untrusted). */
    private Metadata getPublicUntrustedLabelMetadata() {
      // TODO(#1066): Use a more restrictive Label.
      Metadata result = new Metadata();
      Label label = Label.newBuilder().build();
      Metadata.Key<byte[]> key =
          Metadata.Key.of(OAK_LABEL_GRPC_METADATA_KEY, Metadata.BINARY_BYTE_MARSHALLER);
      result.put(key, label.toByteArray());
      return result;
    }

    /** Gets a socket factory configured with a custom CA certificate to trust. */
    private SSLSocketFactory getSocketFactory() throws Exception {
      InputStream rawCertificate = context.getAssets().open("ca.pem");
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
}
