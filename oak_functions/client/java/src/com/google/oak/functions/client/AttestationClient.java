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

package com.google.oak.functions.client;

import static java.nio.charset.StandardCharsets.UTF_8;
import static java.util.concurrent.TimeUnit.SECONDS;

import com.google.oak.remote_attestation.AeadEncryptor;
import com.google.oak.remote_attestation.ClientHandshaker;
import com.google.oak.remote_attestation.Message;
import com.google.protobuf.ByteString;
import io.grpc.CallOptions;
import io.grpc.Channel;
import io.grpc.ClientCall;
import io.grpc.ClientInterceptor;
import io.grpc.ForwardingClientCall;
import io.grpc.ManagedChannel;
import io.grpc.ManagedChannelBuilder;
import io.grpc.Metadata;
import io.grpc.MethodDescriptor;
import io.grpc.Status;
import io.grpc.stub.StreamObserver;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.security.GeneralSecurityException;
import java.security.SecureRandom;
import java.time.Duration;
import java.util.ArrayList;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
import java.util.function.Predicate;
import java.util.logging.Level;
import java.util.logging.Logger;
import oak.functions.abi.ConfigurationReport;
import oak.functions.invocation.Request;
import oak.functions.invocation.Response;
import oak.session.unary.v1.UnaryRequest;
import oak.session.unary.v1.UnaryResponse;
import oak.session.unary.v1.UnarySessionGrpc;

/**
 * Client with remote attestation support for sending requests to an Oak Functions application.
 */
public class AttestationClient {
  public static final Duration DEFAULT_CONNECTION_TIMEOUT = Duration.ofSeconds(5);
  private static final Logger logger = Logger.getLogger(AttestationClient.class.getName());
  // TODO(#1867): Add remote attestation support.
  private static final String TEST_TEE_MEASUREMENT = "Test TEE measurement";
  private static final Integer SESSION_ID_BYTE_LENGTH = 8;
  private final Duration connectionTimeout;
  // HTTP/gRPC header for Google API keys.
  // https://cloud.google.com/apis/docs/system-parameters
  // https://cloud.google.com/docs/authentication/api-keys
  private static final String API_KEY_HEADER = "x-goog-api-key";
  private ByteString sessionId;
  private ManagedChannel channel;
  private UnarySessionGrpc.UnarySessionBlockingStub stub;
  private AeadEncryptor encryptor;

  /** Remote Attestation identity verification failure. */
  public static class VerificationException extends Exception {
    public VerificationException(String msg) {
      super(msg);
    }
  }

  /** Creates an unattested AttestationClient instance with the default connection timeout. */
  public AttestationClient() {
    this(DEFAULT_CONNECTION_TIMEOUT);
  }

  /**
   * Creates an unattested AttestationClient instance.
   *
   * @param connectionTimeout contains an inactivity threshold for gRPC connections.
   */
  public AttestationClient(Duration connectionTimeout) {
    this.connectionTimeout = connectionTimeout;
  }

  /**
   * Adds a gRPC channel interceptor that inserts an API key header into every request.
   *
   * @param builder an instance of a {@code ManagedChannelBuilder} for a gRPC channel.
   * @param apiKey value of the API key used in gRPC requests. If the value is `null` or empty, then
   * the API key header is not included in requests.
   * https://cloud.google.com/docs/authentication/api-keys
   *
   * @return an updated instance of a {@code ManagedChannelBuilder}.
   */
  public static ManagedChannelBuilder addApiKey(ManagedChannelBuilder builder, String apiKey) {
    ArrayList<ClientInterceptor> interceptors = new ArrayList<>();
    if (apiKey != null && !apiKey.trim().isEmpty()) {
      interceptors.add(new Interceptor(apiKey));
    }
    return builder.intercept(interceptors);
  }

  // TODO(#2356): Change the return type to `AttestationResult` instead of throwing exceptions.
  /**
   * Creates an attested channel over the gRPC channel.
   *
   * @param channel an instance of a gRPC {@code ManagedChannel}.
   * @param verifier checks that the ServerIdentity contains the expected attestation info as
   * described in {@code ServerIdentityVerifier::verifyAttestationInfo}.
   */
  public void attest(ManagedChannel channel, Predicate<ConfigurationReport> verifier)
      throws GeneralSecurityException, IOException, InterruptedException, VerificationException {
    if (channel == null) {
      throw new NullPointerException("Channel must not be null.");
    }
    this.channel = channel;
    stub = UnarySessionGrpc.newBlockingStub(channel);

    SecureRandom random = new SecureRandom();
    byte[] rawSessionId = new byte[SESSION_ID_BYTE_LENGTH];
    random.nextBytes(rawSessionId);
    sessionId = ByteString.copyFrom(rawSessionId);

    // Generate client private/public key pair.
    ClientHandshaker handshaker = new ClientHandshaker(TEST_TEE_MEASUREMENT.getBytes(UTF_8));

    // Send client hello message.
    byte[] clientHello = handshaker.createClientHello();
    UnaryRequest clientHelloRequest = UnaryRequest.newBuilder()
                                          .setBody(ByteString.copyFrom(clientHello))
                                          .setSessionId(sessionId)
                                          .build();

    // Receive server attestation identity containing server's ephemeral public key.
    UnaryResponse serverIdentityResponse = stub.message(clientHelloRequest);
    byte[] serverIdentity = serverIdentityResponse.getBody().toByteArray();

    // Verify ServerIdentity, including its configuration and proof of its inclusion in Rekor.
    if (!verifyServerIdentity(serverIdentity, verifier)) {
      throw new VerificationException("Verification of ServerIdentity failed.");
    }

    // Remotely attest the server and create:
    // - Client attestation identity containing client's ephemeral public key
    // - Encryptor used for decrypting/encrypting messages between client and server
    byte[] clientIdentity = handshaker.processServerIdentity(serverIdentity);
    UnaryRequest clientIdentityRequest = UnaryRequest.newBuilder()
                                             .setBody(ByteString.copyFrom(clientIdentity))
                                             .setSessionId(sessionId)
                                             .build();
    stub.message(clientIdentityRequest);
    encryptor = handshaker.getEncryptor();
  }

  // TODO(#2356): Change the return type to `VerificationResult` instead of throwing an exception.
  /**
   * Verifies server identity including its configuration.
   *
   * This function performs the following steps:
   *
   * - Deserializes `serializedServerIdentity` into an instance of {@code
   * Message.ServerIdentity}. Throws IOException if the deserialization fails.
   * - Checks that the resulting ServerIdentity contains an instance of {@code ConfigurationReport},
   * and checks that the {@code configurationVerifier} predicate is valid for it. Returns false if
   * the check fails.
   * - Checks that the ServerIdentity contains the expected attestation info as described in {@code
   * ServerIdentityVerifier::verifyAttestationInfo}.
   *
   * @param serializedServerIdentity The server's identity.
   * @param configurationVerifier Predicate that verifies the configuration info part of the server
   *     identity.
   * @throws IOException If {@code serializedServerIdentity} cannot be deserialized into an instance
   *     of {@code Message.ServerIdentity}.
   */
  boolean verifyServerIdentity(byte[] serializedServerIdentity,
      Predicate<ConfigurationReport> configurationVerifier) throws IOException {
    Message.ServerIdentity serverIdentity =
        Message.ServerIdentity.deserialize(serializedServerIdentity);

    ServerConfigurationVerifier verifier =
        new ServerConfigurationVerifier(serverIdentity, configurationVerifier);

    if (!verifier.verify()) {
      logger.log(Level.WARNING, "Verification of the ServerIdentity failed.");
      return false;
    }

    return true;
  }

  /**
   * Encrypts and sends a Request via an attested gRPC channel to the server and receives and
   * decrypts the response.
   *
   * This method can only be used after the {@code attest} method has been called successfully.
   *
   * @param request contains a request to be sent via the attested gRPC channel.
   */
  @SuppressWarnings("ProtoParseWithRegistry")
  public Response send(Request request)
      throws GeneralSecurityException, IOException, InterruptedException {
    if (channel == null || encryptor == null || sessionId == null || stub == null) {
      throw new IllegalStateException("Session is not available");
    }

    byte[] encryptedData = encryptor.encrypt(request.getBody().toByteArray());
    UnaryRequest unaryRequest = UnaryRequest.newBuilder()
                                    .setBody(ByteString.copyFrom(encryptedData))
                                    .setSessionId(sessionId)
                                    .build();

    UnaryResponse streamingResponse = stub.message(unaryRequest);

    byte[] responsePayload = streamingResponse.getBody().toByteArray();
    byte[] decryptedResponse = encryptor.decrypt(responsePayload);
    return Response.parseFrom(decryptedResponse);
  }

  /**
   * Intercepts gRPC requests and adds Metadata with an API key.
   * https://cloud.google.com/endpoints/docs/grpc/restricting-api-access-with-api-keys#java
   */
  private static final class Interceptor implements ClientInterceptor {
    private final String apiKey;

    private static final Metadata.Key<String> API_KEY_METADATA_HEADER =
        Metadata.Key.of(API_KEY_HEADER, Metadata.ASCII_STRING_MARSHALLER);

    public Interceptor(String apiKey) {
      this.apiKey = apiKey;
    }

    @Override
    public <ReqT, RespT> ClientCall<ReqT, RespT> interceptCall(
        MethodDescriptor<ReqT, RespT> method, CallOptions callOptions, Channel next) {
      ClientCall<ReqT, RespT> call = next.newCall(method, callOptions);

      call = new ForwardingClientCall.SimpleForwardingClientCall<ReqT, RespT>(call) {
        @Override
        public void start(Listener<RespT> responseListener, Metadata headers) {
          if (apiKey != null && !apiKey.isEmpty()) {
            headers.put(API_KEY_METADATA_HEADER, apiKey);
          }
          super.start(responseListener, headers);
        }
      };
      return call;
    }
  }
}
