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

import com.google.oak.remote_attestation.AeadEncryptor;
import com.google.oak.remote_attestation.ClientHandshaker;
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
import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.security.GeneralSecurityException;
import java.security.SecureRandom;
import java.time.Duration;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Map;
import java.util.function.Predicate;
import java.util.logging.Logger;
import java.util.stream.Collectors;
import oak.functions.abi.ConfigurationReport;
import oak.session.v1.AttestationRequest;
import oak.session.v1.AttestationResponse;
import oak.session.v1.UnarySessionGrpc;

/** Client with remote attestation support for sending requests to an Oak Functions application. */
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

  /** A response received from the trusted runtime */
  public static class Response {
    StatusCode statusCode;
    long length;
    byte[] body;

    public StatusCode getStatus() {
      return statusCode;
    }

    public long getLength() {
      return length;
    }

    public byte[] getBody() {
      return body;
    }

    public static long decodeLength(byte[] lengthBytes) {
      ByteBuffer buffer = ByteBuffer.wrap(lengthBytes);
      buffer.order(ByteOrder.LITTLE_ENDIAN);
      return buffer.getLong();
    }

    public static Response parseFrom(byte[] bytes) throws IllegalArgumentException {
      byte[] statusBytes = Arrays.copyOfRange(bytes, 0, 4);
      byte[] lengthBytes = Arrays.copyOfRange(bytes, 4, 12);
      long length = decodeLength(lengthBytes);
      byte[] body = Arrays.copyOfRange(bytes, 12, bytes.length);
      Response response = new Response();
      response.statusCode = StatusCode.fromBytes(statusBytes);
      response.length = length;
      response.body = body;
      return response;
    }
  }

  /** Status code supplied by the trusted runtime with every response */
  public static enum StatusCode {
    UNSPECIFIED(0),
    // Indicates success of the operation. Similar to HTTP 200 status code.
    SUCCESS(1),
    // Indicates a problem with the request. Similar to HTTP 400 status code.
    BAD_REQUEST(2),
    // Indicates violation of the response size limit specified in the security policy.
    POLICY_SIZE_VIOLATION(3),
    // Indicates violation of the response processing-time limit specified in the security policy.
    POLICY_TIME_VIOLATION(4),
    // Indicates other internal errors at the server. Similar to HTTP 500 status code.
    INTERNAL_SERVER_ERROR(5);

    private final int value;

    private StatusCode(int value) {
      this.value = value;
    }

    private static final Map<Integer, StatusCode> map;

    static {
      map = Arrays.stream(values()).collect(Collectors.toMap(e -> e.value, e -> e));
    }

    public static StatusCode fromInt(int value) throws IllegalArgumentException {
      StatusCode statusCode = map.get(value);
      if (statusCode == null) {
        throw new IllegalArgumentException("Received an invalid status code");
      }
      return statusCode;
    }

    public static StatusCode fromBytes(byte[] statusBytes) throws IllegalArgumentException {
      ByteBuffer buffer = ByteBuffer.wrap(statusBytes);
      buffer.order(ByteOrder.LITTLE_ENDIAN);
      return fromInt(buffer.getInt());
    }
  }

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
   *     the API key header is not included in requests.
   *     https://cloud.google.com/docs/authentication/api-keys
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
   */
  public void attest(ManagedChannel channel)
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
    AttestationRequest clientHelloRequest = AttestationRequest.newBuilder()
                                          .setBody(ByteString.copyFrom(clientHello))
                                          .setSessionId(sessionId)
                                          .build();

    // Receive server attestation identity containing server's ephemeral public key.
    AttestationResponse serverIdentityResponse = stub.message(clientHelloRequest);
    byte[] serverIdentity = serverIdentityResponse.getBody().toByteArray();

    // Remotely attest the server and create:
    // - Client attestation identity containing client's ephemeral public key
    // - Encryptor used for decrypting/encrypting messages between client and server
    byte[] clientIdentity = handshaker.processServerIdentity(serverIdentity);
    AttestationRequest clientIdentityRequest = AttestationRequest.newBuilder()
                                             .setBody(ByteString.copyFrom(clientIdentity))
                                             .setSessionId(sessionId)
                                             .build();
    stub.message(clientIdentityRequest);
    encryptor = handshaker.getEncryptor();
  }

  /**
   * Encrypts and sends a Request via an attested gRPC channel to the server and receives and
   * decrypts the response.
   *
   * <p>This method can only be used after the {@code attest} method has been called successfully.
   *
   * @param request contains a request to be sent via the attested gRPC channel.
   */
  @SuppressWarnings("ProtoParseWithRegistry")
  public Response send(byte[] body)
      throws GeneralSecurityException, IOException, InterruptedException, IllegalArgumentException {
    if (channel == null || encryptor == null || sessionId == null || stub == null) {
      throw new IllegalStateException("Session is not available");
    }

    byte[] encryptedData = encryptor.encrypt(body);
    AttestationRequest unaryRequest = AttestationRequest.newBuilder()
                                    .setBody(ByteString.copyFrom(encryptedData))
                                    .setSessionId(sessionId)
                                    .build();

    AttestationResponse streamingResponse = stub.message(unaryRequest);

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
