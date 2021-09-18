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
import com.google.oak.remote_attestation.Message;
import com.google.protobuf.ByteString;
import com.google.protobuf.InvalidProtocolBufferException;
import io.grpc.ManagedChannel;
import io.grpc.ManagedChannelBuilder;
import io.grpc.Status;
import io.grpc.stub.StreamObserver;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URL;
import java.security.GeneralSecurityException;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
import java.util.logging.Level;
import java.util.logging.Logger;
import oak.functions.invocation.Request;
import oak.functions.invocation.Response;
import oak.functions.server.AttestedInvokeRequest;
import oak.functions.server.AttestedInvokeResponse;
import oak.functions.server.RemoteAttestationGrpc;
import oak.functions.server.RemoteAttestationGrpc.RemoteAttestationStub;

/**
 * Client with remote attestation support for sending requests to an Oak Functions application.
 */
public class AttestationClient {
  private static final Logger logger = Logger.getLogger(AttestationClient.class.getName());
  // TODO(#1867): Add remote attestation support.
  private static final String TEST_TEE_MEASUREMENT = "Test TEE measurement";
  private ManagedChannel channel;
  private StreamObserver<AttestedInvokeRequest> requestObserver;
  private BlockingQueue<AttestedInvokeResponse> messageQueue;
  private AeadEncryptor encryptor;

  /** Creates an unattested AttestationClient instance. */
  public AttestationClient() {}

  /**
   * Creates a gRPC channel and creates an attested channel over it.
   *
   * @param url must contain a protocol used for the connection ("https://" or "http://")
   */
  public void attest(String url)
      throws GeneralSecurityException, IOException, InterruptedException {
    // Create gRPC channel.
    URL parsedUrl = new URL(url);
    if (parsedUrl.getProtocol().equals("https")) {
      channel = ManagedChannelBuilder.forAddress(parsedUrl.getHost(), parsedUrl.getPort()).build();
    } else {
      channel = ManagedChannelBuilder.forAddress(parsedUrl.getHost(), parsedUrl.getPort())
                    .usePlaintext()
                    .build();
    }
    attest(channel);
  }

  /** Creates an attested channel over the gRPC {@code ManagedChannel}. */
  public void attest(ManagedChannel channel)
      throws GeneralSecurityException, IOException, InterruptedException {
    if (channel == null) {
      throw new NullPointerException("Channel must not be null.");
    }
    this.channel = channel;
    RemoteAttestationStub stub = RemoteAttestationGrpc.newStub(channel);

    // Create server response handler.
    messageQueue = new ArrayBlockingQueue<>(1);
    StreamObserver<AttestedInvokeResponse> responseObserver =
        new StreamObserver<AttestedInvokeResponse>() {
          @Override
          public void onNext(AttestedInvokeResponse response) {
            try {
              messageQueue.put(response);
            } catch (Exception e) {
              if (e instanceof InterruptedException) {
                Thread.currentThread().interrupt();
              }
              logger.log(Level.WARNING, "Couldn't send server response to the message queue: " + e);
            }
          }

          @Override
          public void onError(Throwable t) {
            Status status = Status.fromThrowable(t);
            logger.log(Level.WARNING, "Couldn't receive response: " + status);
          }

          @Override
          public void onCompleted() {}
        };
    requestObserver = stub.attestedInvoke(responseObserver);

    // Generate client private/public key pair.
    ClientHandshaker handshaker = new ClientHandshaker(TEST_TEE_MEASUREMENT.getBytes(UTF_8));

    // Send client hello message.
    byte[] clientHello = handshaker.createClientHello();
    AttestedInvokeRequest clientHelloRequest =
        AttestedInvokeRequest.newBuilder().setBody(ByteString.copyFrom(clientHello)).build();
    requestObserver.onNext(clientHelloRequest);

    // Receive server attestation identity containing server's ephemeral public key.
    AttestedInvokeResponse serverIdentityResponse = messageQueue.take();
    byte[] serverIdentity = serverIdentityResponse.getBody().toByteArray();

    // Remotely attest the server and create:
    // - Client attestation identity containing client's ephemeral public key
    // - Encryptor used for decrypting/encrypting messages between client and server
    byte[] clientIdentity = handshaker.processServerIdentity(serverIdentity);
    AttestedInvokeRequest clientIdentityRequest =
        AttestedInvokeRequest.newBuilder().setBody(ByteString.copyFrom(clientIdentity)).build();
    requestObserver.onNext(clientIdentityRequest);
    encryptor = handshaker.getEncryptor();
  }

  public Boolean verifyAttestation(byte[] unusedAttestationInfo) {
    // TODO(#1867): Add remote attestation support.
    return true;
  }

  @Override
  protected void finalize() throws Throwable {
    requestObserver.onCompleted();
    channel.shutdownNow();
  }

  /**
   * Encrypts and sends a Request via an attested gRPC channel to the server and receives and
   * decrypts the response.
   *
   * This method can only be used after the {@code attest} method has been called successfully.
   * */
  @SuppressWarnings("ProtoParseWithRegistry")
  public Response send(Request request)
      throws GeneralSecurityException, IOException, InterruptedException,
             InvalidProtocolBufferException {
    if (channel == null || requestObserver == null || encryptor == null) {
      throw new IllegalStateException("Attested channel not available.");
    }

    byte[] encryptedData = encryptor.encrypt(request.getBody().toByteArray());
    AttestedInvokeRequest attestedRequest =
        AttestedInvokeRequest.newBuilder().setBody(ByteString.copyFrom(encryptedData)).build();

    requestObserver.onNext(attestedRequest);
    AttestedInvokeResponse attestedResponse = messageQueue.take();

    byte[] responsePayload = attestedResponse.getBody().toByteArray();
    byte[] decryptedResponse = encryptor.decrypt(responsePayload);
    return Response.parseFrom(decryptedResponse);
  }
}
