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
import com.google.oak.remote_attestation.ClientAttestationEngine;
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
import oak.remote_attestation.ClientIdentity;
import oak.remote_attestation.ClientHello;
import oak.remote_attestation.EncryptedData;
import oak.remote_attestation.ServerIdentity;

/**
 * Client with remote attestation support for sending requests to an Oak Functions loader
 * application.
 */
public class AttestationClient {
  private static final Logger logger = Logger.getLogger(AttestationClient.class.getName());
  // TODO(#1867): Add remote attestation support.
  private static final String TEST_TEE_MEASUREMENT = "Test TEE measurement";
  private final ManagedChannel channel;
  private final StreamObserver<AttestedInvokeRequest> requestObserver;
  private final BlockingQueue<AttestedInvokeResponse> messageQueue;
  private final AeadEncryptor encryptor;

  /**
   * Creates an attested gRPC channel.
   *
   * `url` must contain a protocol used for connection ("https://" or "http://").
   */
  public AttestationClient(String url)
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
    ClientAttestationEngine attestationEngine =
        new ClientAttestationEngine(TEST_TEE_MEASUREMENT.getBytes(UTF_8));

    // Send client hello message.
    ClientHello clientHello = attestationEngine.clientHello();
    AttestedInvokeRequest clientHelloRequest =
        AttestedInvokeRequest.newBuilder().setClientHello(clientHello).build();
    requestObserver.onNext(clientHelloRequest);

    // Receive server attestation identity containing server's ephemeral public key.
    AttestedInvokeResponse serverIdentityResponse = messageQueue.take();
    ServerIdentity serverIdentity = serverIdentityResponse.getServerIdentity();

    // Remotely attest the server and create:
    // - Client attestation identity containing client's ephemeral public key
    // - Encryptor used for decrypting/encrypting messages between client and server
    ClientIdentity clientIdentity = attestationEngine.processServerIdentity(serverIdentity);
    AttestedInvokeRequest clientIdentityRequest =
        AttestedInvokeRequest.newBuilder().setClientIdentity(clientIdentity).build();
    requestObserver.onNext(clientIdentityRequest);
    encryptor = attestationEngine.getEncryptor();
  }

  public Boolean verifyAttestation(byte[] unusedAttestationInfo) {
    // TODO(#1867): Add remote attestation support.
    return true;
  }

  @Override
  protected void finalize() throws Throwable {
    requestObserver.onCompleted();
    channel.shutdown();
  }

  /** Encrypts and sends `message` via an attested gRPC channel to the server. */
  @SuppressWarnings("ProtoParseWithRegistry")
  public Response send(Request request)
      throws GeneralSecurityException, InterruptedException, InvalidProtocolBufferException {
    EncryptedData encryptedData = encryptor.encrypt(request.getBody().toByteArray());
    oak.functions.server.Request serverRequest =
        oak.functions.server.Request.newBuilder().setEncryptedPayload(encryptedData).build();
    AttestedInvokeRequest attestedRequest =
        AttestedInvokeRequest.newBuilder().setRequest(serverRequest).build();

    requestObserver.onNext(attestedRequest);
    AttestedInvokeResponse attestedResponse = messageQueue.take();

    EncryptedData responsePayload = attestedResponse.getEncryptedPayload();
    byte[] decryptedResponse = encryptor.decrypt(responsePayload);
    return Response.parseFrom(decryptedResponse);
  }
}
