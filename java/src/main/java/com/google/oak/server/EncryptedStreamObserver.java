//
// Copyright 2023 The Project Oak Authors
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

package com.google.oak.server;

import com.google.oak.crypto.DecryptionResult;
import com.google.oak.crypto.ServerEncryptor;
import com.google.oak.crypto.hpke.KeyPair;
import com.google.oak.crypto.v1.EncryptedRequest;
import com.google.oak.crypto.v1.EncryptedResponse;
import com.google.oak.session.v1.AttestationBundle;
import com.google.oak.session.v1.AttestationEndorsement;
import com.google.oak.session.v1.AttestationEvidence;
import com.google.oak.session.v1.GetPublicKeyResponse;
import com.google.oak.session.v1.InvokeResponse;
import com.google.oak.session.v1.RequestWrapper;
import com.google.oak.session.v1.ResponseWrapper;
import com.google.oak.transport.QueueingStreamObserver;
import com.google.oak.util.Result;
import com.google.protobuf.ByteString;
import com.google.protobuf.ExtensionRegistry;
import com.google.protobuf.InvalidProtocolBufferException;
import io.grpc.stub.ServerCallStreamObserver;
import io.grpc.stub.StreamObserver;
import java.util.Arrays;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * Generic StreamObserver for processing encrypted requests, by decrypting them, passing them to an
 * inner unencrypted service, and encrypting the responses.
 *
 * @param <I> Type of unencrypted requests
 * @param <O> Type of unencrypted responses
 */
public final class EncryptedStreamObserver<I, O> implements StreamObserver<RequestWrapper> {
  private static final Logger logger = Logger.getLogger(QueueingStreamObserver.class.getName());

  private final byte[] publicKey;
  private final ServerEncryptor encryptor;
  private final ServerCallStreamObserver<ResponseWrapper> outboundObserver;
  private final QueueingStreamObserver<O> innerServerStream = new QueueingStreamObserver<>();
  private final StreamObserver<I> innerClientStream;
  private final ConnectionAdapter<I, O> connectionAdapter;

  /**
   * Creates an {@code EncryptedStreamObserver} for processing encrypted requests from a new
   * client.
   *
   * @param keyPair server's key pair required for creating an encryptor for the client associated
   *     with the {@code serverStreamObserver}.
   * @param connectionAdapter connectionAdapter required for communication with the inner
   *     unencrypted service
   * @param serverStreamObserver serverStreamObserver associated with the output response stream
   */
  public static <I, O> EncryptedStreamObserver<I, O> create(KeyPair keyPair,
      ConnectionAdapter<I, O> connectionAdapter,
      ServerCallStreamObserver<ResponseWrapper> serverStreamObserver) {
    return new EncryptedStreamObserver<>(keyPair, connectionAdapter, serverStreamObserver);
  }

  EncryptedStreamObserver(KeyPair keyPair, ConnectionAdapter<I, O> connectionAdapter,
      ServerCallStreamObserver<ResponseWrapper> serverStreamObserver) {
    this.connectionAdapter = connectionAdapter;
    this.publicKey = Arrays.copyOf(keyPair.publicKey, keyPair.publicKey.length);
    this.encryptor = new ServerEncryptor(keyPair);
    this.innerClientStream = connectionAdapter.connect(this.innerServerStream);
    this.outboundObserver = serverStreamObserver;
  }

  @Override
  public void onNext(RequestWrapper message) {
    if (message.hasGetPublicKeyRequest()) {
      logger.log(Level.INFO, "Received GetPublicKeyRequest request");
      ResponseWrapper response =
          ResponseWrapper.newBuilder().setGetPublicKeyResponse(createPublicKeyResponse()).build();
      logger.log(Level.INFO, "Sending GetPublicKeyResponse response");
      outboundObserver.onNext(response);
    } else if (message.hasInvokeRequest()) {
      logger.log(Level.INFO, "Received InvokeRequest request");

      EncryptedRequest encryptedRequest = message.getInvokeRequest().getEncryptedRequest();
      Result<ResponseWrapper, Exception> result =
          encryptor.decrypt(encryptedRequest).andThen(this::processMessage);
      result.ifError(this::onError);
      result.ifSuccess(msg -> {
        logger.log(Level.INFO, "Sending Processed response");
        outboundObserver.onNext(msg);
      });
    } else {
      onError(new InvalidProtocolBufferException(
          "Got unexpected RequestWrapper that is neither an InvokeRequest nor a"
          + " GetPublicKeyRequest."));
    }
  }

  @Override
  public void onError(Throwable error) {
    logger.log(Level.SEVERE, "Terminating connection with error: " + error);
    outboundObserver.onError(error);
  }

  @Override
  public void onCompleted() {
    outboundObserver.onCompleted();
  }

  private GetPublicKeyResponse createPublicKeyResponse() {
    AttestationEvidence attestationEvidence =
        AttestationEvidence.newBuilder()
            .setEncryptionPublicKey(ByteString.copyFrom(this.publicKey))
            .build();
    // TODO(#3640): Fill out the details of the attestation.
    AttestationEndorsement attestationEndorsement = AttestationEndorsement.getDefaultInstance();
    AttestationBundle attestationBundle = AttestationBundle.newBuilder()
                                              .setAttestationEvidence(attestationEvidence)
                                              .setAttestationEndorsement(attestationEndorsement)
                                              .build();
    return GetPublicKeyResponse.newBuilder().setAttestationBundle(attestationBundle).build();
  }

  private Result<ResponseWrapper, Exception> processMessage(DecryptionResult decrypted) {
    try {
      I request = connectionAdapter.parse(decrypted.plaintext);
      this.innerClientStream.onNext(request);

      // Wait/block until the response is ready.
      O response = this.innerServerStream.take();
      Result<EncryptedResponse, Exception> encryptedResponse =
          encryptor.encrypt(connectionAdapter.serialize(response), decrypted.associatedData);

      return encryptedResponse.map(encrypted -> {
        InvokeResponse invokeResponse =
            InvokeResponse.newBuilder().setEncryptedResponse(encrypted).build();
        return ResponseWrapper.newBuilder().setInvokeResponse(invokeResponse).build();
      });
    } catch (InterruptedException e) {
      Thread.currentThread().interrupt();
      return Result.error(e);
    } catch (InvalidProtocolBufferException e) {
      return Result.error(e);
    }
  }
}
