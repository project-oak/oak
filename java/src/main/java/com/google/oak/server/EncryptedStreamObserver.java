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

import com.google.oak.crypto.Encryptor;
import com.google.oak.crypto.ServerEncryptor;
import com.google.oak.crypto.hpke.KeyPair;
import com.google.oak.session.v1.EndorsedEvidence;
import com.google.oak.session.v1.AttestationEndorsement;
import com.google.oak.session.v1.AttestationEvidence;
import com.google.oak.session.v1.GetEndorsedEvidenceResponse;
import com.google.oak.session.v1.InvokeResponse;
import com.google.oak.session.v1.RequestWrapper;
import com.google.oak.session.v1.ResponseWrapper;
import com.google.oak.transport.QueueingStreamObserver;
import com.google.oak.util.Result;
import com.google.protobuf.ByteString;
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
    if (message.hasGetEndorsedEvidenceRequest()) {
      logger.log(Level.INFO, "Received GetEndorsedEvidenceRequest request");
      ResponseWrapper response =
          ResponseWrapper.newBuilder().setGetEndorsedEvidenceResponse(createPublicKeyResponse()).build();
      logger.log(Level.INFO, "Sending GetEndorsedEvidenceResponse response");
      outboundObserver.onNext(response);
    } else if (message.hasInvokeRequest()) {
      logger.log(Level.INFO, "Received InvokeRequest request");
      Result<ResponseWrapper, Exception> result =
          encryptor.decrypt(message.getInvokeRequest().getEncryptedBody().toByteArray())
              .andThen(this::processMessage);
      result.ifError(this::onError);
      result.ifSuccess(msg -> {
        logger.log(Level.INFO, "Sending Processed response");
        outboundObserver.onNext(msg);
      });
    } else {
      onError(new InvalidProtocolBufferException(
          "Got unexpected RequestWrapper that is neither an InvokeRequest nor a"
          + " GetEndorsedEvidenceRequest."));
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

  private GetEndorsedEvidenceResponse createPublicKeyResponse() {
    AttestationEvidence attestationEvidence =
        AttestationEvidence.newBuilder()
            .setEncryptionPublicKey(ByteString.copyFrom(this.publicKey))
            .build();
    // TODO(#3640): Fill out the details of the attestation.
    AttestationEndorsement attestationEndorsement = AttestationEndorsement.getDefaultInstance();
    EndorsedEvidence EndorsedEvidence = EndorsedEvidence.newBuilder()
                                              .setAttestationEvidence(attestationEvidence)
                                              .setAttestationEndorsement(attestationEndorsement)
                                              .build();
    return GetEndorsedEvidenceResponse.newBuilder().setEndorsedEvidence(EndorsedEvidence).build();
  }

  private Result<ResponseWrapper, Exception> processMessage(Encryptor.DecryptionResult decrypted) {
    try {
      I request = connectionAdapter.parse(decrypted.plaintext);
      this.innerClientStream.onNext(request);

      // Wait/block until the response is ready.
      O response = this.innerServerStream.take();
      Result<byte[], Exception> encryptedResult =
          encryptor.encrypt(connectionAdapter.serialize(response), decrypted.associatedData);

      return encryptedResult.map(encrypted -> {
        InvokeResponse invokeResponse =
            InvokeResponse.newBuilder().setEncryptedBody(ByteString.copyFrom(encrypted)).build();
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
