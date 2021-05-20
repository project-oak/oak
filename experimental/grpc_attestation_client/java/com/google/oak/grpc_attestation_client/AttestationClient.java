package com.google.oak.grpc_attestation_client;

import com.google.oak.grpc_attestation_client.AeadEncryptor;
import com.google.oak.grpc_attestation_client.KeyNegotiator;
import com.google.protobuf.ByteString;
import io.grpc.ManagedChannel;
import io.grpc.ManagedChannelBuilder;
import io.grpc.Status;
import io.grpc.StatusRuntimeException;
import io.grpc.stub.StreamObserver;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.logging.Level;
import java.util.logging.Logger;
import oak.examples.grpc_attestation.AttestedInvokeResponse;
import oak.examples.grpc_attestation.AttestedInvokeRequest;
import oak.examples.grpc_attestation.ClientIdentity;
import oak.examples.grpc_attestation.ServerIdentity;
import oak.examples.grpc_attestation.GrpcAttestationGrpc;
import oak.examples.grpc_attestation.GrpcAttestationGrpc.GrpcAttestationStub;

public class AttestationClient {
    private static final Logger logger = Logger.getLogger(AttestationClient.class.getName());
    // String uri;
    // Bytes expected_tee_measurement;

    public AttestationClient(String uri) throws InterruptedException {
        KeyNegotiator keyNegotiator = null;
        try {
            keyNegotiator = new KeyNegotiator();
        } catch (Exception e) {
            e.printStackTrace();
        }

        // String target = "localhost:8080";
        ManagedChannel channel = ManagedChannelBuilder
            .forTarget(uri)
            // .forTarget(target)
            .usePlaintext()
            .build();

        GrpcAttestationStub stub = GrpcAttestationGrpc.newStub(channel);
        
        // String publicKey = "";
        // ByteString publicKeyBytes = ByteString.copyFromUtf8(publicKey);
        byte[] publicKey = null;
        try {
            publicKey = keyNegotiator.getPublicKey();
        } catch (Exception e) {
            e.printStackTrace();
        }
        ByteString publicKeyBytes = ByteString.copyFrom(publicKey);

        final CountDownLatch finishLatch = new CountDownLatch(1);
        BlockingQueue queue = new ArrayBlockingQueue(1000);

        StreamObserver<AttestedInvokeResponse> responseObserver = new StreamObserver<AttestedInvokeResponse>() {
            @Override
            public void onNext(AttestedInvokeResponse response) {
                // logger.log(Level.INFO, "Client received response: {0}", response);
                // logger.log(Level.INFO, "Public key: {0}", response.getClientIdentity().getPublicKey());
                try {
                    queue.put(response);
                } catch (Exception e) {
                    e.printStackTrace();
                }
            }

            @Override
            public void onError(Throwable t) {
                Status status = Status.fromThrowable(t);
                logger.log(Level.WARNING, "Couldn't receive response: {0}", status);
                finishLatch.countDown();
            }

            @Override
            public void onCompleted() {
                logger.log(Level.INFO, "Server has finished the stream");
                finishLatch.countDown();
            }
        };

        StreamObserver<AttestedInvokeRequest> requestObserver = stub.attestedInvoke(responseObserver);
        try {
            AttestedInvokeRequest request = AttestedInvokeRequest
                .newBuilder()
                .setClientIdentity(
                    ClientIdentity.newBuilder()
                        .setPublicKey(publicKeyBytes)
                        .build()
                )
                .build();

            logger.log(Level.INFO, "Client sends request: {0}", request);
            requestObserver.onNext(request);
            AttestedInvokeResponse response = (AttestedInvokeResponse) queue.take();
            logger.log(Level.INFO, "Client received response: {0}", response);

            byte[] peerPublicKey = response.getServerIdentity().getPublicKey().toByteArray();
            byte[] sessionKey = keyNegotiator.deriveSessionKey(peerPublicKey);
            logger.log(Level.INFO, "Session key: {0}", sessionKey);

            AeadEncryptor encryptor = new AeadEncryptor(sessionKey);
            byte[] encrypted_payload = encryptor.encrypt("Example message".getBytes());

            AttestedInvokeRequest data_request = AttestedInvokeRequest
                .newBuilder()
                .setEncryptedPayload(ByteString.copyFrom(encrypted_payload))
                .build();

            logger.log(Level.INFO, "Client sends data request: {0}", request);
            requestObserver.onNext(data_request);
            AttestedInvokeResponse data_response = (AttestedInvokeResponse) queue.take();
            logger.log(Level.INFO, "Client received data response: {0}", response);


        // } catch (RuntimeException e) {
        } catch (Exception e) {
            logger.log(Level.WARNING, "Couldn't send request");
            requestObserver.onError(e);
            // throw e;
            e.printStackTrace();
        }
        logger.log(Level.INFO, "Client has finished the stream");
        requestObserver.onCompleted();

        // AttestedInvokeResponse response = stub.getAttestedData(request);

        finishLatch.await(1, TimeUnit.MINUTES);

        channel.shutdown();
    }

    // public String Send(String message) {

    // }
}
