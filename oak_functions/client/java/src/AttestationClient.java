package com.google.oak.functions.client;

import com.google.oak.functions.client.AeadEncryptor;
import com.google.oak.functions.client.KeyNegotiator;
import com.google.protobuf.ByteString;
import io.grpc.ManagedChannel;
import io.grpc.ManagedChannelBuilder;
import io.grpc.Status;
import io.grpc.stub.StreamObserver;
import java.lang.RuntimeException;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
import java.util.logging.Level;
import java.util.logging.Logger;
import oak.remote_attestation.AttestedInvokeResponse;
import oak.remote_attestation.AttestedInvokeRequest;
import oak.remote_attestation.ClientIdentity;
import oak.remote_attestation.ServerIdentity;
import oak.remote_attestation.RemoteAttestationGrpc;
import oak.remote_attestation.RemoteAttestationGrpc.RemoteAttestationStub;

// TODO(#2121): Implement a protocol independent state machine.
public class AttestationClient {
    private static Logger logger = Logger.getLogger(AttestationClient.class.getName());
    private ManagedChannel channel;
    private StreamObserver<AttestedInvokeRequest> requestObserver;
    private BlockingQueue messageQueue;
    private AeadEncryptor encryptor;

    public AttestationClient(String uri) throws Exception {
        // Create gRPC channel.
        channel = ManagedChannelBuilder
            .forTarget(uri)
            .usePlaintext()
            .build();
        RemoteAttestationStub stub = RemoteAttestationGrpc.newStub(channel);

        // Create server response handler.
        messageQueue = new ArrayBlockingQueue(1);
        StreamObserver<AttestedInvokeResponse> responseObserver = new StreamObserver<AttestedInvokeResponse>() {
            @Override
            public void onNext(AttestedInvokeResponse response) {
                try {
                    messageQueue.put(response);
                } catch (Exception e) {
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
        KeyNegotiator keyNegotiator = new KeyNegotiator();
        byte[] publicKey = keyNegotiator.getPublicKey();
        ByteString publicKeyBytes = ByteString.copyFrom(publicKey);

        // Send client public key to the server.
        AttestedInvokeRequest request = AttestedInvokeRequest
            .newBuilder()
            .setClientIdentity(
                ClientIdentity.newBuilder()
                    .setPublicKey(publicKeyBytes)
                    .build()
            )
            .build();
        requestObserver.onNext(request);
        AttestedInvokeResponse response = (AttestedInvokeResponse) messageQueue.take();

        // Verify remote attestation.
        byte[] attestationInfo = response.getServerIdentity().getAttestationInfo().toByteArray();
        if (!verifyAttestation(attestationInfo)) {
            throw new RuntimeException("Couldn't verify attestation info");
        }

        // Generate session key and initialize AEAD encryptor based on it.
        byte[] peerPublicKey = response.getServerIdentity().getPublicKey().toByteArray();
        encryptor = keyNegotiator.createAeadEncryptor(peerPublicKey);
    }

    private Boolean verifyAttestation(byte[] attestationInfo) {
        // TODO(#1867): Add remote attestation support.
        return true;
    }

    protected void finalize() throws Throwable {
        requestObserver.onCompleted();
        channel.shutdown();
    }

    /**
     * Encrypts and sends `message` via an attested gRPC channel to the server.
     */
    public byte[] Send(byte[] message) throws Exception {
        byte[] encryptedMessage = encryptor.encrypt(message);
        AttestedInvokeRequest request = AttestedInvokeRequest
            .newBuilder()
            .setEncryptedPayload(ByteString.copyFrom(encryptedMessage))
            .build();

        requestObserver.onNext(request);
        AttestedInvokeResponse response = (AttestedInvokeResponse) messageQueue.take();

        byte[] responsePayload = response.getEncryptedPayload().toByteArray();
        return encryptor.decrypt(responsePayload);
    }
}
